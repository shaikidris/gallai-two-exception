/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentHubOddMin

@[expose] public section

/-! # Native cut-side closure for the odd/odd hub-cut auxiliary

The recursive pendant auxiliary in Xie's odd/odd hub-cut branch is formed on
`G.induce S`, not on the ambient spanning copy of that graph.  The elementary
closure lemma below is the bridge needed to compare local degrees on the
native cut side with degrees in `G` away from the shared hub.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- In a one-vertex induced cut decomposition, every neighbour of a vertex on
the `S` side other than the shared hub remains on that side.  This uses the
literal edge-cover equality, rather than connectivity of an ambient spanning
graph. -/
theorem neighborSet_subset_left_of_one_vertex_union
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (v : V) (hvS : v ∈ S) (hvh : v ≠ h) :
    G.neighborSet v ⊆ S := by
  intro w hw
  have hvw : G.Adj v w := (G.mem_neighborSet v w).mp hw
  rw [← hgraph] at hvw
  rcases hvw with hS | hT
  · exact ((spanning_induce_adj_iff G S v w).mp hS).2.2
  · have hvT : v ∈ T := ((spanning_induce_adj_iff G T v w).mp hT).2.1
    have hvinter : v ∈ S ∩ T := ⟨hvS, hvT⟩
    have : v = h := by
      simpa only [hinter, Set.mem_singleton_iff] using hvinter
    exact False.elim (hvh this)

/-- The symmetric closure fact for the opposite native cut side. -/
theorem neighborSet_subset_right_of_one_vertex_union
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (v : V) (hvT : v ∈ T) (hvh : v ≠ h) :
    G.neighborSet v ⊆ T := by
  intro w hw
  have hvw : G.Adj v w := (G.mem_neighborSet v w).mp hw
  rw [← hgraph] at hvw
  rcases hvw with hS | hT
  · have hvS : v ∈ S := ((spanning_induce_adj_iff G S v w).mp hS).2.1
    have hvinter : v ∈ S ∩ T := ⟨hvS, hvT⟩
    have : v = h := by
      simpa only [hinter, Set.mem_singleton_iff] using hvinter
    exact False.elim (hvh this)
  · exact ((spanning_induce_adj_iff G T v w).mp hT).2.2

/-- On the cut side containing the second hub, an odd local shared hub is
automatically harmless for the one-exception cap.  Every other local even
vertex, and each of its local even neighbours, has its full ambient
neighbourhood on this side; therefore the ambient subcubic E-degree cap
restricts to the native induced graph. -/
theorem induce_cap_left_of_native_closure_except_odd_hub
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S)
    (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∀ v : S, Even ((G.induce S).degree v) → v ≠ ⟨y, hyS⟩ →
      eDegree (G.induce S) v ≤ 3 := by
  classical
  intro v hv hvy
  have hvh : v.val ≠ h := by
    intro e
    have ev : v = ⟨h, hhS⟩ := Subtype.ext e
    subst v
    exact (Nat.not_even_iff_odd.mpr hhOdd) hv
  have hclosed : G.neighborSet v.val ⊆ S :=
    neighborSet_subset_left_of_one_vertex_union S T h hinter hgraph v.val v.property hvh
  have hvG : Even (G.degree v.val) := by
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset hclosed] at hv
  let f : S ↪ V := Function.Embedding.subtype S
  have hsubset : (evenNeighbors (G.induce S) v).map f ⊆
      evenNeighbors G v.val := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors (G := G.induce S) v w).mp hw
    have hwAdj : G.Adj v.val w.val := hvw
    have hwh : w.val ≠ h := by
      intro e
      have ew : w = ⟨h, hhS⟩ := Subtype.ext e
      subst w
      exact (Nat.not_even_iff_odd.mpr hhOdd) hwEven
    have hwclosed : G.neighborSet w.val ⊆ S :=
      neighborSet_subset_left_of_one_vertex_union S T h hinter hgraph w.val w.property hwh
    have hwG : Even (G.degree w.val) := by
      rwa [SimpleGraph.degree_induce_of_neighborSet_subset hwclosed] at hwEven
    exact (mem_evenNeighbors (G := G) v.val w.val).mpr ⟨hwAdj, hwG⟩
  calc
    eDegree (G.induce S) v = (evenNeighbors (G.induce S) v).card := rfl
    _ ≤ (evenNeighbors G v.val).card := by
      rw [← Finset.card_map f]
      exact Finset.card_le_card hsubset
    _ = eDegree G v.val := rfl
    _ ≤ 3 := hcap v.val hvG hvh (fun e => hvy (Subtype.ext e))

/-- A local cap transport statement with the shared hub explicitly exempted
from closure.  The hub can become even only after the pendant attachment, so
its global evenness supplies the one additional admissible even neighbour. -/
theorem pendantExtension_cap_induce_of_native_closure
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S)
    (hh : Even (G.degree h))
    (hclosed : ∀ v ∈ S, v ≠ h → G.neighborSet v ⊆ S)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∀ v, Even ((pendantExtension (G.induce S) ⟨h, hhS⟩).degree v) →
      v ≠ (.inl ⟨h, hhS⟩ : S ⊕ Unit) → v ≠ .inl ⟨y, hyS⟩ →
      eDegree (pendantExtension (G.induce S) ⟨h, hhS⟩) v ≤ 3 := by
  classical
  intro v hv hvh hvy
  let f : S ⊕ Unit ↪ V ⊕ Unit :=
    (Function.Embedding.subtype S).sumMap (Function.Embedding.refl Unit)
  cases v with
  | inr u =>
    cases u
    exact False.elim ((Nat.not_even_iff_odd.mpr
      (pendantExtension_odd_new (G.induce S) ⟨h, hhS⟩)) hv)
  | inl v =>
    have hvh' : v.val ≠ h := fun e =>
      hvh (congrArg Sum.inl (Subtype.ext e))
    have hvy' : v.val ≠ y := fun e =>
      hvy (congrArg Sum.inl (Subtype.ext e))
    have hvLocal : Even ((G.induce S).degree v) :=
      (pendantExtension_even_old_ne (G.induce S) ⟨h, hhS⟩ v
        (fun e => hvh' (congrArg Subtype.val e))).mp hv
    have hvG : Even (G.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_neighborSet_subset
        (hclosed v.val v.property hvh')] at hvLocal
    have hsubset : (evenNeighbors (pendantExtension (G.induce S) ⟨h, hhS⟩) (.inl v)).map f ⊆
        (evenNeighbors G v.val).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hz
      cases q with
      | inr u =>
        cases u
        exact False.elim ((Nat.not_even_iff_odd.mpr
          (pendantExtension_odd_new (G.induce S) ⟨h, hhS⟩))
          ((mem_evenNeighbors (G := pendantExtension (G.induce S) ⟨h, hhS⟩) (.inl v) (.inr ())).mp hq).2)
      | inl w =>
        obtain ⟨hvw, hwEven⟩ :=
          (mem_evenNeighbors (G := pendantExtension (G.induce S) ⟨h, hhS⟩) (.inl v) (.inl w)).mp hq
        have hwAdj : G.Adj v.val w.val :=
          (pendantExtension_adj_old (G.induce S) ⟨h, hhS⟩ v w).mp hvw
        by_cases hwh : w.val = h
        · rw [hwh] at hwAdj
          exact Finset.mem_map.mpr ⟨h,
            (mem_evenNeighbors (G := G) v.val h).mpr ⟨hwAdj, hh⟩, by
              change Sum.inl h = Sum.inl w.val
              exact congrArg Sum.inl hwh.symm⟩
        · have hwLocal : Even ((G.induce S).degree w) :=
            (pendantExtension_even_old_ne (G.induce S) ⟨h, hhS⟩ w
              (fun e => hwh (congrArg Subtype.val e))).mp hwEven
          have hwG : Even (G.degree w.val) := by
            rwa [SimpleGraph.degree_induce_of_neighborSet_subset
              (hclosed w.val w.property hwh)] at hwLocal
          exact Finset.mem_map.mpr ⟨w.val,
            (mem_evenNeighbors (G := G) v.val w.val).mpr ⟨hwAdj, hwG⟩, by rfl⟩
    calc
      eDegree (pendantExtension (G.induce S) ⟨h, hhS⟩) (.inl v) =
          (evenNeighbors (pendantExtension (G.induce S) ⟨h, hhS⟩) (.inl v)).card := rfl
      _ ≤ (evenNeighbors G v.val).card := by
        rw [← Finset.card_map f, ← Finset.card_map (Function.Embedding.inl : V ↪ V ⊕ Unit)]
        exact Finset.card_le_card hsubset
      _ = eDegree G v.val := rfl
      _ ≤ 3 := hcap v.val hvG hvh' hvy'

/-- The connected native cut piece containing the other hub becomes an
adjacent two-exception instance after the fresh pendant attachment.  Every
condition is stated on the subtype where the recursive call actually runs. -/
theorem adjacentInstance_pendant_induce_of_native_closure
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S)
    (hconn : (G.induce S).Connected) (hhy : G.Adj h y) (hneq : h ≠ y)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hyEven : Even ((G.induce S).degree ⟨y, hyS⟩))
    (hh : Even (G.degree h))
    (hclosed : ∀ v ∈ S, v ≠ h → G.neighborSet v ⊆ S)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    AdjacentInstance (pendantExtension (G.induce S) ⟨h, hhS⟩)
      (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩) := by
  letI : DecidableRel (pendantExtension (G.induce S) ⟨h, hhS⟩).Adj :=
    Gallai.instDecidableRelAdjPendantExtension (G.induce S) ⟨h, hhS⟩
  refine ⟨pendantExtension_connected (G.induce S) ⟨h, hhS⟩ hconn, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact hneq (congrArg Subtype.val (Sum.inl.inj e))
  · exact (pendantExtension_adj_old (G.induce S) ⟨h, hhS⟩ ⟨h, hhS⟩ ⟨y, hyS⟩).mpr hhy
  · exact (pendantExtension_even_attach_iff (G.induce S) ⟨h, hhS⟩).mpr hhOdd
  · exact (pendantExtension_even_old_ne (G.induce S) ⟨h, hhS⟩ ⟨y, hyS⟩
      (fun e => hneq (congrArg Subtype.val e).symm)).mpr hyEven
  · exact pendantExtension_cap_induce_of_native_closure S h y hhS hyS hh hclosed hcap

/-- The strict native cut-piece budget directly consumes Xie's cross-type
edge-minimality resource once the native pendant instance has been built. -/
theorem adjacent_pendant_induce_conclusion_of_cut_budget
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    [Fintype S] [Fintype T]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S)
    (M : AdjacentEdgeMinimalCounterexample G h y)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card)
    (hpendant : AdjacentInstance (pendantExtension (G.induce S) ⟨h, hhS⟩)
      (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩)) :
    AdjacentConclusion (pendantExtension (G.induce S) ⟨h, hhS⟩)
      (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩) := by
  let J := pendantExtension (G.induce S) ⟨h, hhS⟩
  have hsmall : J.edgeFinset.card < G.edgeFinset.card :=
    pendantExtension_induce_edgeFinset_lt_of_cut_piece S T h hhS hgraph
      hSsupport hTsupport hinter hTcount
  let finJ : Fintype J.edgeSet :=
    (SimpleGraph.map (Function.Embedding.inl : S ↪ S ⊕ Unit) (G.induce S)).fintypeEdgeSetSup
      (SimpleGraph.edge (.inl ⟨h, hhS⟩ : S ⊕ Unit) (.inr ()))
  apply M.2 (S ⊕ Unit) J (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩) ?_ hpendant
  calc
    _ = @Fintype.card J.edgeSet J.fintypeEdgeSet :=
      @SimpleGraph.edgeFinset_card _ J J.fintypeEdgeSet
    _ = @Fintype.card J.edgeSet finJ :=
      @Fintype.card_congr _ _ J.fintypeEdgeSet finJ (Equiv.refl _)
    _ = (@SimpleGraph.edgeFinset _ J finJ).card :=
      (@SimpleGraph.edgeFinset_card _ J finJ).symm
    _ < (@SimpleGraph.edgeFinset _ G G.fintypeEdgeSet).card := by
      simpa only [J, finJ] using hsmall
    _ = @Fintype.card G.edgeSet G.fintypeEdgeSet :=
      @SimpleGraph.edgeFinset_card _ G G.fintypeEdgeSet
    _ = _ := (@SimpleGraph.edgeFinset_card _ G G.fintypeEdgeSet).symm

/-- Literal non-singleton odd/odd cut wrapper.  It is the source-facing
consumer of the native closure, native pendant instance, and strict edge
budget; its remaining hypotheses are exactly the local branch facts to be
derived by the selected-cut analysis. -/
theorem adjacent_native_odd_cut_non_singleton_conclusion
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hyEven : Even ((G.induce S).degree ⟨y, hyS⟩))
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card) :
    AdjacentConclusion (pendantExtension (G.induce S) ⟨h, hhS⟩)
      (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩) := by
  letI : DecidableRel (pendantExtension (G.induce S) ⟨h, hhS⟩).Adj :=
    Gallai.instDecidableRelAdjPendantExtension (G.induce S) ⟨h, hhS⟩
  apply adjacent_pendant_induce_conclusion_of_cut_budget S T h y hhS hyS M hgraph
    hSsupport hTsupport hinter hTcount
  apply adjacentInstance_pendant_induce_of_native_closure S h y hhS hyS hconnS
    M.counterexample.1.2.2.1 M.counterexample.1.2.1 hhOdd hyEven
    M.counterexample.1.2.2.2.1
  · intro v hv hvh
    exact neighborSet_subset_left_of_one_vertex_union S T h hinter hgraph v hv hvh
  · exact M.counterexample.1.2.2.2.2.2

/-- The nonshared adjacent hub has unchanged degree on its native cut side.
Thus its local evenness is not an extra odd/odd-branch hypothesis: it follows
from the global adjacent-instance input and one-vertex cut closure. -/
theorem induce_even_other_hub_of_one_vertex_union
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hyS : y ∈ S) (hyh : y ≠ h)
    (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hy : Even (G.degree y)) :
    Even ((G.induce S).degree ⟨y, hyS⟩) := by
  rw [SimpleGraph.degree_induce_of_neighborSet_subset
    (neighborSet_subset_left_of_one_vertex_union S T h hinter hgraph y hyS hyh)]
  exact hy

/-- The direct one-exception consumer on the odd/odd cut side containing the
other adjacent hub.  This is Xie's `P'_1`: it exposes `y` twice, while the
odd shared hub supplies the terminal carrier needed for the later merge. -/
theorem oneException_induce_left_other_endpoint_of_odd_hub
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S) (hyh : y ≠ h)
    (hconn : (G.induce S).Connected) (hhy : G.Adj h y)
    (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hyEven : Even ((G.induce S).degree ⟨y, hyS⟩))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition (G.induce S),
      D.size ≤ (Fintype.card S + 1) / 2 ∧
        0 < D.endpointCount ⟨h, hhS⟩ ∧ 2 ≤ D.endpointCount ⟨y, hyS⟩ := by
  have hyPos : 0 < (G.induce S).degree ⟨y, hyS⟩ :=
    ((G.induce S).degree_pos_iff_exists_adj ⟨y, hyS⟩).mpr
      ⟨⟨h, hhS⟩, hhy.symm⟩
  obtain ⟨D, hsD, hyD⟩ := one_exception_endpoint (G.induce S) ⟨y, hyS⟩
    hconn hyPos hyEven
    (induce_cap_left_of_native_closure_except_odd_hub S T h y hhS hyS
      hinter hgraph hhOdd hcap)
  exact ⟨D, hsD, D.endpointCount_pos_of_odd_degree ⟨h, hhS⟩ hhOdd, hyD⟩

/-- The opposite direct cut side has no copy of `y`.  With an odd local shared
hub, every local even vertex therefore lies under the ambient subcubic cap. -/
theorem induce_cap_right_of_native_closure_odd_hub
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhT : h ∈ T) (hyT : y ∉ T)
    (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hhOdd : Odd ((G.induce T).degree ⟨h, hhT⟩))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∀ v : T, Even ((G.induce T).degree v) → eDegree (G.induce T) v ≤ 3 := by
  classical
  intro v hv
  have hvh : v.val ≠ h := by
    intro e
    have ev : v = ⟨h, hhT⟩ := Subtype.ext e
    subst v
    exact (Nat.not_even_iff_odd.mpr hhOdd) hv
  have hclosed : G.neighborSet v.val ⊆ T :=
    neighborSet_subset_right_of_one_vertex_union S T h hinter hgraph v.val v.property hvh
  have hvG : Even (G.degree v.val) := by
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset hclosed] at hv
  let f : T ↪ V := Function.Embedding.subtype T
  have hsubset : (evenNeighbors (G.induce T) v).map f ⊆ evenNeighbors G v.val := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors (G := G.induce T) v w).mp hw
    have hwAdj : G.Adj v.val w.val := hvw
    have hwh : w.val ≠ h := by
      intro e
      have ew : w = ⟨h, hhT⟩ := Subtype.ext e
      subst w
      exact (Nat.not_even_iff_odd.mpr hhOdd) hwEven
    have hwclosed : G.neighborSet w.val ⊆ T :=
      neighborSet_subset_right_of_one_vertex_union S T h hinter hgraph w.val w.property hwh
    have hwG : Even (G.degree w.val) := by
      rwa [SimpleGraph.degree_induce_of_neighborSet_subset hwclosed] at hwEven
    exact (mem_evenNeighbors (G := G) v.val w.val).mpr ⟨hwAdj, hwG⟩
  calc
    eDegree (G.induce T) v = (evenNeighbors (G.induce T) v).card := rfl
    _ ≤ (evenNeighbors G v.val).card := by
      rw [← Finset.card_map f]
      exact Finset.card_le_card hsubset
    _ = eDegree G v.val := rfl
    _ ≤ 3 := hcap v.val hvG hvh (fun e => hyT (e ▸ v.property))

/-- The direct floor-or-SET consumer on the opposite odd/odd cut side.
Regardless of the floor-or-SET alternative, odd degree at the shared hub
supplies a terminal carrier for the final merge. -/
theorem floor_or_set_induce_right_endpoint_of_odd_hub
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhT : h ∈ T) (hyT : y ∉ T)
    (hconn : (G.induce T).Connected)
    (hinter : S ∩ T = {h})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hhOdd : Odd ((G.induce T).degree ⟨h, hhT⟩))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition (G.induce T),
      D.size ≤ (Fintype.card T + 1) / 2 ∧ 0 < D.endpointCount ⟨h, hhT⟩ := by
  rcases floor_or_set (G.induce T) hconn
    (induce_cap_right_of_native_closure_odd_hub S T h y hhT hyT
      hinter hgraph hhOdd hcap) with ⟨D, hD⟩ | hset
  · exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree ⟨h, hhT⟩ hhOdd⟩
  · obtain ⟨D, hD, _⟩ := hset.endpoint_reserve ⟨h, hhT⟩
    exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree ⟨h, hhT⟩ hhOdd⟩

/-- Source-facing non-singleton wrapper with the redundant local evenness of
the nonshared hub discharged from the global adjacent-instance hypothesis. -/
theorem adjacent_native_odd_cut_non_singleton_conclusion_of_global_y_even
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card) :
    AdjacentConclusion (pendantExtension (G.induce S) ⟨h, hhS⟩)
      (.inl ⟨h, hhS⟩) (.inl ⟨y, hyS⟩) := by
  apply adjacent_native_odd_cut_non_singleton_conclusion S T h y M hhS hyS
    hgraph hSsupport hTsupport hinter hconnS hhOdd
  · exact induce_even_other_hub_of_one_vertex_union S T h y hyS M.counterexample.1.2.1.symm
      hinter hgraph M.counterexample.1.2.2.2.2.1
  · exact hTcount

/-- A subtype graph and its spanning copy have equal degree at every old
vertex.  The proof uses finite neighbour-set cardinalities, avoiding a rewrite
across the choice of `Fintype` instance carried by `degree`. -/
theorem degree_spanningCoe {S : Set V} [DecidablePred (· ∈ S)]
    (H : SimpleGraph S) [DecidableRel H.Adj] (v : S) :
    H.spanningCoe.degree v = H.degree v := by
  rw [← SimpleGraph.ncard_neighborSet H.spanningCoe (v : V),
    ← SimpleGraph.ncard_neighborSet H v]
  change ((SimpleGraph.map (Function.Embedding.subtype S) H).neighborSet
      (Function.Embedding.subtype S v)).ncard = (H.neighborSet v).ncard
  rw [SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ (Function.Embedding.subtype S).injective]

/-- Across edge-disjoint cut pieces, an even shared hub that is odd on one
piece is odd on the other. -/
theorem odd_degree_right_of_even_sup_left_odd
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (h : V) (hdis : Disjoint (A.neighborFinset h) (B.neighborFinset h))
    (hhEven : Even ((A ⊔ B).degree h)) (hhOdd : Odd (A.degree h)) :
    Odd (B.degree h) := by
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hdeg : (A ⊔ B).degree h = A.degree h + B.degree h := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  rw [Nat.even_iff, hdeg] at hhEven
  rw [Nat.odd_iff] at hhOdd ⊢
  omega

/-- At a literal induced one-vertex cut, global evenness and local oddness of
the shared hub on the left side force local oddness on the right side.  This
is the parity input for the opposite one-exception pendant auxiliary. -/
theorem induce_odd_shared_hub_other_of_one_vertex_union
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hhEven : Even (G.degree h))
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩)) :
    Odd ((G.induce T).degree ⟨h, hhT⟩) := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAodd : Odd (A.degree h) := by
    have hAdeg : A.degree h = (G.induce S).degree ⟨h, hhS⟩ := by
      change (G.induce S).spanningCoe.degree h = (G.induce S).degree ⟨h, hhS⟩
      simpa using degree_spanningCoe (G.induce S) ⟨h, hhS⟩
    rwa [hAdeg]
  have hdis : Disjoint (A.neighborFinset h) (B.neighborFinset h) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' : A.Adj h w := (A.mem_neighborFinset h w).mp ha
    have hb' : B.Adj h w := (B.mem_neighborFinset h w).mp hb
    have hwS : w ∈ S := hSsupport ⟨h, ha'.symm⟩
    have hwT : w ∈ T := hTsupport ⟨h, hb'.symm⟩
    have hwh : w = h := by
      simpa only [hinter, Set.mem_singleton_iff] using
        (show w ∈ S ∩ T from ⟨hwS, hwT⟩)
    exact ha'.ne hwh.symm
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hdeg : (A ⊔ B).degree h = G.degree h := by
    rw [← SimpleGraph.ncard_neighborSet (A ⊔ B) h,
      ← SimpleGraph.ncard_neighborSet G h]
    exact congrArg Set.ncard (congrArg (fun K : SimpleGraph V => K.neighborSet h) hAB)
  have hhEvenAB : Even ((A ⊔ B).degree h) := by
    rwa [hdeg]
  have hBodd : Odd (B.degree h) :=
    odd_degree_right_of_even_sup_left_odd A B h hdis hhEvenAB hAodd
  have hBdeg : B.degree h = (G.induce T).degree ⟨h, hhT⟩ := by
    change (G.induce T).spanningCoe.degree h = (G.induce T).degree ⟨h, hhT⟩
    simpa using degree_spanningCoe (G.induce T) ⟨h, hhT⟩
  exact hBdeg ▸ hBodd

/-- The opposite native cut side has no copy of the other exception.  Its
pendant extension therefore satisfies the one-exception endpoint interface at
the newly even shared hub. -/
theorem oneException_pendant_induce_of_native_closure
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (T : Set V) [DecidablePred (· ∈ T)]
    (h y : V) (hhT : h ∈ T) (hyT : y ∉ T)
    (hconn : (G.induce T).Connected)
    (hhOdd : Odd ((G.induce T).degree ⟨h, hhT⟩))
    (hh : Even (G.degree h))
    (hclosed : ∀ v ∈ T, v ≠ h → G.neighborSet v ⊆ T)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition (pendantExtension (G.induce T) ⟨h, hhT⟩),
      D.size ≤ (Fintype.card (T ⊕ Unit) + 1) / 2 ∧
        2 ≤ D.endpointCount (.inl ⟨h, hhT⟩) := by
  classical
  letI : DecidableRel (pendantExtension (G.induce T) ⟨h, hhT⟩).Adj :=
    Gallai.instDecidableRelAdjPendantExtension (G.induce T) ⟨h, hhT⟩
  apply one_exception_endpoint (pendantExtension (G.induce T) ⟨h, hhT⟩) (.inl ⟨h, hhT⟩)
    (pendantExtension_connected (G.induce T) ⟨h, hhT⟩ hconn)
  · rw [pendantExtension_degree_attach]
    omega
  · exact (pendantExtension_even_attach_iff (G.induce T) ⟨h, hhT⟩).mpr hhOdd
  · intro v hv hvh
    cases v with
    | inr u =>
      cases u
      exact False.elim ((Nat.not_even_iff_odd.mpr
        (pendantExtension_odd_new (G.induce T) ⟨h, hhT⟩)) hv)
    | inl v =>
      have hvh' : v.val ≠ h := fun e =>
        hvh (congrArg Sum.inl (Subtype.ext e))
      have hvLocal : Even ((G.induce T).degree v) :=
        (pendantExtension_even_old_ne (G.induce T) ⟨h, hhT⟩ v
          (fun e => hvh' (congrArg Subtype.val e))).mp hv
      have hvG : Even (G.degree v.val) := by
        rwa [SimpleGraph.degree_induce_of_neighborSet_subset
          (hclosed v.val v.property hvh')] at hvLocal
      let f : T ⊕ Unit ↪ V ⊕ Unit :=
        (Function.Embedding.subtype T).sumMap (Function.Embedding.refl Unit)
      have hsubset : (evenNeighbors (pendantExtension (G.induce T) ⟨h, hhT⟩) (.inl v)).map f ⊆
          (evenNeighbors G v.val).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
        intro z hz
        obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hz
        cases q with
        | inr u =>
          cases u
          exact False.elim ((Nat.not_even_iff_odd.mpr
            (pendantExtension_odd_new (G.induce T) ⟨h, hhT⟩))
            ((mem_evenNeighbors (G := pendantExtension (G.induce T) ⟨h, hhT⟩)
              (.inl v) (.inr ())).mp hq).2)
        | inl w =>
          obtain ⟨hvw, hwEven⟩ :=
            (mem_evenNeighbors (G := pendantExtension (G.induce T) ⟨h, hhT⟩)
              (.inl v) (.inl w)).mp hq
          have hwAdj : G.Adj v.val w.val :=
            (pendantExtension_adj_old (G.induce T) ⟨h, hhT⟩ v w).mp hvw
          by_cases hwh : w.val = h
          · rw [hwh] at hwAdj
            exact Finset.mem_map.mpr ⟨h,
              (mem_evenNeighbors (G := G) v.val h).mpr ⟨hwAdj, hh⟩, by
                change Sum.inl h = Sum.inl w.val
                exact congrArg Sum.inl hwh.symm⟩
          · have hwLocal : Even ((G.induce T).degree w) :=
              (pendantExtension_even_old_ne (G.induce T) ⟨h, hhT⟩ w
                (fun e => hwh (congrArg Subtype.val e))).mp hwEven
            have hwG : Even (G.degree w.val) := by
              rwa [SimpleGraph.degree_induce_of_neighborSet_subset
                (hclosed w.val w.property hwh)] at hwLocal
            exact Finset.mem_map.mpr ⟨w.val,
              (mem_evenNeighbors (G := G) v.val w.val).mpr ⟨hwAdj, hwG⟩, by rfl⟩
      calc
        eDegree (pendantExtension (G.induce T) ⟨h, hhT⟩) (.inl v) =
            (evenNeighbors (pendantExtension (G.induce T) ⟨h, hhT⟩) (.inl v)).card := rfl
        _ ≤ (evenNeighbors G v.val).card := by
          rw [← Finset.card_map f, ← Finset.card_map (Function.Embedding.inl : V ↪ V ⊕ Unit)]
          exact Finset.card_le_card hsubset
        _ = eDegree G v.val := rfl
        _ ≤ 3 := hcap v.val hvG hvh' (fun e => hyT (e ▸ v.property))

/-- Literal one-vertex-cut wrapper for the opposite native pendant auxiliary.
The other adjacent exception belongs to the first side, so it is absent from
the second; shared-hub oddness on that side is supplied by the cut parity
transport above. -/
theorem oneException_pendant_induce_opposite_of_one_vertex_union
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S)
    (hconnT : (G.induce T).Connected)
    (hneq : h ≠ y)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hhEven : Even (G.degree h))
    (hhOddS : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ y → eDegree G v ≤ 3) :
    ∃ D : Decomposition (pendantExtension (G.induce T) ⟨h, by
      have : h ∈ S ∩ T := by
        rw [hinter]
        simp
      exact this.2⟩),
      D.size ≤ (Fintype.card (T ⊕ Unit) + 1) / 2 ∧
        2 ≤ D.endpointCount (.inl ⟨h, by
          have : h ∈ S ∩ T := by
            rw [hinter]
            simp
          exact this.2⟩) := by
  have hhT : h ∈ T := by
    have : h ∈ S ∩ T := by
      rw [hinter]
      simp
    exact this.2
  have hyT : y ∉ T := by
    intro hyT
    have hyh : y = h := by
      simpa only [hinter, Set.mem_singleton_iff] using
        (show y ∈ S ∩ T from ⟨hyS, hyT⟩)
    exact hneq hyh.symm
  have hhOddT : Odd ((G.induce T).degree ⟨h, hhT⟩) :=
    induce_odd_shared_hub_other_of_one_vertex_union S T h hhS hhT hgraph
      hSsupport hTsupport hinter hhEven hhOddS
  exact oneException_pendant_induce_of_native_closure T h y hhT hyT hconnT
    hhOddT hhEven
    (neighborSet_subset_right_of_one_vertex_union S T h hinter hgraph)
    hcap

end Gallai.TwoException
