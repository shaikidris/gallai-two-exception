/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.AttachedMerge
public import Gallai.Operations.DecompositionSplit
public import Gallai.Operations.DoubleMerge
public import Gallai.Operations.SingleMerge
public import Gallai.Repair.Exposure
public import Gallai.Inputs.OneException
public import Gallai.Structure.CutVertexPieces
public import Gallai.TwoException.AdjacentMinimality

@[expose] public section

/-!
# Gluing consumer for Xie's adjacent cut claim

In the even-local branch of Claim 1 in Xie Theorem 1.4, the cut side not
containing the adjacent exceptions supplies two endpoints at the separator via
the one-exception theorem.  The other side supplies both independent Xie
outputs by minimality.  One attached merge preserves both off-separator
endpoint reserves and saves the required path.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {A B : SimpleGraph V} [DecidableRel A.Adj] [DecidableRel B.Adj]

/-- If a one-vertex cut is oriented away from `x`, then the adjacent vertex
`y` stays on `x`'s side provided the separator is neither hub.  This is the
literal side-placement fact used in Xie's Claim 1 before invoking adjacent
minimality on the right induced piece. -/
theorem adjacent_hubs_same_cut_side
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z x y : V) (hxS : x ∉ S) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hxy : G.Adj x y) : y ∈ T ∧ y ∉ S := by
  have hyS : y ∉ S := by
    intro hyS
    have hsup : ((G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe).Adj x y := by
      rw [hgraph]
      exact hxy
    have hsplit : (G.induce S).spanningCoe.Adj x y ∨
        (G.induce T).spanningCoe.Adj x y :=
      (SimpleGraph.sup_adj _ _ _ _).mp hsup
    rcases hsplit with hleft | hright
    · exact hxS ((spanning_induce_adj_iff G S x y).mp hleft).2.1
    · have hyT := ((spanning_induce_adj_iff G T x y).mp hright).2.2
      have hyz' : y = z := by
        have : y ∈ S ∩ T := ⟨hyS, hyT⟩
        simpa only [hinter, Set.mem_singleton_iff] using this
      exact hyz hyz'
  have hyT : y ∈ T := by
    have : y ∈ S ∪ T := by rw [hcover]; trivial
    exact this.resolve_left hyS
  exact ⟨hyT, hyS⟩

/-- At an even separator, the right graph of a one-vertex union inherits the
subcubic E-degree cap away from the two named adjacent exceptions.  This is
the cap calculation in the even-local branch of Xie's Claim 1, stated without
the unrelated bare prescribed-endpoint hypotheses. -/
theorem adjacent_cap_right
    (z x y : V)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v, Even (B.degree v) → v ≠ x → v ≠ y → eDegree B v ≤ 3 := by
  intro v hv hvx hvy
  have hparity : Even ((A ⊔ B).degree z) ∨ Odd (B.degree z) := Or.inl hz
  by_cases hp : ∃ w, B.Adj v w
  · exact (eDegree_le_one_vertex_union A B z v hmeet hparity).trans
      (hcap v (even_positive_in_one_vertex_union A B z v hmeet hparity hv hp)
        hvx hvy)
  · have hn : B.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hd : B.degree v = 0 := by
      rw [← B.card_neighborFinset_eq_degree, hn, Finset.card_empty]
    have he := eDegree_le_degree (G := B) v
    omega

/-- The left-side even-neighbour inclusion for a one-vertex union.  It is
proved without commuting the union, because degree and E-degree expressions
carry graph-indexed adjacency-decision data. -/
theorem adjacent_evenNeighbors_subset_left
    (z v : V) (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z) :
    evenNeighbors A v ⊆ evenNeighbors (A ⊔ B) v := by
  intro w hw
  obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors v w).mp hw
  refine (mem_evenNeighbors v w).mpr ⟨Or.inl hvw, ?_⟩
  by_cases hwz : w = z
  · subst w
    exact hz
  · have hBiso : ∀ q, ¬ B.Adj w q := by
      intro q hwq
      exact hwz (hmeet w ⟨v, hvw.symm⟩ ⟨q, hwq⟩)
    have hzero : B.neighborFinset w = ∅ := by
      ext q
      simp [hBiso q]
    have hdeg : (A ⊔ B).degree w = A.degree w := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
        hzero]
      simp
    rw [hdeg]
    exact hwEven

/-- At an even separator, the left graph of a one-vertex union inherits the
subcubic E-degree cap away from the two named adjacent exceptions. -/
theorem adjacent_cap_left
    (z x y : V) (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ x → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v, Even (A.degree v) → v ≠ x → v ≠ y → eDegree A v ≤ 3 := by
  intro v hv hvx hvy
  by_cases hp : ∃ w, A.Adj v w
  · have hEven : Even ((A ⊔ B).degree v) := by
      rcases hp with ⟨w, hvw⟩
      by_cases hvz : v = z
      · subst v
        exact hz
      · have hBiso : ∀ q, ¬ B.Adj v q := by
          intro q hvq
          exact hvz (hmeet v ⟨w, hvw⟩ ⟨q, hvq⟩)
        have hzero : B.neighborFinset v = ∅ := by
          ext q
          simp [hBiso q]
        have hdeg : (A ⊔ B).degree v = A.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree,
            SimpleGraph.neighborFinset_sup, hzero]
          simp
        rw [hdeg]
        exact hv
    exact (Finset.card_le_card
      (adjacent_evenNeighbors_subset_left (A := A) (B := B) z v hz hmeet)).trans
      (hcap v hEven hvx hvy)
  · have hzero : A.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hdeg : A.degree v = 0 := by
      rw [← A.card_neighborFinset_eq_degree, hzero, Finset.card_empty]
    have hle := eDegree_le_degree (G := A) v
    omega

/-- The left cut side receives the published one-exception endpoint reserve in
the even-local branch of Xie's Claim 1.  The side excludes both adjacent hubs,
so the transported cap has no exceptional vertex other than the separator. -/
theorem adjacent_left_cut_endpoint_reserve
    (S : Set V) [DecidablePred (· ∈ S)]
    (z a x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hzS : z ∈ S) (haS : a ∈ S) (haz : a ≠ z)
    (hxS : x ∉ S) (hyS : y ∉ S)
    (hconn : (A.induce S).Connected) (hz : Even ((A ⊔ B).degree z))
    (hzA : Even (A.degree z))
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) :
    ∃ D : Decomposition (A.induce S), D.size ≤ (Fintype.card S + 1) / 2 ∧
      2 ≤ D.endpointCount ⟨z, hzS⟩ := by
  have hnt : Nontrivial S := ⟨⟨z, hzS⟩, ⟨a, haS⟩,
    fun e => haz (congrArg Subtype.val e).symm⟩
  have hzPos : 0 < (A.induce S).degree ⟨z, hzS⟩ :=
    hconn.preconnected.degree_pos_of_nontrivial ⟨z, hzS⟩
  have hzEven : Even ((A.induce S).degree ⟨z, hzS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hzA
  have hcapA := adjacent_cap_left (A := A) (B := B) z x y hz hmeet H.2.2.2.2.2
  have hcap : ∀ v : S, Even ((A.induce S).degree v) →
      v ≠ ⟨z, hzS⟩ → eDegree (A.induce S) v ≤ 3 := by
    intro v hv _
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA v.val hvA
    · intro hvx
      exact hxS (hvx ▸ v.property)
    · intro hvy
      exact hyS (hvy ▸ v.property)
  exact one_exception_endpoint (A.induce S) ⟨z, hzS⟩ hconn hzPos hzEven hcap

/-- A decomposition of a support-contained induced cut piece lifts back to its
ambient spanning piece without changing its number of paths or endpoint
multiplicities on the piece.  This is deliberately local to the adjacent-cut
argument: importing the bare two-exception cut chain here would obscure the
dependency boundary of Xie's Claim 1. -/
theorem adjacent_lift_cut_piece {H : SimpleGraph V} (S : Set V)
    [DecidablePred (· ∈ S)] (hs : H.support ⊆ S) (D : Decomposition (H.induce S)) :
    ∃ E : Decomposition H, E.size = D.size ∧
      ∀ w : S, E.endpointCount w.val = D.endpointCount w := by
  have hgraph : (H.induce S).map (Function.Embedding.subtype _) = H :=
    (H.spanningCoe_induce_eq_self S).mpr hs
  have hout : ∃ E : Decomposition ((H.induce S).map (Function.Embedding.subtype _)),
      E.size = D.size ∧ ∀ w : S, E.endpointCount w.val = D.endpointCount w :=
    ⟨D.map (Function.Embedding.subtype _), rfl,
      fun w => D.map_endpointCount (Function.Embedding.subtype _) w⟩
  rwa [hgraph] at hout

/-- The normalized left reserve, lifted to the literal left spanning cut piece
of an actual graph.  The local parity of the separator is an explicit branch
assumption, matching the even-local branch of Xie's Claim 1. -/
theorem adjacent_actual_left_cut_reserve
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (H : AdjacentInstance G x y)
    (hzS : z ∈ S) (haS : a ∈ S) (haz : a ≠ z)
    (hxS : x ∉ S) (hyS : y ∉ S)
    (hinter : ∀ w, w ∈ S → w ∈ T → w = z)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hz : Even (G.degree z))
    (hzSlocal : Even ((G.induce S).spanningCoe.degree z)) :
    ∃ D : Decomposition ((G.induce S).spanningCoe),
      D.size ≤ (Fintype.card S + 1) / 2 ∧ 2 ≤ D.endpointCount z := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have HAB : AdjacentInstance (A ⊔ B) x y :=
    AdjacentInstance.congr x y hAB.symm H
  have hzAB : Even ((A ⊔ B).degree z) :=
    adjacent_even_degree_congr z hAB.symm hz
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨q', hBq⟩
    have hwS := ((spanning_induce_adj_iff G S w q).mp hAq).2.1
    have hwT := ((spanning_induce_adj_iff G T w q').mp hBq).2.1
    exact hinter w hwS hwT
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  obtain ⟨D0, hD0size, hzD0⟩ := adjacent_left_cut_endpoint_reserve
    (A := A) (B := B) S z a x y HAB hA hzS haS haz hxS hyS hconnA hzAB
      hzSlocal hmeet
  obtain ⟨D, hDsize, hDends⟩ := adjacent_lift_cut_piece S hA D0
  refine ⟨D, ?_, ?_⟩
  · rw [hDsize]
    exact hD0size
  · rw [hDends ⟨z, hzS⟩]
    exact hzD0

/-- Lift both independent endpoint outputs of a supported induced adjacent
instance to its ambient cut piece.  The result remains two decompositions;
this intentionally does not assert unsupported simultaneous exposure. -/
theorem adjacent_lift_conclusion {B : SimpleGraph V} [DecidableRel B.Adj] (T : Set V)
    [DecidablePred (· ∈ T)] (hB : B.support ⊆ T)
    {x y : V} (hxT : x ∈ T) (hyT : y ∈ T)
    (hcard : Fintype.card T ≤ Fintype.card V)
    (H : AdjacentConclusion (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩) :
    AdjacentConclusion B x y := by
  constructor
  · rcases H.1 with ⟨D, hDsize, hxD⟩
    obtain ⟨E, hEsize, hEends⟩ := adjacent_lift_cut_piece T hB D
    refine ⟨E, ?_, ?_⟩
    · rw [hEsize]
      omega
    · rw [hEends ⟨x, hxT⟩]
      exact hxD
  · rcases H.2 with ⟨D, hDsize, hyD⟩
    obtain ⟨E, hEsize, hEends⟩ := adjacent_lift_cut_piece T hB D
    refine ⟨E, ?_, ?_⟩
    · rw [hEsize]
      omega
    · rw [hEends ⟨y, hyT⟩]
      exact hyD

/-- Assemble the smaller adjacent instance on the actual right cut side.
The geometric facts about the cut are explicit inputs: the right piece retains
the hub edge and both hub degrees, has no support outside its subtype, and is
connected there.  The theorem packages exactly the transport needed before
invoking Xie minimality. -/
theorem adjacentInstance_induced_right_of_union
    (S : Set V) [DecidablePred (· ∈ S)]
    (z x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hs : B.support ⊆ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hconn : (B.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hxyB : B.Adj x y)
    (hxdeg : (A ⊔ B).degree x = B.degree x)
    (hydeg : (A ⊔ B).degree y = B.degree y) :
    AdjacentInstance (B.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
  rcases H with ⟨_, hne, _, hxEven, hyEven, hcap⟩
  refine ⟨hconn, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hne (Subtype.ext_iff.mp h)
  · exact hxyB
  · rw [SimpleGraph.degree_induce_of_support_subset hs, ← hxdeg]
    exact hxEven
  · rw [SimpleGraph.degree_induce_of_support_subset hs, ← hydeg]
    exact hyEven
  · intro v hv hvx hvy
    rw [eDegree_induce_of_support_subset B S hs v]
    apply adjacent_cap_right (A := A) (B := B) z x y hz hmeet hcap v.val ?_
      (fun h => hvx (Subtype.ext h)) (fun h => hvy (Subtype.ext h))
    rwa [SimpleGraph.degree_induce_of_support_subset hs v] at hv

/-- A literal one-vertex partition whose right side contains `x` produces the
smaller adjacent instance required in the even-local branch of Xie's Claim 1.
The conclusion lives on the supported subtype of the right spanning piece;
the ambient piece need not itself be connected because it can have isolates
outside `T`. -/
theorem adjacent_actual_right_cut_instance
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z x y : V) (H : AdjacentInstance G x y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hxT : x ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnT : (G.induce T).Connected) (hz : Even (G.degree z)) :
    ∃ hyT : y ∈ T, y ∉ S ∧
      AdjacentInstance ((G.induce T).spanningCoe.induce T)
        ⟨x, hxT⟩ ⟨y, hyT⟩ := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hxS : x ∉ S := by
    intro hxS
    have : x ∈ S ∩ T := ⟨hxS, hxT⟩
    have : x = z := by
      simpa only [hinter, Set.mem_singleton_iff] using this
    exact hxz this
  have hyT : y ∈ T := (adjacent_hubs_same_cut_side S T z x y hxS hyz
    hcover hinter hgraph H.2.2.1).1
  have hyS : y ∉ S := (adjacent_hubs_same_cut_side S T z x y hxS hyz
    hcover hinter hgraph H.2.2.1).2
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨a, ha⟩
    rcases hBw with ⟨b, hb⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨a, ha⟩, hB ⟨b, hb⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hxAiso : ∀ w, ¬ A.Adj x w := fun w hxw => hxS (hA ⟨w, hxw⟩)
  have hyAiso : ∀ w, ¬ A.Adj y w := fun w hyw => hyS (hA ⟨w, hyw⟩)
  have hxdeg : (A ⊔ B).degree x = B.degree x :=
    degree_union_of_left_isolated A B x hxAiso
  have hydeg : (A ⊔ B).degree y = B.degree y :=
    degree_union_of_left_isolated A B y hyAiso
  have hxyB : B.Adj x y := by
    exact (spanning_induce_adj_iff G T x y).mpr ⟨H.2.2.1, hxT, hyT⟩
  have hzAB : Even ((A ⊔ B).degree z) := by
    exact adjacent_even_degree_congr z hAB.symm hz
  have HAB : AdjacentInstance (A ⊔ B) x y :=
    AdjacentInstance.congr x y hAB.symm H
  exact ⟨hyT, hyS,
    adjacentInstance_induced_right_of_union T z x y HAB hB hxT hyT hconnB
      hzAB hmeet hxyB hxdeg hydeg⟩

/-- The hub-containing side of an even/even separator is itself an adjacent
instance after restricting to its connected support.  Unlike the ordinary
right-side transport, the shared hub `x` need not retain its ambient degree;
its local evenness is therefore an explicit hypothesis.  The other hub `y`
is absent from the opposite piece, so its degree is preserved. -/
theorem adjacentInstance_induced_left_hub_of_union
    (S : Set V) [DecidablePred (· ∈ S)]
    (x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (hconn : (A.induce S).Connected)
    (hxEven : Even (A.degree x))
    (hyBiso : ∀ w, ¬ B.Adj y w)
    (hxyA : A.Adj x y)
    (hz : Even ((A ⊔ B).degree x))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x) :
    AdjacentInstance (A.induce S) ⟨x, hxS⟩ ⟨y, hyS⟩ := by
  rcases H with ⟨_, hne, _, _, hyEven, hcap⟩
  refine ⟨hconn, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hne (Subtype.ext_iff.mp h)
  · exact hxyA
  · rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hxEven
  · rw [SimpleGraph.degree_induce_of_support_subset hA]
    have hydeg : (A ⊔ B).degree y = A.degree y := by
      have hzero : B.neighborFinset y = ∅ := by
        ext w
        simp [hyBiso w]
      rw [← (A ⊔ B).card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_sup, hzero]
      simp
    rwa [← hydeg]
  · intro v hv hvx hvy
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    exact adjacent_cap_left (A := A) (B := B) x x y hz hmeet hcap v.val hvA
      (fun h => hvx (Subtype.ext h)) (fun h => hvy (Subtype.ext h))

/-- The cut component opposite the nonshared hub has only the shared hub as a
possible E-degree exception.  This is the cap input for the one-exception
endpoint theorem in Xie's even/even hub case. -/
theorem one_exception_cap_induced_right_of_absent_other_hub
    (T : Set V) [DecidablePred (· ∈ T)]
    (x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hB : B.support ⊆ T) (hxT : x ∈ T) (hyT : y ∉ T)
    (hz : Even ((A ⊔ B).degree x))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x) :
    ∀ v : T, Even ((B.induce T).degree v) → v ≠ ⟨x, hxT⟩ →
      eDegree (B.induce T) v ≤ 3 := by
  intro v hv hvx
  rw [eDegree_induce_of_support_subset B T hB v]
  have hvB : Even (B.degree v.val) := by
    rwa [SimpleGraph.degree_induce_of_support_subset hB v] at hv
  have hvx' : v.val ≠ x := fun h => hvx (Subtype.ext h)
  have hvy : v.val ≠ y := fun h => hyT (h ▸ v.property)
  exact adjacent_cap_right (A := A) (B := B) x x y hz hmeet H.2.2.2.2.2
    v.val hvB hvx' hvy

/-- Endpoint-theorem consumer for the hub-free side of Xie's even/even
separator.  All remaining premises are literal properties of the cut piece. -/
theorem one_exception_endpoint_induced_right_of_absent_other_hub
    (T : Set V) [DecidablePred (· ∈ T)]
    (x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hB : B.support ⊆ T) (hxT : x ∈ T) (hyT : y ∉ T)
    (hconn : (B.induce T).Connected)
    (hxpos : 0 < (B.induce T).degree ⟨x, hxT⟩)
    (hxEven : Even ((B.induce T).degree ⟨x, hxT⟩))
    (hz : Even ((A ⊔ B).degree x))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x) :
    ∃ D : Decomposition (B.induce T), D.size ≤ (Fintype.card T + 1) / 2 ∧
      2 ≤ D.endpointCount ⟨x, hxT⟩ := by
  apply one_exception_endpoint (B.induce T) ⟨x, hxT⟩ hconn hxpos hxEven
  exact one_exception_cap_induced_right_of_absent_other_hub
    (A := A) (B := B) T x y H hB hxT hyT hz hmeet

/-- A literal separation between a non-hub vertex and `x` supplies the right
cut piece used in Xie's Claim 1.  This is only the structural/minimality input:
it extracts the vertex-smaller right adjacent instance and does not yet build
the left-side endpoint reserve or perform the final merge. -/
theorem adjacent_cut_right_instance_of_separation
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (z a x y : V) (H : AdjacentInstance G x y)
    (haz : a ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsep : ¬ (G.induce {v | v ≠ z}).Reachable ⟨a, haz⟩ ⟨x, hxz⟩)
    (hz : Even (G.degree z)) :
    ∃ S T : Set V, ∃ _ : DecidablePred (· ∈ S), ∃ _ : DecidablePred (· ∈ T),
      a ∈ S ∧ ∃ hxT : x ∈ T, ∃ hyT : y ∈ T,
        Fintype.card T < Fintype.card V ∧
          AdjacentInstance ((G.induce T).spanningCoe.induce T)
            ⟨x, hxT⟩ ⟨y, hyT⟩ := by
  classical
  obtain ⟨S, T, hcover, hinter, haS, hxT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G H.1 z a x haz hxz hsep
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  obtain ⟨hyT, _, hright⟩ :=
    adjacent_actual_right_cut_instance S T z x y H hxz hyz hxT
      hcover hinter hgraph hconnT hz
  have hinter' : T ∩ S = {z} := by
    simpa only [Set.inter_comm] using hinter
  have hsmall : Fintype.card T < Fintype.card V :=
    cut_piece_card_lt T S z a hinter' haS haz
  exact ⟨S, T, inferInstance, inferInstance, haS, hxT, hyT, hsmall, hright⟩

/-- Source Claim 1's even-local gluing step.  The budget premise is stated
after the single merge, so callers may obtain it either from the actual
one-vertex cardinality identity or from a stronger local bound. -/
theorem xie_adjacent_glue_left_reserve_separate
    (D : Decomposition A) (Ex Ey : Decomposition B)
    (z x y : V) (hxz : x ≠ z) (hyz : y ≠ z)
    (hzD : 2 ≤ D.endpointCount z)
    (hinc : ∃ w, B.Adj z w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hbudgetX : D.size + Ex.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hbudgetY : D.size + Ey.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hxEx : 2 ≤ Ex.endpointCount x)
    (hyEy : 2 ≤ Ey.endpointCount y) :
    AdjacentConclusion (A ⊔ B) x y := by
  obtain ⟨Fx, hFxsize, hFxends⟩ := D.glue_at_exposed_vertex Ex z hzD hinc hmeet
  obtain ⟨Fy, hFysize, hFyends⟩ := D.glue_at_exposed_vertex Ey z hzD hinc hmeet
  constructor
  · refine ⟨Fx, ?_, ?_⟩
    · omega
    · have hx := hFxends x
      simp only [hxz.symm, if_false, mul_zero, Nat.add_zero] at hx
      omega
  · refine ⟨Fy, ?_, ?_⟩
    · omega
    · have hy := hFyends y
      simp only [hyz.symm, if_false, mul_zero, Nat.add_zero] at hy
      omega

/-- The odd-local split-degree counterpart of the adjacent cut merge.  One
terminal carrier at the separator on each side suffices to save one path; the
two independent right-side outputs are merged separately, preserving their
respective endpoint reserves away from the separator. -/
theorem xie_adjacent_glue_left_endpoint_separate
    (D : Decomposition A) (Ex Ey : Decomposition B)
    (z x y : V) (hxz : x ≠ z) (hyz : y ≠ z)
    (hzD : 0 < D.endpointCount z)
    (hzEx : 0 < Ex.endpointCount z) (hzEy : 0 < Ey.endpointCount z)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hbudgetX : D.size + Ex.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hbudgetY : D.size + Ey.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hxEx : 2 ≤ Ex.endpointCount x)
    (hyEy : 2 ≤ Ey.endpointCount y) :
    AdjacentConclusion (A ⊔ B) x y := by
  obtain ⟨Fx, hFxsize, hFxends⟩ := D.single_merge_endpoints Ex z hzD hzEx hmeet
  obtain ⟨Fy, hFysize, hFyends⟩ := D.single_merge_endpoints Ey z hzD hzEy hmeet
  constructor
  · refine ⟨Fx, ?_, ?_⟩
    · omega
    · have hx := hFxends x
      simp only [hxz.symm, if_false, mul_zero, Nat.add_zero] at hx
      omega
  · refine ⟨Fy, ?_, ?_⟩
    · omega
    · have hy := hFyends y
      simp only [hyz.symm, if_false, mul_zero, Nat.add_zero] at hy
      omega

/-- Direct hub-side gluing for Xie's even/even separator case.  A twice
exposed hub on both pieces loses exactly two endpoint incidences on merging,
while every distinct prescribed endpoint count is preserved additively. -/
theorem xie_adjacent_hub_even_glue
    (D : Decomposition A) (E : Decomposition B)
    (x y : V) (hxy : x ≠ y)
    (hxD : 2 ≤ D.endpointCount x) (hxE : 2 ≤ E.endpointCount x)
    (hyD : 2 ≤ D.endpointCount y)
    (hinc : ∃ w, B.Adj x w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x)
    (hbudget : D.size + E.size - 1 ≤ (Fintype.card V + 1) / 2) :
    ∃ Fx Fy : Decomposition (A ⊔ B),
      Fx.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ Fx.endpointCount x ∧
      Fy.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ Fy.endpointCount y := by
  obtain ⟨Fx, hFxsize, hFxends⟩ := D.glue_at_exposed_vertex E x hxD hinc hmeet
  obtain ⟨Fy, hFysize, hFyends⟩ := D.glue_at_exposed_vertex E x hxD hinc hmeet
  refine ⟨Fx, Fy, ?_, ?_, ?_, ?_⟩
  · omega
  · have hx := hFxends x
    simp at hx
    omega
  · omega
  · have hy := hFyends y
    simp [hxy] at hy
    omega

/-- Split a specified internal hub carrier.  This is the exact local operation
used in Xie's even/even hub case when the decomposition exposing `y` has no
endpoint at the shared hub. -/
theorem split_internal_hub_carrier
    (D : Decomposition A) (i : Fin D.size) (x : V)
    (hx : x ∈ (D.path i).walk.support)
    (hstart : (D.path i).start ≠ x) (hfinish : x ≠ (D.path i).finish) :
    ∃ E : Decomposition A, E.size = D.size + 1 ∧
      E.endpointCount x = D.endpointCount x + 2 ∧
      ∀ w, w ≠ x → E.endpointCount w = D.endpointCount w := by
  let E := D.splitAt i x hx hstart hfinish
  refine ⟨E, rfl, ?_, ?_⟩
  · rw [Decomposition.splitAt_endpointCount]
    simp
  · intro w hw
    rw [Decomposition.splitAt_endpointCount]
    simp [hw.symm]

/-- Full zero-endpoint repair for the `y`-output of Xie's even/even hub
separator case.  `exists_expose_even` either keeps an already exposed hub or
splits one internal carrier; the subsequent merge recovers that single cost.
The two output decompositions remain independent, as required by Xie's
theorem. -/
theorem xie_adjacent_hub_even_glue_after_exposure
    (Dx Dy : Decomposition A) (R : Decomposition B)
    (x y : V) (hxy : x ≠ y)
    (hxDx : 2 ≤ Dx.endpointCount x) (hyDy : 2 ≤ Dy.endpointCount y)
    (hxR : 2 ≤ R.endpointCount x)
    (hxpos : 0 < A.degree x) (hxEven : Even (A.degree x))
    (hinc : ∃ w, B.Adj x w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x)
    (hbudgetX : Dx.size + R.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hbudgetY : Dy.size + R.size ≤ (Fintype.card V + 1) / 2) :
    AdjacentConclusion (A ⊔ B) x y := by
  obtain ⟨Fx, hFxsize, hFxends⟩ := Dx.glue_at_exposed_vertex R x hxDx hinc hmeet
  obtain ⟨Ey, hEysize, hxEy, hpreserve⟩ := Dy.exists_expose_even x hxpos hxEven
  obtain ⟨Fy, hFysize, hFyends⟩ := Ey.glue_at_exposed_vertex R x hxEy hinc hmeet
  constructor
  · refine ⟨Fx, ?_, ?_⟩
    · omega
    · have hx := hFxends x
      simp at hx
      omega
  · refine ⟨Fy, ?_, ?_⟩
    · by_cases hz : Dy.endpointCount x = 0
      · simp [hz] at hEysize
        omega
      · simp [hz] at hEysize
        omega
    · have hy := hFyends y
      rw [hpreserve y hxy.symm] at hy
      simp [hxy] at hy
      omega

/-- Source-faithful exact-budget completion of the even/even hub separator.
The `x`-output uses the ordinary one-join assembly.  For the independent
`y`-output, a possible one-path exposure repair at `x` is paid back by two
joins, whose endpoint accounting preserves the distinct vertex `y`. -/
theorem xie_adjacent_hub_even_glue_after_exposure_double
    (Dx Dy : Decomposition A) (R : Decomposition B)
    (x y : V) (hxy : x ≠ y)
    (hxDx : 2 ≤ Dx.endpointCount x) (hyDy : 2 ≤ Dy.endpointCount y)
    (hxR : 2 ≤ R.endpointCount x)
    (hxpos : 0 < A.degree x) (hxEven : Even (A.degree x))
    (hinc : ∃ w, B.Adj x w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = x)
    (hbudgetX : Dx.size + R.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hbudgetY : Dy.size + R.size - 1 ≤ (Fintype.card V + 1) / 2) :
    AdjacentConclusion (A ⊔ B) x y := by
  obtain ⟨Fx, hFxsize, hFxends⟩ := Dx.glue_at_exposed_vertex R x hxDx hinc hmeet
  obtain ⟨Ey, hEysize, hxEy, hpreserve⟩ := Dy.exists_expose_even x hxpos hxEven
  obtain ⟨Fy, hFysize, hFyends⟩ := Ey.double_merge_endpoints R x hxEy hxR hmeet
  constructor
  · refine ⟨Fx, ?_, ?_⟩
    · omega
    · have hx := hFxends x
      simp at hx
      omega
  · refine ⟨Fy, ?_, ?_⟩
    · rw [hFysize, hEysize]
      by_cases hz : Dy.endpointCount x = 0
      · simp [hz]
        omega
      · simp [hz]
        omega
    · have hy := hFyends y hxy.symm
      rw [hpreserve y hxy.symm] at hy
      omega

/-- The reconstruction core of the odd-local cut branch.  It is independent
of the choice of minimality measure: callers supply the right induced
adjacent conclusion, while this theorem performs the parity transports,
left floor-or-SET construction, two separate lifts, and single merges. -/
theorem adjacent_odd_local_union_false_of_right
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hfail : ¬ AdjacentConclusion (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hzS : z ∈ S) (hxS : x ∉ S) (hyS : y ∉ S)
    (hxT : x ∈ T) (hyT : y ∈ T)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hconnS : (A.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Odd (A.degree z))
    (hrightOut : AdjacentConclusion (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) : False := by
  have hzT : z ∈ T := by
    have : z ∈ S ∩ T := by rw [hinter]; simp
    exact this.2
  have hcapA0 := adjacent_cap_left (A := A) (B := B) z x y hz hmeet H.2.2.2.2.2
  have hcapA : ∀ v : S, Even ((A.induce S).degree v) →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA0 v.val hvA
    · intro h
      exact hxS (h ▸ v.property)
    · intro h
      exact hyS (h ▸ v.property)
  have hzOddAS : Odd ((A.induce S).degree ⟨z, hzS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hzA
  have hdis : Disjoint (A.neighborFinset z) (B.neighborFinset z) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset z w).mp ha
    have hb' := (B.mem_neighborFinset z w).mp hb
    exact ha'.ne (hmeet w ⟨z, ha'.symm⟩ ⟨z, hb'.symm⟩).symm
  have hzdeg : (A ⊔ B).degree z = A.degree z + B.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hzOddB : Odd (B.degree z) := by
    rw [Nat.even_iff, hzdeg] at hz
    rw [Nat.odd_iff] at hzA ⊢
    omega
  have hzOddBT : Odd ((B.induce T).degree ⟨z, hzT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hzOddB
  obtain ⟨D0, hD0size, hzD0⟩ : ∃ D : Decomposition (A.induce S),
      D.size ≤ (Fintype.card S + 1) / 2 ∧ 0 < D.endpointCount ⟨z, hzS⟩ := by
    rcases floor_or_set (A.induce S) hconnS hcapA with ⟨D, hD⟩ | hset
    · exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree _ hzOddAS⟩
    · obtain ⟨D, hD, hzD⟩ := hset.endpoint_reserve ⟨z, hzS⟩
      exact ⟨D, hD, by omega⟩
  obtain ⟨D, hDsize, hDends⟩ := adjacent_lift_cut_piece S hA D0
  have hzD : 0 < D.endpointCount z := by
    rw [hDends ⟨z, hzS⟩]
    exact hzD0
  obtain ⟨Ex0, hEx0size, hxEx0⟩ := hrightOut.1
  obtain ⟨Ey0, hEy0size, hyEy0⟩ := hrightOut.2
  obtain ⟨Ex, hExsize, hExends⟩ := adjacent_lift_cut_piece T hB Ex0
  obtain ⟨Ey, hEysize, hEyends⟩ := adjacent_lift_cut_piece T hB Ey0
  have hxEx : 2 ≤ Ex.endpointCount x := by
    rw [hExends ⟨x, hxT⟩]
    exact hxEx0
  have hyEy : 2 ≤ Ey.endpointCount y := by
    rw [hEyends ⟨y, hyT⟩]
    exact hyEy0
  have hzEx : 0 < Ex.endpointCount z := by
    rw [hExends ⟨z, hzT⟩]
    exact Ex0.endpointCount_pos_of_odd_degree _ hzOddBT
  have hzEy : 0 < Ey.endpointCount z := by
    rw [hEyends ⟨z, hzT⟩]
    exact Ey0.endpointCount_pos_of_odd_degree _ hzOddBT
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  apply hfail
  exact xie_adjacent_glue_left_endpoint_separate D Ex Ey z x y hxz hyz hzD hzEx hzEy
    hmeet (by omega) (by omega) hxEx hyEy

/-- The full normalized odd-local cut contradiction in Xie's Claim 1.  Both
cut pieces have odd local degree at the separator.  The left piece therefore
uses the floor-or-SET alternative only for a ceiling decomposition and its
parity-forced terminal; the vertex-smaller right piece supplies the two
independent endpoint conclusions. -/
theorem adjacent_odd_local_union_not_minimal
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z x y : V) (M : AdjacentMinimalCounterexample (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hzS : z ∈ S) (hxS : x ∉ S) (hyS : y ∉ S)
    (hxT : x ∈ T) (hyT : y ∈ T)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hconnS : (A.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Odd (A.degree z))
    (hconnT : (B.induce T).Connected)
    (hsmall : Fintype.card T < Fintype.card V)
    (hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) : False := by
  have hzT : z ∈ T := by
    have : z ∈ S ∩ T := by rw [hinter]; simp
    exact this.2
  have hcapA0 := adjacent_cap_left (A := A) (B := B) z x y hz hmeet
    M.counterexample.1.2.2.2.2.2
  have hcapA : ∀ v : S, Even ((A.induce S).degree v) →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA0 v.val hvA
    · intro h
      exact hxS (h ▸ v.property)
    · intro h
      exact hyS (h ▸ v.property)
  have hzOddAS : Odd ((A.induce S).degree ⟨z, hzS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hzA
  have hdis : Disjoint (A.neighborFinset z) (B.neighborFinset z) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset z w).mp ha
    have hb' := (B.mem_neighborFinset z w).mp hb
    exact ha'.ne (hmeet w ⟨z, ha'.symm⟩ ⟨z, hb'.symm⟩).symm
  have hzdeg : (A ⊔ B).degree z = A.degree z + B.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hzOddB : Odd (B.degree z) := by
    rw [Nat.even_iff, hzdeg] at hz
    rw [Nat.odd_iff] at hzA ⊢
    omega
  have hzOddBT : Odd ((B.induce T).degree ⟨z, hzT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hzOddB
  obtain ⟨D0, hD0size, hzD0⟩ : ∃ D : Decomposition (A.induce S),
      D.size ≤ (Fintype.card S + 1) / 2 ∧ 0 < D.endpointCount ⟨z, hzS⟩ := by
    rcases floor_or_set (A.induce S) hconnS hcapA with ⟨D, hD⟩ | hset
    · exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree _ hzOddAS⟩
    · obtain ⟨D, hD, hzD⟩ := hset.endpoint_reserve ⟨z, hzS⟩
      exact ⟨D, hD, by omega⟩
  obtain ⟨D, hDsize, hDends⟩ := adjacent_lift_cut_piece S hA D0
  have hzD : 0 < D.endpointCount z := by
    rw [hDends ⟨z, hzS⟩]
    exact hzD0
  have hrightOut := M.of_vertex_smaller T (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩
    hsmall hright
  obtain ⟨Ex0, hEx0size, hxEx0⟩ := hrightOut.1
  obtain ⟨Ey0, hEy0size, hyEy0⟩ := hrightOut.2
  obtain ⟨Ex, hExsize, hExends⟩ := adjacent_lift_cut_piece T hB Ex0
  obtain ⟨Ey, hEysize, hEyends⟩ := adjacent_lift_cut_piece T hB Ey0
  have hxEx : 2 ≤ Ex.endpointCount x := by
    rw [hExends ⟨x, hxT⟩]
    exact hxEx0
  have hyEy : 2 ≤ Ey.endpointCount y := by
    rw [hEyends ⟨y, hyT⟩]
    exact hyEy0
  have hzEx : 0 < Ex.endpointCount z := by
    rw [hExends ⟨z, hzT⟩]
    exact Ex0.endpointCount_pos_of_odd_degree _ hzOddBT
  have hzEy : 0 < Ey.endpointCount z := by
    rw [hEyends ⟨z, hzT⟩]
    exact Ey0.endpointCount_pos_of_odd_degree _ hzOddBT
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  apply M.counterexample.2
  exact xie_adjacent_glue_left_endpoint_separate D Ex Ey z x y hxz hyz hzD hzEx hzEy
    hmeet (by omega) (by omega) hxEx hyEy

/-- Source-faithful edge-minimal consumption of the odd-local cut assembly.
The recursive right graph may live on a subtype; only its strict edge decrease
is used, so this theorem also applies after a later fresh-leaf construction. -/
theorem adjacent_odd_local_union_not_edge_minimal
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z x y : V) (M : AdjacentEdgeMinimalCounterexample (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hzS : z ∈ S) (hxS : x ∉ S) (hyS : y ∉ S)
    (hxT : x ∈ T) (hyT : y ∈ T)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hconnS : (A.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Odd (A.degree z))
    (hedge : (B.induce T).edgeFinset.card < (A ⊔ B).edgeFinset.card)
    (hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) : False := by
  apply adjacent_odd_local_union_false_of_right S T z x y M.counterexample.1
    M.counterexample.2 hA hB hzS hxS hyS hxT hyT hxz hyz hcover hinter hconnS hz hzA
  exact M.2 T (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using hedge) hright
  exact hmeet

/-- A same-right-decomposition specialization of the independent-output
gluing interface. -/
theorem xie_adjacent_glue_left_reserve
    (D : Decomposition A) (E : Decomposition B)
    (z x y : V) (hxz : x ≠ z) (hyz : y ≠ z)
    (hzD : 2 ≤ D.endpointCount z)
    (hinc : ∃ w, B.Adj z w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hbudget : D.size + E.size - 1 ≤ (Fintype.card V + 1) / 2)
    (hxE : 2 ≤ E.endpointCount x)
    (hyE : 2 ≤ E.endpointCount y) :
    AdjacentConclusion (A ⊔ B) x y :=
  xie_adjacent_glue_left_reserve_separate D E E z x y hxz hyz hzD hinc hmeet
    hbudget hbudget hxE hyE

/-- The full normalized even-local cut contradiction in Xie's Claim 1.  The
only inputs still supplied by the source-specific structural argument are the
literal one-vertex separation and the local evenness of the separator on the
left; all recursive calls, lifts, budget arithmetic, and independent-output
merges are discharged here. -/
theorem adjacent_even_local_union_false_of_right
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (H : AdjacentInstance (A ⊔ B) x y)
    (hfail : ¬ AdjacentConclusion (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hzS : z ∈ S) (haS : a ∈ S) (haz : a ≠ z)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∈ T) (hyT : y ∈ T)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hconnS : (A.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Even (A.degree z))
    (hinc : ∃ w, B.Adj z w)
    (hrightOut : AdjacentConclusion (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) : False := by
  obtain ⟨D0, hD0size, hzD0⟩ := adjacent_left_cut_endpoint_reserve
    (A := A) (B := B) S z a x y H hA hzS haS haz hxS hyS
      hconnS hz hzA hmeet
  obtain ⟨D, hDsize, hDends⟩ := adjacent_lift_cut_piece S hA D0
  have hzD : 2 ≤ D.endpointCount z := by
    rw [hDends ⟨z, hzS⟩]
    exact hzD0
  have hDsize' : D.size ≤ (Fintype.card S + 1) / 2 := by
    rw [hDsize]
    exact hD0size
  obtain ⟨Ex0, hEx0size, hxEx0⟩ := hrightOut.1
  obtain ⟨Ey0, hEy0size, hyEy0⟩ := hrightOut.2
  obtain ⟨Ex, hExsize, hExends⟩ := adjacent_lift_cut_piece T hB Ex0
  obtain ⟨Ey, hEysize, hEyends⟩ := adjacent_lift_cut_piece T hB Ey0
  have hxEx : 2 ≤ Ex.endpointCount x := by
    rw [hExends ⟨x, hxT⟩]
    exact hxEx0
  have hyEy : 2 ≤ Ey.endpointCount y := by
    rw [hEyends ⟨y, hyT⟩]
    exact hyEy0
  have hExsize' : Ex.size ≤ (Fintype.card T + 1) / 2 := by
    rw [hExsize]
    exact hEx0size
  have hEysize' : Ey.size ≤ (Fintype.card T + 1) / 2 := by
    rw [hEysize]
    exact hEy0size
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  apply hfail
  exact xie_adjacent_glue_left_reserve_separate D Ex Ey z x y hxz hyz hzD hinc
    hmeet (by omega) (by omega) hxEx hyEy

/-- The legacy lexicographic wrapper for the normalized even-local branch. -/
theorem adjacent_even_local_union_not_minimal
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (M : AdjacentMinimalCounterexample (A ⊔ B) x y)
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hzS : z ∈ S) (haS : a ∈ S) (haz : a ≠ z)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∈ T) (hyT : y ∈ T)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hconnS : (A.induce S).Connected)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Even (A.degree z))
    (hconnT : (B.induce T).Connected)
    (hsmall : Fintype.card T < Fintype.card V)
    (hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩)
    (hinc : ∃ w, B.Adj z w)
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z) : False := by
  obtain ⟨D0, hD0size, hzD0⟩ := adjacent_left_cut_endpoint_reserve
    (A := A) (B := B) S z a x y M.counterexample.1 hA hzS haS haz hxS hyS
      hconnS hz hzA hmeet
  obtain ⟨D, hDsize, hDends⟩ := adjacent_lift_cut_piece S hA D0
  have hzD : 2 ≤ D.endpointCount z := by
    rw [hDends ⟨z, hzS⟩]
    exact hzD0
  have hDsize' : D.size ≤ (Fintype.card S + 1) / 2 := by
    rw [hDsize]
    exact hD0size
  have hrightOut := M.of_vertex_smaller T (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩
    hsmall hright
  obtain ⟨Ex0, hEx0size, hxEx0⟩ := hrightOut.1
  obtain ⟨Ey0, hEy0size, hyEy0⟩ := hrightOut.2
  obtain ⟨Ex, hExsize, hExends⟩ := adjacent_lift_cut_piece T hB Ex0
  obtain ⟨Ey, hEysize, hEyends⟩ := adjacent_lift_cut_piece T hB Ey0
  have hxEx : 2 ≤ Ex.endpointCount x := by
    rw [hExends ⟨x, hxT⟩]
    exact hxEx0
  have hyEy : 2 ≤ Ey.endpointCount y := by
    rw [hEyends ⟨y, hyT⟩]
    exact hyEy0
  have hExsize' : Ex.size ≤ (Fintype.card T + 1) / 2 := by
    rw [hExsize]
    exact hEx0size
  have hEysize' : Ey.size ≤ (Fintype.card T + 1) / 2 := by
    rw [hEysize]
    exact hEy0size
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  apply M.counterexample.2
  exact xie_adjacent_glue_left_reserve_separate D Ex Ey z x y hxz hyz hzD hinc
    hmeet (by omega) (by omega) hxEx hyEy

/-- In an actual connected right cut piece, the separator has an incident
edge whenever the piece also contains a distinct hub. This removes the
otherwise manual merge-carrier witness from the source-level cut bundle. -/
theorem adjacent_right_separator_incident
    (T : Set V) [DecidablePred (· ∈ T)]
    (z x : V) (hB : B.support ⊆ T) (hzT : z ∈ T) (hxT : x ∈ T)
    (hxz : x ≠ z) (hconnT : (B.induce T).Connected) :
    ∃ w, B.Adj z w := by
  have hnt : Nontrivial T := ⟨⟨z, hzT⟩, ⟨x, hxT⟩,
    fun h => hxz (congrArg Subtype.val h).symm⟩
  have hp : 0 < (B.induce T).degree ⟨z, hzT⟩ :=
    hconnT.preconnected.degree_pos_of_nontrivial ⟨z, hzT⟩
  rw [SimpleGraph.degree_induce_of_support_subset hB] at hp
  exact (B.degree_pos_iff_exists_adj z).mp hp

/-- The actual even-local cut branch, with the partition data left explicit.
This is the bridge from a minimum counterexample on `G` to the normalized
one-vertex-union contradiction.  The only source-specific premise remaining
is the local evenness of the separator in its left cut piece. -/
theorem adjacent_actual_even_local_cut_not_minimal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (M : AdjacentMinimalCounterexample G x y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (haS : a ∈ S) (hxT : x ∈ T)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (haz : a ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : Even (G.degree z))
    (hzA : Even ((G.induce S).spanningCoe.degree z)) : False := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hzST : z ∈ S ∩ T := by
    rw [hinter]
    simp
  have hzS : z ∈ S := hzST.1
  have hzT : z ∈ T := hzST.2
  have hxS : x ∉ S := by
    intro hxS
    have : x ∈ S ∩ T := ⟨hxS, hxT⟩
    have : x = z := by
      simpa only [hinter, Set.mem_singleton_iff] using this
    exact hxz this
  obtain ⟨hyT, hyS, hright0⟩ :=
    adjacent_actual_right_cut_instance S T z x y M.counterexample.1 hxz hyz hxT
      hcover hinter hgraph hconnT hz
  have hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    simpa only [B] using hright0
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hq⟩
    rcases hBw with ⟨r, hr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hq⟩, hB ⟨r, hr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hsmall : Fintype.card T < Fintype.card V := by
    have hinter' : T ∩ S = {z} := by
      simpa only [Set.inter_comm] using hinter
    exact cut_piece_card_lt T S z a hinter' haS haz
  have hinc : ∃ w, B.Adj z w :=
    adjacent_right_separator_incident T z x hB hzT hxT hxz hconnB
  have hM : AdjacentMinimalCounterexample (A ⊔ B) x y :=
    AdjacentMinimalCounterexample.congr x y hAB.symm M
  have hzAB : Even ((A ⊔ B).degree z) :=
    adjacent_even_degree_congr z hAB.symm hz
  exact adjacent_even_local_union_not_minimal S T z a x y hM hA hB hzS haS haz
    hxS hyS hxT hyT hxz hyz hcover hinter hconnA hzAB (by simpa only [A] using hzA)
    hconnB hsmall hright hinc hmeet

/-- Source-faithful edge-minimal version of the actual even-local cut branch.
The recursive right adjacent theorem is obtained from the literal induced
cut piece through strict edge decrease, not the experimental vertex ordering. -/
theorem adjacent_actual_even_local_cut_not_edge_minimal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (haS : a ∈ S) (hxT : x ∈ T)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (haz : a ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : Even (G.degree z))
    (hzA : Even ((G.induce S).spanningCoe.degree z)) : False := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hzST : z ∈ S ∩ T := by rw [hinter]; simp
  have hzS : z ∈ S := hzST.1
  have hzT : z ∈ T := hzST.2
  have hxS : x ∉ S := by
    intro hxS
    have hxz' : x = z := by
      simpa only [hinter, Set.mem_singleton_iff] using (show x ∈ S ∩ T from ⟨hxS, hxT⟩)
    exact hxz hxz'
  obtain ⟨hyT, hyS, hright⟩ :=
    adjacent_actual_right_cut_instance S T z x y M.counterexample.1 hxz hyz hxT
      hcover hinter hgraph hconnT hz
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hq⟩
    rcases hBw with ⟨r, hr⟩
    simpa only [hinter, Set.mem_singleton_iff] using
      (show w ∈ S ∩ T from ⟨hA ⟨q, hq⟩, hB ⟨r, hr⟩⟩)
  have hsmall0 : (G.induce T).edgeFinset.card < G.edgeFinset.card := by
    exact cut_piece_edge_count_lt (G := G) T S z M.counterexample.1.1 hzS
      (fun w hwT hwS => by
        simpa only [hinter, Set.mem_singleton_iff] using
          (show w ∈ S ∩ T from ⟨hwS, hwT⟩))
      ((sup_comm _ _).trans hgraph) ⟨a, haS, haz⟩
  have hsmall : (B.induce T).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
    simpa only [A, B, SimpleGraph.induce_spanningCoe, SimpleGraph.edgeFinset,
      ← Set.ncard_eq_toFinset_card', hgraph] using hsmall0
  have hM : AdjacentEdgeMinimalCounterexample (A ⊔ B) x y :=
    AdjacentEdgeMinimalCounterexample.congr x y hAB.symm M
  have hrightOut : AdjacentConclusion (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩ :=
    hM.2 T (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩
      (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using hsmall) hright
  have hinc : ∃ w, B.Adj z w :=
    adjacent_right_separator_incident T z x hB hzT hxT hxz hconnB
  have hzAB : Even ((A ⊔ B).degree z) :=
    adjacent_even_degree_congr z hAB.symm hz
  exact adjacent_even_local_union_false_of_right S T z a x y hM.counterexample.1
    hM.counterexample.2 hA hB hzS haS haz hxS hyS hxT hyT hxz hyz hcover hinter
    hconnA hzAB (by simpa only [A] using hzA) hinc hrightOut hmeet

/-- The actual odd-local cut branch of Xie's Claim 1.  This wrapper keeps the
partition equalities explicit, transports the smaller right adjacent instance,
and feeds the two locally odd separator degrees into the normalized consumer. -/
theorem adjacent_actual_odd_local_cut_not_minimal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (M : AdjacentMinimalCounterexample G x y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (haS : a ∈ S) (hxT : x ∈ T)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (haz : a ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : Even (G.degree z))
    (hzA : Odd ((G.induce S).spanningCoe.degree z)) : False := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hzST : z ∈ S ∩ T := by
    rw [hinter]
    simp
  have hzS : z ∈ S := hzST.1
  have hzT : z ∈ T := hzST.2
  have hxS : x ∉ S := by
    intro hxS
    have : x ∈ S ∩ T := ⟨hxS, hxT⟩
    have : x = z := by
      simpa only [hinter, Set.mem_singleton_iff] using this
    exact hxz this
  obtain ⟨hyT, hyS, hright0⟩ :=
    adjacent_actual_right_cut_instance S T z x y M.counterexample.1 hxz hyz hxT
      hcover hinter hgraph hconnT hz
  have hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    simpa only [B] using hright0
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hq⟩
    rcases hBw with ⟨r, hr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hq⟩, hB ⟨r, hr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hsmall : Fintype.card T < Fintype.card V := by
    have hinter' : T ∩ S = {z} := by
      simpa only [Set.inter_comm] using hinter
    exact cut_piece_card_lt T S z a hinter' haS haz
  have hM : AdjacentMinimalCounterexample (A ⊔ B) x y :=
    AdjacentMinimalCounterexample.congr x y hAB.symm M
  have hzAB : Even ((A ⊔ B).degree z) :=
    adjacent_even_degree_congr z hAB.symm hz
  exact adjacent_odd_local_union_not_minimal S T z x y hM hA hB hzS hxS hyS hxT hyT
    hxz hyz hcover hinter hconnA hzAB (by simpa only [A] using hzA) hconnB hsmall
    hright hmeet

/-- Source-faithful edge-minimal version of the actual odd-local cut branch.
Unlike the earlier experimental wrapper, the right recursive call is justified
by the strict edge count of the induced cut piece, exactly as in Xie's proof. -/
theorem adjacent_actual_odd_local_cut_not_edge_minimal
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z a x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (haS : a ∈ S) (hxT : x ∈ T)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (haz : a ≠ z) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : Even (G.degree z))
    (hzA : Odd ((G.induce S).spanningCoe.degree z)) : False := by
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  letI : DecidableRel (A ⊔ B).Adj := SimpleGraph.Sup.adjDecidable V A B
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hzST : z ∈ S ∩ T := by
    rw [hinter]
    simp
  have hzS : z ∈ S := hzST.1
  have hzT : z ∈ T := hzST.2
  have hxS : x ∉ S := by
    intro hxS
    have : x ∈ S ∩ T := ⟨hxS, hxT⟩
    have : x = z := by
      simpa only [hinter, Set.mem_singleton_iff] using this
    exact hxz this
  obtain ⟨hyT, hyS, hright0⟩ :=
    adjacent_actual_right_cut_instance S T z x y M.counterexample.1 hxz hyz hxT
      hcover hinter hgraph hconnT hz
  have hright : AdjacentInstance (B.induce T) ⟨x, hxT⟩ ⟨y, hyT⟩ := by
    simpa only [B] using hright0
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hq⟩
    rcases hBw with ⟨r, hr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hq⟩, hB ⟨r, hr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hsmall0 : (G.induce T).edgeFinset.card < G.edgeFinset.card := by
    have hinter' : T ∩ S = {z} := by
      simpa only [Set.inter_comm] using hinter
    exact cut_piece_edge_count_lt (G := G) T S z M.counterexample.1.1 hzS
      (fun w hwT hwS => by
        have hw : w ∈ S ∩ T := ⟨hwS, hwT⟩
        simpa only [hinter, Set.mem_singleton_iff] using hw)
      ((sup_comm _ _).trans hgraph) ⟨a, haS, haz⟩
  have hsmall : (B.induce T).edgeFinset.card < (A ⊔ B).edgeFinset.card := by
    simpa only [A, B, SimpleGraph.induce_spanningCoe, SimpleGraph.edgeFinset,
      ← Set.ncard_eq_toFinset_card', hgraph] using hsmall0
  have hM : AdjacentEdgeMinimalCounterexample (A ⊔ B) x y :=
    AdjacentEdgeMinimalCounterexample.congr x y hAB.symm M
  have hzAB : Even ((A ⊔ B).degree z) :=
    adjacent_even_degree_congr z hAB.symm hz
  exact adjacent_odd_local_union_not_edge_minimal S T z x y hM hA hB hzS hxS hyS hxT hyT
    hxz hyz hcover hinter hconnA hzAB (by simpa only [A] using hzA) hsmall hright hmeet

/-- Xie's Claim 1 away from the two adjacent exceptions: an even vertex
distinct from `x,y` cannot be a cut vertex in an adjacent minimum
counterexample.  The actual cut pieces are constructed from reachability after
deleting the proposed separator; their left local parity selects one of the
two already checked reconstruction branches. -/
theorem adjacent_nonhub_even_vertex_noncut
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z x y : V) (M : AdjacentMinimalCounterexample G x y)
    (hz : Even (G.degree z)) (hxz : x ≠ z) (hyz : y ≠ z) :
    (G.induce {v | v ≠ z}).Connected := by
  classical
  by_contra hdisc
  obtain ⟨a, ha⟩ := exists_not_reachable_of_not_connected
    (G.induce {v | v ≠ z}) ⟨x, hxz⟩ hdisc
  have hsep : ¬ (G.induce {v | v ≠ z}).Reachable a ⟨x, hxz⟩ := by
    intro h
    exact ha h.symm
  obtain ⟨S, T, hcover, hinter, haS, hxT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G M.counterexample.1.1 z a.val x a.property hxz hsep
  by_cases hzA : Even ((G.induce S).spanningCoe.degree z)
  · exact adjacent_actual_even_local_cut_not_minimal S T z a.val x y M hcover hinter
      haS hxT hgraph hconnS hconnT a.property hxz hyz hz hzA
  · exact adjacent_actual_odd_local_cut_not_minimal S T z a.val x y M hcover hinter
      haS hxT hgraph hconnS hconnT a.property hxz hyz hz
      (Nat.not_even_iff_odd.mp hzA)

/-- Source-faithful non-hub part of Xie's Claim 1.  The proof uses the
edge-minimal resource throughout: an even nonexceptional vertex cannot
separate an adjacent two-exception counterexample. -/
theorem adjacent_nonhub_even_vertex_noncut_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z x y : V) (M : AdjacentEdgeMinimalCounterexample G x y)
    (hz : Even (G.degree z)) (hxz : x ≠ z) (hyz : y ≠ z) :
    (G.induce {v | v ≠ z}).Connected := by
  classical
  by_contra hdisc
  obtain ⟨a, ha⟩ := exists_not_reachable_of_not_connected
    (G.induce {v | v ≠ z}) ⟨x, hxz⟩ hdisc
  have hsep : ¬ (G.induce {v | v ≠ z}).Reachable a ⟨x, hxz⟩ := by
    intro h
    exact ha h.symm
  obtain ⟨S, T, hcover, hinter, haS, hxT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G M.counterexample.1.1 z a.val x a.property hxz hsep
  by_cases hzA : Even ((G.induce S).spanningCoe.degree z)
  · exact adjacent_actual_even_local_cut_not_edge_minimal S T z a.val x y M
      hcover hinter haS hxT hgraph hconnS hconnT a.property hxz hyz hz hzA
  · exact adjacent_actual_odd_local_cut_not_edge_minimal S T z a.val x y M
      hcover hinter haS hxT hgraph hconnS hconnT a.property hxz hyz hz
      (Nat.not_even_iff_odd.mp hzA)

end Gallai.TwoException
