/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryDegreeThree
public import Gallai.TwoException.BareWindmill
public import Gallai.TwoException.BareOrdinaryCycle

@[expose] public section

/-! # Protected component of an ordinary cycle puncture -/

namespace Gallai.TwoException

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The component retaining both designated vertices is a native smaller
bare instance. The cycle deletion flips only its four ordinary vertices. -/
theorem ordinary_cycle_puncture_protected_instance
    (h z x a b c : V) (H : BareCounterexample G h z)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hhB : h ∈ B.supp) (hzB : z ∈ B.supp) :
    BareInstance ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp)
      ⟨h, hhB⟩ ⟨z, hzB⟩ := by
  classical
  let P := twoEdgeCyclePuncture (G := G) x a b c
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.1
  have hhd : P.degree h = G.degree h :=
    twoEdgeCyclePuncture_degree_away x a b c h hhx hha hhb hhc
  have hzd : P.degree z = G.degree z :=
    twoEdgeCyclePuncture_degree_away x a b c z hzx hza hzb hzc
  have hkeep : ∀ v, Even (P.degree v) → Even (G.degree v) :=
    twoEdgeCyclePuncture_even_preserved x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  have hmono : ∀ v, eDegree P v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation (twoEdgeCyclePuncture_le x a b c) hkeep
  have hclosed : ∀ v ∈ B.supp, P.neighborSet v ⊆ B.supp := by
    intro v hv w hvw
    exact B.mem_supp_of_adj_mem_supp hv hvw
  have hdeg : ∀ v : B.supp, (P.induce B.supp).degree v = P.degree v.val := by
    intro v
    exact SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v.val v.property)
  refine ⟨B.connected_toSimpleGraph, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hhz (congrArg Subtype.val heq)
  · rw [hdeg, hhd]; exact hhpos
  · rw [hdeg, hhd]; exact hheven
  · rw [hdeg, hzd]; exact hzeven
  · rw [eDegree_induce_of_closed P B.supp hclosed]
    have hb := hmono h
    rw [hhbare] at hb
    exact Nat.le_zero.mp hb
  · intro v hv hvh hvz
    have hvP : Even (P.degree v.val) := by rwa [hdeg] at hv
    rw [eDegree_induce_of_closed P B.supp hclosed]
    exact (hmono v.val).trans (hcap v.val (hkeep v.val hvP)
      (fun heq => hvh (Subtype.ext heq)) (fun heq => hvz (Subtype.ext heq)))

/-- A proper protected component receives its ceiling and prescribed
endpoint reserve by strict vertex minimality. -/
theorem ordinary_cycle_puncture_protected_conclusion
    (h z x a b c : V) (H : BareMinimalCounterexample G h z)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hhB : h ∈ B.supp) (hzB : z ∈ B.supp) (v : V) (hv : v ∉ B.supp) :
    BareConclusion ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp)
      ⟨h, hhB⟩ := by
  classical
  exact H.of_vertex_smaller B.supp _ ⟨h, hhB⟩ ⟨z, hzB⟩
    (Fintype.card_subtype_lt hv)
    (ordinary_cycle_puncture_protected_instance h z x a b c H.counterexample
      hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      hhx hha hhb hhc hzx hza hzb hzc B hhB hzB)

/-- The literal puncture is strictly edge-smaller: its first boundary edge
was present and is now absent. -/
theorem ordinary_cycle_puncture_edge_count_lt
    (x a b c : V) (hxa : G.Adj x a) :
    (twoEdgeCyclePuncture (G := G) x a b c).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨SimpleGraph.edgeFinset_mono (twoEdgeCyclePuncture_le x a b c), ?_⟩
  intro heq
  have he : s(x, a) ∈ G.edgeFinset := by simpa using hxa
  rw [← heq] at he
  have hp : (twoEdgeCyclePuncture (G := G) x a b c).Adj x a := by simpa using he
  have hn := (SimpleGraph.deleteEdges_adj.mp (SimpleGraph.deleteEdges_adj.mp hp).1).2
  exact hn rfl

/-- If the puncture remains connected, its unchanged designated vertices
and monotone even degrees make the whole puncture a bare instance. -/
theorem ordinary_cycle_puncture_connected_instance
    (h z x a b c : V) (H : BareCounterexample G h z)
    (hP : (twoEdgeCyclePuncture (G := G) x a b c).Connected)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    BareInstance (twoEdgeCyclePuncture (G := G) x a b c) h z := by
  let P := twoEdgeCyclePuncture (G := G) x a b c
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.1
  have hhd : P.degree h = G.degree h :=
    twoEdgeCyclePuncture_degree_away x a b c h hhx hha hhb hhc
  have hzd : P.degree z = G.degree z :=
    twoEdgeCyclePuncture_degree_away x a b c z hzx hza hzb hzc
  have hkeep : ∀ v, Even (P.degree v) → Even (G.degree v) :=
    twoEdgeCyclePuncture_even_preserved x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven
  have hmono : ∀ v, eDegree P v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation (twoEdgeCyclePuncture_le x a b c) hkeep
  refine ⟨hP, hhz, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hhd]
  · rwa [hhd]
  · rwa [hzd]
  · have hb := hmono h
    rw [hhbare] at hb
    exact Nat.le_zero.mp hb
  · intro v hv hvh hvz
    exact (hmono v).trans (hcap v (hkeep v hv) hvh hvz)

/-- Strict edge minimality supplies the ceiling and h's reserve for the
connected ordinary-cycle puncture. -/
theorem ordinary_cycle_puncture_connected_conclusion
    (h z x a b c : V) (H : BareMinimalCounterexample G h z)
    (hP : (twoEdgeCyclePuncture (G := G) x a b c).Connected)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    BareConclusion (twoEdgeCyclePuncture (G := G) x a b c) h := by
  exact H.of_edge_smaller V _ h z rfl
    (ordinary_cycle_puncture_edge_count_lt x a b c hxa)
    (ordinary_cycle_puncture_connected_instance h z x a b c H.counterexample hP
      hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      hhx hha hhb hhc hzx hza hzb hzc)

/-- Every component of the actual two-edge puncture meets one of its four
boundary vertices, since the original graph is connected. -/
theorem ordinary_cycle_puncture_component_contact
    (hconn : G.Connected) (x a b c : V) (hxa : G.Adj x a)
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent) :
    ∃ v ∈ B.supp, v = x ∨ v = a ∨ v = b ∨ v = c := by
  have hlt : twoEdgeCyclePuncture (G := G) x a b c < G := by
    refine lt_of_le_of_ne (twoEdgeCyclePuncture_le x a b c) ?_
    intro heq
    have hp : (twoEdgeCyclePuncture (G := G) x a b c).Adj x a := by
      rw [heq]; exact hxa
    exact (SimpleGraph.deleteEdges_adj.mp (SimpleGraph.deleteEdges_adj.mp hp).1).2 rfl
  obtain ⟨v, hv, w, hvw, hn⟩ := puncture_closed_boundary_nonempty hconn hlt
    B.supp B.nonempty_supp (fun u hu v huv => B.mem_supp_of_adj_mem_supp hu huv)
  refine ⟨v, hv, ?_⟩
  by_cases hfirst : s(v, w) = s(x, a)
  · rcases Sym2.eq_iff.mp hfirst with ⟨hvx, _⟩ | ⟨hva, _⟩
    · exact Or.inl hvx
    · exact Or.inr (Or.inl hva)
  have hsecond : s(v, w) = s(b, c) := by
    by_contra hsecond
    apply hn
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨SimpleGraph.deleteEdges_adj.mpr ⟨hvw, hfirst⟩, hsecond⟩
  rcases Sym2.eq_iff.mp hsecond with ⟨hvb, _⟩ | ⟨hvc, _⟩
  · exact Or.inr (Or.inr (Or.inl hvb))
  · exact Or.inr (Or.inr (Or.inr hvc))

/-- A puncture component excluding z has subcubic induced E-degree. -/
theorem ordinary_cycle_puncture_component_cap
    (h z x a b c : V) (H : BareCounterexample G h z)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hz : z ∉ B.supp) :
    ∀ v, Even (((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp).degree v) →
      eDegree ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp) v ≤ 3 := by
  classical
  let P := twoEdgeCyclePuncture (G := G) x a b c
  have hkeep := twoEdgeCyclePuncture_even_preserved x a b c hxa hbc
    hxb hxc hab hac hxEven haEven hbEven hcEven
  have hmono : ∀ v, eDegree P v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation (twoEdgeCyclePuncture_le x a b c) hkeep
  have hclosed : ∀ v ∈ B.supp, P.neighborSet v ⊆ B.supp := by
    intro v hv w hvw
    exact B.mem_supp_of_adj_mem_supp hv hvw
  intro v he
  have heP : Even (P.degree v.val) := by
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v.val v.property)] at he
  rw [eDegree_induce_of_closed P B.supp hclosed]
  apply (hmono v.val).trans
  by_cases hvh : v.val = h
  · rw [hvh, H.1.2.2.2.2.2.1]; omega
  · exact H.1.2.2.2.2.2.2 v.val (hkeep v.val heP) hvh
      (fun heq => hz (heq ▸ v.property))

/-- Every nonprotected component of an ordinary cycle puncture gets the
published floor budget: its actual boundary contact rules out SET. -/
theorem ordinary_cycle_puncture_component_floor
    (h z x a b c : V) (H : BareCounterexample G h z)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hxDeg : eDegree G x = 2) (haDeg : eDegree G a = 2)
    (hbDeg : eDegree G b = 2) (hcDeg : eDegree G c = 2)
    (B : (twoEdgeCyclePuncture (G := G) x a b c).ConnectedComponent)
    (hz : z ∉ B.supp) :
    HasPathBudget ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp)
      (Fintype.card B.supp / 2) := by
  classical
  rcases floor_or_set ((twoEdgeCyclePuncture (G := G) x a b c).induce B.supp)
      B.connected_toSimpleGraph
      (ordinary_cycle_puncture_component_cap h z x a b c H hxa hbc hxb hxc hab hac
        hxEven haEven hbEven hcEven B hz) with hf | hs
  · exact hf
  · exact (ordinary_cycle_contact_component_not_set x a b c hxa hbc hxb hxc hab hac
      hxEven haEven hbEven hcEven hxDeg haDeg hbDeg hcDeg B
      (ordinary_cycle_puncture_component_contact H.1.1 x a b c hxa B) hs).elim

/-- A good ordinary-cycle puncture has the full bare endpoint budget:
the protected component pays a ceiling and every other component a floor. -/
theorem ordinary_cycle_good_puncture_conclusion
    (h z x a b c : V) (H : BareMinimalCounterexample G h z)
    (hxa : G.Adj x a) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hxDeg : eDegree G x = 2) (haDeg : eDegree G a = 2)
    (hbDeg : eDegree G b = 2) (hcDeg : eDegree G c = 2)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hreach : (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z) :
    BareConclusion (twoEdgeCyclePuncture (G := G) x a b c) h := by
  classical
  let P := twoEdgeCyclePuncture (G := G) x a b c
  by_cases hP : P.Connected
  · exact ordinary_cycle_puncture_connected_conclusion h z x a b c H hP
      hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      hhx hha hhb hhc hzx hza hzb hzc
  let B₀ := P.connectedComponentMk h
  have hh₀ : h ∈ B₀.supp := rfl
  have hz₀ : z ∈ B₀.supp := SimpleGraph.ConnectedComponent.eq.mpr hreach.symm
  have hex : ∃ v, ¬ P.Reachable h v := by
    by_contra hn
    push_neg at hn
    exact hP (P.connected_iff_exists_forall_reachable.mpr ⟨h, hn⟩)
  obtain ⟨v, hv⟩ := hex
  have hv₀ : v ∉ B₀.supp := fun hm => hv (B₀.reachable_of_mem_supp hh₀ hm)
  obtain ⟨D, hD, hhD⟩ := ordinary_cycle_puncture_protected_conclusion h z x a b c H
    hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
    hhx hha hhb hhc hzx hza hzb hzc B₀ hh₀ hz₀ v hv₀
  have hf : ∀ B : P.ConnectedComponent, B ≠ B₀ →
      HasPathBudget (P.induce B.supp) (Fintype.card B.supp / 2) := by
    intro B hB
    have hzB : z ∉ B.supp := by
      intro hm
      apply hB
      change P.connectedComponentMk z = B at hm
      change P.connectedComponentMk z = B₀ at hz₀
      exact hm.symm.trans hz₀
    exact ordinary_cycle_puncture_component_floor h z x a b c H.counterexample
      hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      hxDeg haDeg hbDeg hcDeg B hzB
  exact assemble_one_ceiling P h D hD hhD hf

end Gallai.TwoException
