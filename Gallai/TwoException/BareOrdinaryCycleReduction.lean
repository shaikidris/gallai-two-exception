/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryCycleBudget

@[expose] public section

/-! # Restoring a good ordinary cycle puncture -/

namespace Gallai.TwoException

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A good degree-two ordinary cycle puncture contradicts bare minimality:
the component budget restores both edges without spending h's reserve. -/
theorem bare_good_ordinary_cycle_puncture_false
    (h z x a b c : V) (H : BareMinimalCounterexample G h z)
    (hxa : G.Adj x a) (habAdj : G.Adj a b) (hbc : G.Adj b c)
    (hxb : x ≠ b) (hxc : x ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hxEven : Even (G.degree x)) (haEven : Even (G.degree a))
    (hbEven : Even (G.degree b)) (hcEven : Even (G.degree c))
    (hxDeg : eDegree G x = 2) (haDeg : eDegree G a = 2)
    (hbDeg : eDegree G b = 2) (hcDeg : eDegree G c = 2)
    (hhx : h ≠ x) (hha : h ≠ a) (hhb : h ≠ b) (hhc : h ≠ c)
    (hzx : z ≠ x) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hreach : (twoEdgeCyclePuncture (G := G) x a b c).Reachable h z) : False := by
  obtain ⟨D, hDsize, hDh⟩ := ordinary_cycle_good_puncture_conclusion
    h z x a b c H hxa hbc hxb hxc hab hac hxEven haEven hbEven hcEven
    hxDeg haDeg hbDeg hcDeg hhx hha hhb hhc hzx hza hzb hzc hreach
  obtain ⟨E, hEsize, hEpreserve⟩ :=
    Decomposition.restore_twoEdgeCyclePuncture_of_local_ledger
      x a b c hxa habAdj hbc hxb hxc hab hac hxEven haEven hbEven hcEven
      haDeg hbDeg D
  apply H.counterexample.2
  refine ⟨E, hEsize.le.trans hDsize, ?_⟩
  rw [hEpreserve h hhx hha hhb hhc]
  exact hDh

/-- No long simple cycle consisting of ordinary degree-two even vertices
can survive in a bare minimum counterexample. -/
theorem bare_no_long_ordinary_cycle
    (h z x : V) (H : BareMinimalCounterexample G h z)
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : 4 ≤ p.length)
    (heven : ∀ v ∈ p.support, Even (G.degree v))
    (hdeg : ∀ v ∈ p.support, eDegree G v = 2)
    (havoid : ∀ v ∈ p.support, v ≠ h ∧ v ≠ z) : False := by
  obtain ⟨a, b, c, d, hxa, hab, hbc, hcd, r, heq⟩ :=
    closed_walk_four_edge_decomposition p hlen
  subst p
  let w := SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
    (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))
  have hwlen : 4 ≤ w.length := by simpa [w] using hlen
  obtain ⟨hxb, hac, hbd⟩ := cycle_four_edge_segment_guards x a b c d hxa hab hbc hcd r hp
  have hxc : x ≠ c := by
    intro he
    have hv : w.getVert 3 = x := by simpa [w] using he.symm
    have hi := (hp.getVert_endpoint_iff (i := 3) (by change 3 ≤ w.length; omega)).mp hv
    change 3 = 0 ∨ 3 = w.length at hi
    omega
  have had : a ≠ d := by
    intro he
    have hv : w.getVert 1 = w.getVert 4 := by simpa [w] using he
    have hi := hp.getVert_injOn (by change 1 ≤ 1 ∧ 1 ≤ w.length; omega)
      (by change 1 ≤ 4 ∧ 4 ≤ w.length; omega) hv
    omega
  have hxS : x ∈ w.support := w.start_mem_support
  have haS : a ∈ w.support := by simp [w]
  have hbS : b ∈ w.support := by simp [w]
  have hcS : c ∈ w.support := by simp [w]
  have hdS : d ∈ w.support := by
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr r.start_mem_support)))
  have hg := bare_consecutive_cycle_puncture_good h z x a b c d H.counterexample
    H.counterexample.1.1 hxa hab hbc hcd r hp.isTrail hxb hac hbd hab.ne
    (heven a haS) (heven b hbS) (havoid a haS).1 (havoid a haS).2
    (havoid b hbS).1 (havoid b hbS).2
  rcases hg with hg | hg
  · exact bare_good_ordinary_cycle_puncture_false h z x a b c H hxa hab hbc
      hxb hxc hab.ne hac (heven x hxS) (heven a haS) (heven b hbS) (heven c hcS)
      (hdeg x hxS) (hdeg a haS) (hdeg b hbS) (hdeg c hcS)
      (havoid x hxS).1.symm (havoid a haS).1.symm
      (havoid b hbS).1.symm (havoid c hcS).1.symm
      (havoid x hxS).2.symm (havoid a haS).2.symm
      (havoid b hbS).2.symm (havoid c hcS).2.symm hg
  · exact bare_good_ordinary_cycle_puncture_false h z a b c d H hab hbc hcd
      hac had hbc.ne hbd (heven a haS) (heven b hbS) (heven c hcS) (heven d hdS)
      (hdeg a haS) (hdeg b hbS) (hdeg c hcS) (hdeg d hdS)
      (havoid a haS).1.symm (havoid b hbS).1.symm
      (havoid c hcS).1.symm (havoid d hdS).1.symm
      (havoid a haS).2.symm (havoid b hbS).2.symm
      (havoid c hcS).2.symm (havoid d hdS).2.symm hg

/-- An actual ordinary component of the induced even graph contains no
simple cycle of length at least four. All ambient guards are derived here. -/
theorem bare_ordinary_component_no_long_cycle
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent) (hz : z ∉ C.supp)
    (hw : w ∈ C.supp) (p : (evenSubgraph G).Walk w w)
    (hp : p.IsCycle) (hlen : 4 ≤ p.length) : False := by
  have hsupport : ∀ v ∈ p.support, v ∈ C.supp := by
    intro v hv
    have hr := arc_walk_support_reachable p p.start_mem_support hv
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).symm.trans hw
  have hpositive : ∀ v ∈ p.support, 0 < eDegree G (v : V) := by
    intro v hv
    rw [eDegree_eq_induced_degree]
    apply ((evenSubgraph G).degree_pos v).mpr
    intro hi
    exact hp.not_nil (p.nil_of_isIsolated_of_mem_support hi hv)
  have htwo : ∀ v ∈ p.support, eDegree G (v : V) = 2 := by
    intro v hv
    have hd := bare_ordinary_degree_zero_or_two z v h H C hz (hsupport v hv)
    have hpos := hpositive v hv
    omega
  let q := p.map (evenSubgraphInclusion G)
  have hq : q.IsCycle := hp.map Subtype.val_injective
  apply bare_no_long_ordinary_cycle h (z : V) (w : V) H q hq
    (by
      change 4 ≤ (p.map (evenSubgraphInclusion G)).length
      rw [SimpleGraph.Walk.length_map]
      exact hlen)
  · intro v hv
    change v ∈ (p.map (evenSubgraphInclusion G)).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact t.property
  · intro v hv
    change v ∈ (p.map (evenSubgraphInclusion G)).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact htwo t ht
  · intro v hv
    change v ∈ (p.map (evenSubgraphInclusion G)).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    constructor
    · intro he
      change (t : V) = h at he
      have hpos := hpositive t ht
      rw [he, H.counterexample.1.2.2.2.2.2.1] at hpos
      omega
    · intro he
      exact hz (by simpa only [show t = z from Subtype.ext he] using hsupport t ht)

end Gallai.TwoException
