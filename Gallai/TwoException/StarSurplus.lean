/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OutwardStar
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-!
# Star restoration with endpoint surplus

The inherited outward-star lemma restores a missing star when every leaf has
at most `l` passing neighbours and the hub has `l` endpoints beyond the
number of pending edges. This file records the surplus-two and protected
surplus-one forms used by the two-exception proof.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- Passing neighbours of `v` in a decomposition of the current graph. -/
def passingNeighborCount (D : Decomposition G) (v : V) : ℕ :=
  #{t ∈ G.neighborFinset v | D.endpointCount t = 0}

/-- If the current graph preserves original degree parity away from a hub,
then a passing neighbour of a pending spoke is an original even neighbour
other than that hub. This is the count interface used for star-only punctures. -/
theorem passing_neighbor_count_le_two_of_star_parity
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (D : Decomposition J) (c w : V)
    (hsub : J ≤ G)
    (hparity : ∀ v, v ≠ c → J.degree v % 2 = G.degree v % 2)
    (hmissing : ¬ J.Adj w c)
    (hc : c ∈ evenNeighbors G w)
    (hcap : eDegree G w ≤ 3) :
    #{v ∈ J.neighborFinset w | D.endpointCount v = 0} ≤ 2 := by
  classical
  let P := {v ∈ J.neighborFinset w | D.endpointCount v = 0}
  have hsubset : P ⊆ evenNeighbors G w := by
    intro v hv
    obtain ⟨hvAdj, hzero⟩ := Finset.mem_filter.mp hv
    have hJEven : Even (J.degree v) := by
      rw [Nat.even_iff]
      have hmod := D.endpointCount_mod_two v
      rw [hzero] at hmod
      omega
    have hvc : v ≠ c := by
      intro h
      subst v
      exact hmissing ((J.mem_neighborFinset w c).mp hvAdj)
    have hGEven : Even (G.degree v) := by
      apply Nat.even_iff.mpr
      rw [← hparity v hvc]
      exact Nat.even_iff.mp hJEven
    exact (mem_evenNeighbors (G := G) w v).mpr
      ⟨hsub ((J.mem_neighborFinset w v).mp hvAdj), hGEven⟩
  have hcnot : c ∉ P := by
    intro h
    exact hmissing ((J.mem_neighborFinset w c).mp (Finset.mem_filter.mp h).1)
  have hne : P ≠ evenNeighbors G w := by
    intro heq
    exact hcnot (heq ▸ hc)
  have hlt : #P < eDegree G w := by
    rw [eDegree]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
  change #P ≤ 2
  omega

/-- The same pending-spoke bound when the pending leaf itself has changed
parity.  A passing neighbour of `w` cannot be `w` by loop-freeness, so parity
only has to be preserved away from the centre and that one missing leaf. -/
theorem passing_neighbor_count_le_two_of_star_parity_except_leaf
    {J : SimpleGraph V} [DecidableRel J.Adj]
    (D : Decomposition J) (c w : V)
    (hsub : J ≤ G)
    (hparity : ∀ v, v ≠ c → v ≠ w → J.degree v % 2 = G.degree v % 2)
    (hmissing : ¬ J.Adj w c)
    (hc : c ∈ evenNeighbors G w)
    (hcap : eDegree G w ≤ 3) :
    #{v ∈ J.neighborFinset w | D.endpointCount v = 0} ≤ 2 := by
  classical
  let P := {v ∈ J.neighborFinset w | D.endpointCount v = 0}
  have hsubset : P ⊆ evenNeighbors G w := by
    intro v hv
    obtain ⟨hvAdj, hzero⟩ := Finset.mem_filter.mp hv
    have hJEven : Even (J.degree v) := by
      rw [Nat.even_iff]
      have hmod := D.endpointCount_mod_two v
      rw [hzero] at hmod
      omega
    have hvc : v ≠ c := by
      intro h
      subst v
      exact hmissing ((J.mem_neighborFinset w c).mp hvAdj)
    have hvw : v ≠ w := by
      intro h
      subst v
      exact J.irrefl ((J.mem_neighborFinset w w).mp hvAdj)
    have hGEven : Even (G.degree v) := by
      apply Nat.even_iff.mpr
      rw [← hparity v hvc hvw]
      exact Nat.even_iff.mp hJEven
    exact (mem_evenNeighbors (G := G) w v).mpr
      ⟨hsub ((J.mem_neighborFinset w v).mp hvAdj), hGEven⟩
  have hcnot : c ∉ P := by
    intro h
    exact hmissing ((J.mem_neighborFinset w c).mp (Finset.mem_filter.mp h).1)
  have hne : P ≠ evenNeighbors G w := by
    intro heq
    exact hcnot (heq ▸ hc)
  have hlt : #P < eDegree G w := by
    rw [eDegree]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
  change #P ≤ 2
  omega

private theorem star_neighborFinset_eq_empty (c t : V) (S : Finset V)
    (htc : t ≠ c) (htS : t ∉ S) :
    ∀ v, ¬ (S.sup (SimpleGraph.edge c)).Adj t v := by
  classical
  intro v hadj
  induction S using Finset.induction_on with
  | empty => simp at hadj
  | @insert x S hx ih =>
      have htS' : t ∉ S := fun h => htS (Finset.mem_insert_of_mem h)
      have htx : t ≠ x := fun h => htS (h ▸ Finset.mem_insert_self x S)
      rw [Finset.sup_insert, SimpleGraph.sup_adj] at hadj
      rcases hadj with hnew | hold
      · simp [SimpleGraph.edge_adj, htc, htx] at hnew
      · exact ih htS' hold

/-- Adding a star away from `t` cannot create new passing neighbours at `t`
when the hub remains positive and leaves only gain endpoints. -/
private theorem zero_neighbor_count_mono_after_star (D : Decomposition G)
    (c : V) (S N : Finset V) (endpointE : V → ℕ)
    (hbalance : ∀ v, endpointE v + (if c = v then #S else 0) =
      D.endpointCount v + if v ∈ S then 1 else 0)
    (hpositive : 0 < endpointE c) :
    #{v ∈ N | endpointE v = 0} ≤ #{v ∈ N | D.endpointCount v = 0} := by
  classical
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvt, hzero⟩ := Finset.mem_filter.mp hv
  have hvc : c ≠ v := by
    intro h
    subst v
    exact (Nat.ne_of_gt hpositive) hzero
  have hnotS : v ∉ S := by
    intro hvS
    have hb := hbalance v
    simp only [hvc, if_false, Nat.add_zero, hvS, if_true] at hb
    omega
  have hb := hbalance v
  simp only [hvc, if_false, Nat.add_zero, hnotS, if_false, Nat.add_zero] at hb
  exact Finset.mem_filter.mpr ⟨hvt, by omega⟩

/-- Restore a missing star when every pending leaf has at most two passing
neighbours and the hub has two endpoints of surplus. -/
theorem restore_star_surplus_two (D : Decomposition G) (c : V) (S : Finset V)
    (hcS : c ∉ S) (hmissing : ∀ w ∈ S, ¬ G.Adj c w)
    (hpassing : ∀ w ∈ S, passingNeighborCount D w ≤ 2)
    (hreserve : #S + 2 ≤ D.endpointCount c) :
    ∃ E : Decomposition (G ⊔ S.sup (SimpleGraph.edge c)), E.size = D.size ∧
      ∀ v, E.endpointCount v + (if c = v then #S else 0) =
        D.endpointCount v + if v ∈ S then 1 else 0 := by
  have hpass : ∀ w ∈ S,
      #{v ∈ G.neighborFinset w | D.endpointCount v = 0} ≤ 2 := hpassing
  exact D.outward_star_addibility c S 2 hcS hmissing hpass (by omega)

/-- With no pending spoke, the current decomposition is already the desired
restoration; no endpoint surplus is needed. -/
theorem restore_star_empty (D : Decomposition G) (c : V) :
    ∃ E : Decomposition (G ⊔ (∅ : Finset V).sup (SimpleGraph.edge c)),
      E.size = D.size ∧ ∀ v, E.endpointCount v = D.endpointCount v := by
  classical
  have hstar : (∅ : Finset V).sup (SimpleGraph.edge c) = ⊥ := by
    ext u v
    simp
  have hgraph : G ⊔ (∅ : Finset V).sup (SimpleGraph.edge c) = G := by
    rw [hstar, sup_bot_eq]
  rw [hgraph]
  exact ⟨D, rfl, fun _ => rfl⟩

/-- Restore a missing star with one endpoint of surplus when one selected
pending leaf has at most one passing neighbour; the other leaves may have two. -/
theorem restore_star_surplus_one (D : Decomposition G) (c : V) (S : Finset V)
    (hcS : c ∉ S) (hmissing : ∀ w ∈ S, ¬ G.Adj c w)
    (hpassing : ∀ w ∈ S, passingNeighborCount D w ≤ 2)
    (w₀ : V) (hw₀ : w₀ ∈ S) (hsmall : passingNeighborCount D w₀ ≤ 1)
    (hreserve : #S + 1 ≤ D.endpointCount c) :
    ∃ E : Decomposition (G ⊔ S.sup (SimpleGraph.edge c)), E.size = D.size ∧
      ∀ v, E.endpointCount v + (if c = v then #S else 0) =
        D.endpointCount v + if v ∈ S then 1 else 0 := by
  let S' := S.erase w₀
  letI : DecidableRel (S'.sup (SimpleGraph.edge c)).Adj := Classical.decRel _
  letI : DecidableRel (G ⊔ S'.sup (SimpleGraph.edge c)).Adj :=
    SimpleGraph.Sup.adjDecidable V G (S'.sup (SimpleGraph.edge c))
  letI : Fintype ((G ⊔ S'.sup (SimpleGraph.edge c)).neighborSet w₀) := Subtype.fintype _
  letI : Fintype ((S'.sup (SimpleGraph.edge c)).neighborSet w₀) := Subtype.fintype _
  have hw₀c : w₀ ≠ c := fun h => hcS (h ▸ hw₀)
  have hS' : S' ⊆ S := Finset.erase_subset w₀ S
  have hw₀S' : w₀ ∉ S' := by simp [S']
  have hcS' : c ∉ S' := fun h => hcS (hS' h)
  have hcard : #S = #S' + 1 := by
    simp [S', Finset.card_erase_add_one hw₀]
  have hreserve' : #S' + 2 ≤ D.endpointCount c := by omega
  have hmissing' : ∀ w ∈ S', ¬ G.Adj c w := fun w hw => hmissing w (hS' hw)
  have hpassing' : ∀ w ∈ S', passingNeighborCount D w ≤ 2 :=
    fun w hw => hpassing w (hS' hw)
  obtain ⟨E₁, hsize₁, hbalance₁⟩ :=
    D.outward_star_addibility c S' 2 hcS' hmissing' hpassing' (by omega)
  have hcenter₁ : 2 ≤ E₁.endpointCount c := by
    have hbal : E₁.endpointCount c + #S' = D.endpointCount c := by
      simpa [hcS'] using hbalance₁ c
    omega
  have hstarN : (S'.sup (SimpleGraph.edge c)).neighborFinset w₀ = ∅ := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset]
    constructor
    · intro h
      exact False.elim ((star_neighborFinset_eq_empty c w₀ S' hw₀c hw₀S' v) h)
    · intro h
      exact False.elim (Finset.notMem_empty v h)
  have hpassBase : #{v ∈ G.neighborFinset w₀ | E₁.endpointCount v = 0} ≤
      passingNeighborCount D w₀ := by
    exact zero_neighbor_count_mono_after_star D c S' (G.neighborFinset w₀)
      E₁.endpointCount hbalance₁ (by omega)
  have hpass₁ : #{v ∈ (G ⊔ S'.sup (SimpleGraph.edge c)).neighborFinset w₀ |
      E₁.endpointCount v = 0} ≤ 1 := by
    rw [SimpleGraph.neighborFinset_sup]
    simp only [hstarN, Finset.union_empty]
    exact hpassBase.trans hsmall
  have hmissing₁ : ¬ (G ⊔ S'.sup (SimpleGraph.edge c)).Adj w₀ c := by
    intro h
    rcases (SimpleGraph.sup_adj _ _ _ _).mp h with hG | hS
    · exact hmissing w₀ hw₀ hG.symm
    · exact (star_neighborFinset_eq_empty c w₀ S' hw₀c hw₀S' c hS).elim
  have hstrict : #{v ∈ (G ⊔ S'.sup (SimpleGraph.edge c)).neighborFinset w₀ |
      E₁.endpointCount v = 0} < E₁.endpointCount c := by omega
  obtain ⟨E₂, hsize₂, hbalance₂⟩ :=
    E₁.single_edge_addibility w₀ c hw₀c hmissing₁ hstrict
  have hstar : S'.sup (SimpleGraph.edge c) ⊔ SimpleGraph.edge w₀ c =
      (insert w₀ S').sup (SimpleGraph.edge c) := by
    rw [Finset.sup_insert, SimpleGraph.edge_comm w₀ c, sup_comm]
  have hgraph : (G ⊔ S'.sup (SimpleGraph.edge c)) ⊔ SimpleGraph.edge w₀ c =
      G ⊔ (insert w₀ S').sup (SimpleGraph.edge c) := by
    rw [sup_assoc, hstar]
  have hSrepr : insert w₀ S' = S := by
    classical
    ext w
    simp [S', hw₀]
  rw [hSrepr] at hgraph
  rw [← hgraph]
  refine ⟨E₂, hsize₂.trans hsize₁, ?_⟩
  intro v
  have h₁ := hbalance₁ v
  have h₂ := hbalance₂ v
  by_cases hcv : c = v
  · subst v
    simp [hw₀c, hcS', hw₀S', hcS] at h₁ h₂ ⊢
    omega
  · by_cases hwv : w₀ = v
    · subst v
      simp [hcv, hw₀S', hcS', hw₀] at h₁ h₂ ⊢
      omega
    · simp only [hcv, hwv, Ne.symm hwv, if_false, Nat.add_zero] at h₁ h₂ ⊢
      have hvS : v ∈ S' ↔ v ∈ S := by simp [S', Ne.symm hwv]
      simp only [hvS] at h₁ ⊢
      omega

/-- If the one-surplus restoration profile is unavailable, the hub has
exactly one endpoint beyond the pending star and every pending leaf has two
passing neighbours. -/
theorem star_surplus_failure_profile (D : Decomposition G) (c : V) (S : Finset V)
    (hcS : c ∉ S) (hmissing : ∀ w ∈ S, ¬ G.Adj c w)
    (hpassing : ∀ w ∈ S, passingNeighborCount D w ≤ 2)
    (hreserve : #S + 1 ≤ D.endpointCount c)
    (hfail : ¬ ∃ E : Decomposition (G ⊔ S.sup (SimpleGraph.edge c)),
      E.size = D.size ∧
        ∀ v, E.endpointCount v + (if c = v then #S else 0) =
          D.endpointCount v + if v ∈ S then 1 else 0) :
    D.endpointCount c = #S + 1 ∧ ∀ w ∈ S, passingNeighborCount D w = 2 := by
  constructor
  · by_contra h
    have htwo : #S + 2 ≤ D.endpointCount c := by omega
    obtain ⟨E, hs, hb⟩ := restore_star_surplus_two D c S hcS hmissing hpassing htwo
    exact hfail ⟨E, hs, hb⟩
  · intro w hw
    have hnotSmall : ¬ passingNeighborCount D w ≤ 1 := by
      intro hsmall
      obtain ⟨E, hs, hb⟩ := restore_star_surplus_one D c S hcS hmissing
        hpassing w hw hsmall hreserve
      exact hfail ⟨E, hs, hb⟩
    have hge : 2 ≤ passingNeighborCount D w := by omega
    exact Nat.le_antisymm (hpassing w hw) hge

end Gallai.TwoException
