/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryLocalPreparation
public import Gallai.TwoException.OrdinarySpecialSelection
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! # Exact assembly of ordinary deletion spokes -/
namespace Gallai.TwoException
open scoped Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance spokeAssemblyComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Spokes chosen inside different original components cannot overlap.
Their ambient union therefore has the exact preparation cardinality:
one per component, two extra per T3, and one extra per special T2. -/
theorem ordinary_selected_spokes_count
    (F T3 special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hT3 : T3 ⊆ F) (hspecial : special ⊆ F)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hcard : ∀ C ∈ F, #(P C) = 1 +
      2 * (if C ∈ T3 then 1 else 0) + (if C ∈ special then 1 else 0)) :
    #((F.biUnion P).image Subtype.val) = #F + 2 * #T3 + #special := by
  classical
  have hdis : (F : Set _).PairwiseDisjoint P := by
    intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro t htC htD
    exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (hsupp C hC t htC) (hsupp D hD t htD))
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_biUnion hdis]
  have hT : (∑ C ∈ F, if C ∈ T3 then (1 : ℕ) else 0) = #T3 := by
    rw [Finset.sum_boole]
    have heq : F.filter (fun C => C ∈ T3) = T3 := by
      ext C
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hT3 h, h⟩⟩
    simp [heq]
  have hS : (∑ C ∈ F, if C ∈ special then (1 : ℕ) else 0) = #special := by
    rw [Finset.sum_boole]
    have heq : F.filter (fun C => C ∈ special) = special := by
      ext C
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hspecial h, h⟩⟩
    simp [heq]
  calc
    (∑ C ∈ F, #(P C)) = ∑ C ∈ F,
        (1 + 2 * (if C ∈ T3 then 1 else 0) + (if C ∈ special then 1 else 0)) :=
      Finset.sum_congr rfl hcard
    _ = #F + 2 * #T3 + #special := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hT, hS]
      simp

/-- Choose the optional special T2 and simultaneously obtain the actual
assembled spoke count and the parity needed by every remaining regular
T2. Local regular and special preparations are consumed coherently. -/
theorem ordinary_parity_spoke_assembly
    (F T3 eligible : Finset (evenSubgraph G).ConnectedComponent) (hub : ℕ)
    (regular specialPacket : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hT3 : T3 ⊆ F) (heligible : eligible ⊆ F)
    (hnotT3 : ∀ C ∈ eligible, C ∉ T3)
    (hregularSupport : ∀ C ∈ F, ∀ t ∈ regular C, t ∈ C.supp)
    (hspecialSupport : ∀ C ∈ eligible, ∀ t ∈ specialPacket C, t ∈ C.supp)
    (hregularCard : ∀ C ∈ F, #(regular C) = 1 + 2 * (if C ∈ T3 then 1 else 0))
    (hspecialCard : ∀ C ∈ eligible, #(specialPacket C) = 2) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
      special ⊆ eligible ∧ #special ≤ 1 ∧
      let P := fun C => if C ∈ special then specialPacket C else regular C
      #((F.biUnion P).image Subtype.val) = #F + 2 * #T3 + #special ∧
      ((eligible \ special).Nonempty → Even (hub + #((F.biUnion P).image Subtype.val))) ∧
      #special ≤ (if Even (hub + #((F.biUnion P).image Subtype.val)) then 1 else 0) := by
  classical
  obtain ⟨special, hs, hsize, _, heven, hreserve⟩ :=
    select_special_ordinary_packet eligible (hub + #F + 2 * #T3)
  let P := fun C => if C ∈ special then specialPacket C else regular C
  have hsupport : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp := by
    intro C hC t ht
    by_cases hCs : C ∈ special
    · exact hspecialSupport C (hs hCs) t (by simpa [P, hCs] using ht)
    · exact hregularSupport C hC t (by simpa [P, hCs] using ht)
  have hcard : ∀ C ∈ F, #(P C) = 1 +
      2 * (if C ∈ T3 then 1 else 0) + (if C ∈ special then 1 else 0) := by
    intro C hC
    by_cases hCs : C ∈ special
    · have hn := hnotT3 C (hs hCs)
      simpa [P, hCs, hn] using hspecialCard C (hs hCs)
    · simpa [P, hCs] using hregularCard C hC
  have hcount := ordinary_selected_spokes_count G F T3 special P hT3
    (hs.trans heligible) hsupport hcard
  refine ⟨special, hs, hsize, hcount, ?_, ?_⟩
  · intro hremaining
    have he := heven hremaining
    change Even (hub + #((F.biUnion P).image Subtype.val))
    rw [hcount]
    simpa [Nat.add_assoc] using he
  · change #special ≤ (if Even (hub + #((F.biUnion P).image Subtype.val)) then 1 else 0)
    rw [hcount]
    simpa [Nat.add_assoc] using hreserve

end Gallai.TwoException
