/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyMixedFamily

@[expose] public section

/-! # Parity of the actual mixed early deletion star -/
namespace Gallai.TwoException
open scoped Finset

/-- If an eligible T2 exists, the at-most-one selector yields even total
parity even when selecting it leaves no regular T2 behind. -/
theorem special_selection_even_of_nonempty
    {I : Type*} [DecidableEq I] (eligible special : Finset I) (k : ℕ)
    (hsize : #special ≤ 1)
    (hempty : Even k → special = ∅)
    (hpar : (eligible \ special).Nonempty → Even (k + #special))
    (he : eligible.Nonempty) : Even (k + #special) := by
  classical
  by_cases hk : Even k
  · simpa [hempty hk] using hk
  · by_cases hs : special = ∅
    · apply hpar
      simpa [hs] using he
    · have hc : #special = 1 := by
        have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        omega
      have ho : Odd k := (Nat.even_or_odd k).resolve_left hk
      rw [hc,Nat.even_iff]
      rw [Nat.odd_iff] at ho
      omega

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance parityFamilyComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- The selector parity applies to the literal combined private and
ordinary contact star, using the exact merged-family count. The odd
baseline requires an available T2; that branch condition is explicit. -/
theorem early_actual_mixed_star_even
    (S : Finset (evenVertices G))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (K : Finset V)
    (hdis : Disjoint K ((F.biUnion Q).image Subtype.val))
    (hsub : special ⊆ F)
    (hsupp : ∀ C ∈ F, ∀ t ∈ Q C, t ∈ C.supp)
    (hregular : ∀ C ∈ F, C ∉ special →
      #(Q C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0))
    (hspecial : ∀ C ∈ special,
      #(ordinaryComponentPacket G S C) = 2 ∧ #(Q C) = 2)
    (hsize : #special ≤ 1)
    (hempty : Even (#K + #F +
      2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3))) → special = ∅)
    (hpar : ((F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)) \ special).Nonempty →
      Even (#K + #F + 2 * #(F.filter
        (fun C => #(ordinaryComponentPacket G S C) = 3)) + #special))
    (havailable : Even (#K + #F + 2 * #(F.filter
      (fun C => #(ordinaryComponentPacket G S C) = 3))) ∨
      (F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)).Nonempty) :
    Even #(K ∪ (F.biUnion Q).image Subtype.val) := by
  classical
  have hc := early_mixed_spokes_count S F special Q hsub hsupp hregular hspecial
  have hp : Even (#K + #F + 2 * #(F.filter
      (fun C => #(ordinaryComponentPacket G S C) = 3)) + #special) := by
    rcases havailable with hk | he
    · simpa [hempty hk] using hk
    · exact special_selection_even_of_nonempty _ special _ hsize hempty hpar he
  rw [Finset.card_union_of_disjoint hdis,hc]
  convert hp using 1 <;> omega

end Gallai.TwoException
