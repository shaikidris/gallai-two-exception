/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalMultipleHubContradiction
public import Gallai.TwoException.EarlyCanonicalHubAllDoubleResidual
public import Gallai.TwoException.EarlySelectedOddHubContradiction

@[expose] public section

/-! # Canonical zero-contact or single-T3 frontier -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalZeroT3Components :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- After delayed and multiple-component restoration, the canonical ordinary
contact family is empty or consists of one three-contact triangle packet. -/
theorem bare_canonical_early_zero_or_t3
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u))
    : earlyOrdinaryContactComponents G h x u = ∅ ∨
      ∃ Z : (evenSubgraph G).ConnectedComponent,
        earlyOrdinaryContactComponents G h x u = {Z} ∧
        #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3 := by
  classical
  let F := earlyOrdinaryContactComponents G h x u
  have hle : #F ≤ 1 := by
    by_contra hn
    have hN : 2 ≤ #F := by omega
    exact bare_canonical_multiple_contacts_impossible h u x H C hxC f hinv hedge P
      hindex p hup hu hN
  by_cases hempty : F = ∅
  · exact Or.inl hempty
  · have hone : #F = 1 := by
      have hn : #F ≠ 0 := fun he => hempty (Finset.card_eq_zero.mp he)
      omega
    obtain ⟨Z,hZ⟩ := Finset.card_eq_one.mp hone
    refine Or.inr ⟨Z,hZ,?_⟩
    by_contra hnot3
    apply bare_canonical_delayed_single_or_odd_impossible h u x H C hxC p hup hu
    apply Or.inl
    refine ⟨hone,?_⟩
    intro W hW
    change W ∈ F at hW
    rw [hZ] at hW
    have hWZ := Finset.mem_singleton.mp hW
    simpa only [hWZ] using hnot3

end Gallai.TwoException
