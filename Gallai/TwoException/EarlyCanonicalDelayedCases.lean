/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyDelayedContactAgreement
public import Gallai.TwoException.BareDelayedContact

@[expose] public section

/-! # Delayed reductions in the canonical ordinary-component interface -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalDelayedComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A single non-T3 ordinary component, or an odd count of at least three
ordinary components, is reducible using the canonical early contact data. -/
theorem bare_canonical_delayed_single_or_odd_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u))
    (hcase :
      let S := earlyOriginalContacts G h x u
      let F := earlyOrdinaryContactComponents G h x u
      (#F = 1 ∧ ∀ Z ∈ F, #(ordinaryComponentPacket G S Z) ≠ 3) ∨
        (Odd #F ∧ 3 ≤ #F)) : False := by
  classical
  let T : Finset (evenVertices G) := Finset.univ.filter
    (fun t => G.Adj u t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  have hag := early_delayed_contact_agreement h u x C hxC
  have hF : earlyOrdinaryContactComponents G h x u =
      T.image (evenSubgraph G).connectedComponentMk := hag.1
  rcases hcase with hone | hodd
  · apply bare_delayed_contact_reducible h u x H C hxC p hup hu
    apply Or.inl
    refine ⟨?_,?_⟩
    · change #(T.image (evenSubgraph G).connectedComponentMk) = 1
      rw [← hF]
      exact hone.1
    · intro Z hZ
      have hZE : Z ∈ earlyOrdinaryContactComponents G h x u := by
        rw [hF]
        exact hZ
      have heq := hag.2 Z hZE
      change #(ordinaryComponentPacket G T Z) ≠ 3
      rw [← heq]
      exact hone.2 Z hZE
  · apply bare_delayed_contact_reducible h u x H C hxC p hup hu
    apply Or.inr
    apply Or.inl
    change Odd #(T.image (evenSubgraph G).connectedComponentMk) ∧
      3 ≤ #(T.image (evenSubgraph G).connectedComponentMk)
    rw [← hF]
    exact hodd

end Gallai.TwoException
