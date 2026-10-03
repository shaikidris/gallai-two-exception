/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalDelayedCases

@[expose] public section

/-! # All delayed residual restrictions on canonical early contacts -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalDelayedResidualComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Delayed restoration forces the same even count, absent spare single and
restricted spare-double/T2 profile in the canonical early component family. -/
theorem bare_canonical_delayed_multiple_residual
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S := earlyOriginalContacts G h x u
    let F := earlyOrdinaryContactComponents G h x u
    2 ≤ #F →
      Even #F ∧
      (¬ ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
        G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
        ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
          G.Adj u a.val → a = x) ∧
      (¬ (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)).Nonempty ∨
        (#F = 2 ∧
          ¬ ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
            G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
            ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
              a ≠ x → G.Adj u a.val)) := by
  classical
  dsimp only
  intro hcount
  let T : Finset (evenVertices G) := Finset.univ.filter
    (fun t => G.Adj u t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  have hF : earlyOrdinaryContactComponents G h x u =
      T.image (evenSubgraph G).connectedComponentMk :=
    (early_delayed_contact_agreement h u x C hxC).1
  have hTwo := early_delayed_two_contact_agreement h u x C hxC
  have hcountT : 2 ≤ #(T.image (evenSubgraph G).connectedComponentMk) := by
    rw [← hF]
    exact hcount
  have hr := bare_delayed_multiple_contact_residual h u x H C hxC p hup hu hcountT
  rw [← hTwo,← hF] at hr
  exact hr

end Gallai.TwoException
