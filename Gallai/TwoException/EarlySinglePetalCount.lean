/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareDelayedContact

@[expose] public section

/-! # The sole single-contact petal in the early residual -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance earlySingleCountComponents : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- With at least two ordinary contact components, every single-contact
private is the initially chosen private. The delayed spare-petal reduction
therefore leaves at most one single-contact petal for early payment. -/
theorem bare_early_single_private_eq_selected
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    2 ≤ #F →
      ∀ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
        G.Adj u r.val.val →
        (∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
          G.Adj u a.val → a = x) → r = p := by
  classical
  dsimp only
  intro hcount r hur hsingle
  have hres := bare_delayed_multiple_contact_residual h u x H C hxC p hup hu hcount
  by_contra hrp
  have hpr : p ≠ r := Ne.symm hrp
  have hnonadj : ¬ (evenSubgraph G).Adj p.val r.val := by
    intro ha
    have he := hsingle p.val ha.symm hup
    exact p.property.ne he.symm
  exact hres.2.1 ⟨r, hur, hpr, hnonadj, hsingle⟩

end Gallai.TwoException
