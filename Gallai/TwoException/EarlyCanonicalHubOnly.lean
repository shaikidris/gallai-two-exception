/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalContacts
public import Gallai.TwoException.OrdinaryTwoT2Endgame

@[expose] public section

/-! # Canonical hub-only contact endgame -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalHubOnlyComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- An odd contact centre meeting the hub but no private vertex is reducible
whenever it touches an ordinary component. All contact guards are derived. -/
theorem bare_canonical_hub_only_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hprivate : windmillContacts x u = ∅)
    (hordinary : (earlyOrdinaryContactComponents G h x u).Nonempty) : False := by
  classical
  obtain ⟨hF,hx,_,_,hcover⟩ := bare_early_canonical_contact_guards h u x H
  apply bare_hub_contact_reducible h x H u hu hux
  · intro w hw hwh hwx
    have hS : w ∈ earlyOriginalContacts G h x u :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,hwh,hwx⟩
    rcases hcover w hS with hp | ho
    · obtain ⟨a,ha,_⟩ := (mem_windmillPrivateSet x _ _).mp hp
      rw [hprivate] at ha
      simp at ha
    · exact hx _ ho
  · obtain ⟨Z,hZ⟩ := hordinary
    obtain ⟨w,hw,_⟩ := Finset.mem_image.mp (hF hZ)
    exact ⟨w,(Finset.mem_filter.mp hw).2⟩

end Gallai.TwoException
