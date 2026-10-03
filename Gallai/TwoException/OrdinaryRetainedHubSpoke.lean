/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryFiniteMateAssembly
public import Gallai.TwoException.OrdinaryStarMateProfile

@[expose] public section

/-! # Hub spokes survive ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance retainedHubComponentEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance retainedHubAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A hub-private edge survives the star and all ordinary mate deletions.
The star centre is originally odd and the finite mate components exclude
the even hub. No auxiliary retained-adjacency premise is used. -/
theorem ordinary_retained_hub_spoke
    (u : V) (hu : Odd (G.degree u)) (B : Finset V)
    (x p : evenVertices G) (hxp : (evenSubgraph G).Adj x p)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hx : ∀ C ∈ F, x ∉ C.supp) :
    (ordinaryMatePuncture (starPuncture G u B)
      ((F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))))).Adj x p := by
  classical
  have hn : ¬ Even (G.degree u) := Nat.not_even_iff_odd.mpr hu
  have hxu : (x : V) ≠ u := by
    intro he
    exact hn (he ▸ x.property)
  have hpu : (p : V) ≠ u := by
    intro he
    exact hn (he ▸ p.property)
  have hstar : (starPuncture G u B).Adj x p := by
    refine ⟨hxp,?_⟩
    intro hs
    exact hpu ((star_sup_adj_off_center u B x p hxu).mp hs).2
  have hav : ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      (x : V) ≠ e.1 ∧ (x : V) ≠ e.2 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨hl,hr⟩ := hsupp C hCF f hfC
    constructor
    · intro heq
      have he : x = f.1 := Subtype.val_injective heq
      exact hx C hCF (he ▸ hl)
    · intro heq
      have he : x = f.2 := Subtype.val_injective heq
      exact hx C hCF (he ▸ hr)
  exact (ordinaryMatePuncture_adj_of_avoids (G := starPuncture G u B) _ x p hav).mpr hstar

end Gallai.TwoException
