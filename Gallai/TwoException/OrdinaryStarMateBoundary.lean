/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateProfile
public import Gallai.TwoException.ContactStarAssembly

@[expose] public section

/-! # Actual component contacts for simultaneous star and mate deletions -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance starMateBoundaryAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- No auxiliary component can avoid the entire deletion support. This
includes mate endpoints, not only the centre and selected star leaves. -/
theorem ordinary_star_mates_component_meets_boundary
    (hconn : G.Connected) (u : V) (B : Finset V) (M : List (V × V))
    (K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent) :
    ∃ t ∈ K.supp, t = u ∨ t ∈ B ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2 := by
  classical
  by_contra hnone
  have havoid : ∀ t ∈ K.supp,
      t ≠ u ∧ t ∉ B ∧ ∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2 := by
    intro t ht
    refine ⟨?_,?_,?_⟩
    · exact fun he => hnone ⟨t,ht,Or.inl he⟩
    · exact fun hb => hnone ⟨t,ht,Or.inr (Or.inl hb)⟩
    · intro e he
      exact ⟨fun hl => hnone ⟨t,ht,Or.inr (Or.inr ⟨e,he,Or.inl hl⟩)⟩,
        fun hr => hnone ⟨t,ht,Or.inr (Or.inr ⟨e,he,Or.inr hr⟩)⟩⟩
  have hclosed : ∀ r s, r ∈ K.supp → G.Adj r s → s ∈ K.supp := by
    intro r s hr hrs
    have hstar : (starPuncture G u B).Adj r s := by
      refine ⟨hrs,?_⟩
      intro hs
      exact (havoid r hr).2.1
        ((star_sup_adj_off_center u B r s (havoid r hr).1).mp hs).1
    have hJ := (ordinaryMatePuncture_adj_of_avoids
      (G := starPuncture G u B) M r s (havoid r hr).2.2).mpr hstar
    exact K.mem_supp_of_adj_mem_supp hr hJ
  obtain ⟨w,hw⟩ := K.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj w v →
      w ∈ K.supp → v ∈ K.supp := by
    intro v hv hw
    induction hv with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact (havoid u (hpreserve hreach hw)).1 rfl

end Gallai.TwoException
