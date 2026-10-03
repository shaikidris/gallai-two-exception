/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureAssembly

@[expose] public section

/-! # Component floors for contact-star punctures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance starAssemblyAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

theorem contact_star_leaf_odd (u t : V) (B : Finset V)
    (ht : t ∈ B) (hut : G.Adj u t) (he : Even (G.degree t)) :
    Odd ((starPuncture G u B).degree t) := by
  have hd := starPuncture_degree_leaf (G := G) u B t ht hut
  simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

/-- Every component of a star puncture of a connected graph meets the
centre or a deleted leaf. -/
theorem contact_star_component_meets_boundary (hconn : G.Connected)
    (u : V) (B : Finset V) (C : (starPuncture G u B).ConnectedComponent) :
    ∃ t ∈ C.supp, t = u ∨ t ∈ B := by
  classical
  by_contra hnone
  have havoid : ∀ t ∈ C.supp, t ≠ u ∧ t ∉ B := by
    intro t ht
    exact ⟨fun he => hnone ⟨t, ht, Or.inl he⟩,
      fun hb => hnone ⟨t, ht, Or.inr hb⟩⟩
  have hclosed : ∀ r s, r ∈ C.supp → G.Adj r s → s ∈ C.supp := by
    intro r s hr hrs
    have hpuncture : (starPuncture G u B).Adj r s := by
      refine ⟨hrs, ?_⟩
      intro hs
      exact (havoid r hr).2
        ((star_sup_adj_off_center u B r s (havoid r hr).1).mp hs).1
    exact C.mem_supp_of_adj_mem_supp hr hpuncture
  obtain ⟨w, hw⟩ := C.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj w v →
      w ∈ C.supp → v ∈ C.supp := by
    intro v hv hw
    induction hv with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact (havoid u (hpreserve hreach hw)).1 rfl

/-- A contact-star puncture has an ambient floor budget when its boundary
is made of the zero-E-degree centre, prescribed isolate, hub and privates.
A retained private supplies the witness for the hub's own component. -/
theorem contact_star_floor_of_boundary_data
    (hconn : G.Connected) (h u x : V) (B : Finset V)
    (hkeep : ∀ t, Even ((starPuncture G u B).degree t) → Even (G.degree t))
    (hcap : ∀ t, Even ((starPuncture G u B).degree t) →
      eDegree (starPuncture G u B) t ≤ 3)
    (hxEven : Even (G.degree x)) (hxOdd : Odd ((starPuncture G u B).degree x))
    (hcentre : eDegree (starPuncture G u B) u = 0)
    (hhzero : eDegree G h = 0)
    (hleaves : ∀ t ∈ B, t = x ∨ t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (p : V) (hxp : (starPuncture G u B).Adj x p)
    (hpx : G.Adj p x) (hp : eDegree G p = 2) :
    HasPathBudget (starPuncture G u B) (Fintype.card V / 2) := by
  classical
  have hsub : starPuncture G u B ≤ G := fun _ _ ha => ha.1
  apply floor_of_components
  intro C
  obtain ⟨t, htC, ht⟩ := contact_star_component_meets_boundary hconn u B C
  rcases ht with htu | htB
  · subst t
    apply contact_component_floor_of_eDegree_le_one hcap C u htC
    omega
  · rcases hleaves t htB with htx | hth | ⟨htx, htdeg⟩
    · subst t
      exact contact_private_component_floor_without_parity hsub hkeep hcap C x p
        (C.mem_supp_of_adj_mem_supp htC hxp) hxEven hxOdd hpx hp
    · subst t
      apply contact_component_floor_of_eDegree_le_one hcap C h htC
      have hz := bare_isolate_puncture_eDegree_zero hsub hkeep h hhzero
      omega
    · exact contact_private_component_floor_without_parity hsub hkeep hcap C x t
        htC hxEven hxOdd htx htdeg

end Gallai.TwoException
