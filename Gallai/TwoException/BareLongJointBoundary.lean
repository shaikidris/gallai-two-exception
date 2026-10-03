/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongJointCap
public import Gallai.TwoException.OrdinaryStarMateBoundary

@[expose] public section

/-! # Component boundary in the joint corridor puncture -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance jointBoundaryAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Every joint auxiliary component contains a star centre, a selected
leaf, or a deleted mate endpoint. This uses connectedness of the original
graph, not connectedness of either intermediate puncture. -/
theorem long_joint_component_meets_boundary
    (hconn : G.Connected) (u v : V) (B S : Finset V) (O N : List (V × V))
    (K : (ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
        u (insert v S)) N).ConnectedComponent) :
    ∃ t ∈ K.supp, t = u ∨ t = v ∨ t ∈ B ∨ t ∈ S ∨
      ∃ e ∈ O ++ N, t = e.1 ∨ t = e.2 := by
  classical
  by_contra hn
  have havoid : ∀ t ∈ K.supp,
      t ≠ u ∧ t ≠ v ∧ t ∉ B ∧ t ∉ S ∧
      ∀ e ∈ O ++ N, t ≠ e.1 ∧ t ≠ e.2 := by
    intro t ht
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact fun hh => hn ⟨t,ht,Or.inl hh⟩
    · exact fun hh => hn ⟨t,ht,Or.inr (Or.inl hh)⟩
    · exact fun hh => hn ⟨t,ht,Or.inr (Or.inr (Or.inl hh))⟩
    · exact fun hh => hn ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inl hh)))⟩
    · intro e he
      exact ⟨fun hh => hn ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e,he,Or.inl hh⟩)))⟩,
        fun hh => hn ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e,he,Or.inr hh⟩)))⟩⟩
  have hclosed : ∀ r s, r ∈ K.supp → G.Adj r s → s ∈ K.supp := by
    intro r s hr hrs
    obtain ⟨hru,hrv,hrB,hrS,hrM⟩ := havoid r hr
    have hQ := (long_ordinary_preparation_unchanged (G := G) v r B O
      hrv hrB (fun e he => hrM e (List.mem_append_left N he))).2 s
    have hrI : r ∉ insert v S := by simp [hrv,hrS]
    have hJ := (long_ordinary_preparation_unchanged
      (G := ordinaryMatePuncture (starPuncture G v B) O) u r (insert v S) N
      hru hrI (fun e he => hrM e (List.mem_append_right O he))).2 s
    exact K.mem_supp_of_adj_mem_supp hr (hJ.mpr (hQ.mpr hrs))
  obtain ⟨w,hw⟩ := K.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {t : V}, Relation.ReflTransGen G.Adj w t → t ∈ K.supp := by
    intro t ht
    induction ht with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact (havoid u (hpreserve hreach)).1 rfl

end Gallai.TwoException
