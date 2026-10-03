/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongJointProfile

@[expose] public section

/-! # Subcubic even-degree cap in the joint corridor auxiliary -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance jointCapAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- A separated windmill preparation cannot turn a neighbour of the
second endpoint into a passing even vertex. Its prepared even-neighbour
classification therefore survives the first-side puncture. -/
theorem long_joint_reserved_center_inherited
    (h u v : V) (S : Finset V) (N : List (V × V))
    (hu : u ∉ S) (huv : u ≠ v)
    (hsep : ∀ t ∈ S, ¬ G.Adj v t)
    (hN : ∀ e ∈ N, ¬ G.Adj v e.1 ∧ ¬ G.Adj v e.2)
    (hcenter : ∀ t, G.Adj v t → Even (G.degree t) → t = h) :
    let J := ordinaryMatePuncture (starPuncture G u (insert v S)) N
    ∀ t, J.Adj v t → Even (J.degree t) → t = h := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u (insert v S)) N
  have hsub : J ≤ G := (ordinaryMatePuncture_le N).trans (fun _ _ ht => ht.1)
  have huI : u ∉ insert v S := by simp [huv,hu]
  change ∀ t, J.Adj v t → Even (J.degree t) → t = h
  intro t hvt ht
  have hvtG : G.Adj v t := hsub hvt
  have htu : t ≠ u := by
    intro heq
    subst t
    exact starPuncture_missing G u (insert v S) huI v (Finset.mem_insert_self _ _)
      ((ordinaryMatePuncture_le N) hvt).symm
  have htI : t ∉ insert v S := by
    simp only [Finset.mem_insert]
    exact not_or.mpr ⟨hvtG.ne.symm,fun hs => hsep t hs hvtG⟩
  have htN : ∀ e ∈ N, t ≠ e.1 ∧ t ≠ e.2 := by
    intro e he
    exact ⟨fun hh => (hN e he).1 (hh ▸ hvtG),
      fun hh => (hN e he).2 (hh ▸ hvtG)⟩
  have hd := (long_ordinary_preparation_unchanged (G := G) u t (insert v S) N
    htu htI htN).1
  have htG : Even (G.degree t) := by
    simp only [← SimpleGraph.ncard_neighborSet] at hd ht ⊢
    dsimp only [J] at ht
    rwa [hd] at ht
  exact hcenter t hvtG htG

/-- A selected even leaf becomes odd even when the reserved leaf v has
arbitrary parity. Additional mate deletions must avoid this selected leaf. -/
theorem long_joint_selected_leaf_odd
    (u v w : V) (S : Finset V) (N : List (V × V))
    (hw : w ∈ S) (huw : G.Adj u w) (he : Even (G.degree w))
    (havoid : ∀ e ∈ N, w ≠ e.1 ∧ w ≠ e.2) :
    Odd ((ordinaryMatePuncture (starPuncture G u (insert v S)) N).degree w) := by
  classical
  have hs := starPuncture_degree_leaf (G := G) u (insert v S) w
    (Finset.mem_insert_of_mem hw) huw
  have hn := ordinaryMatePuncture_degree_of_avoids
    (G := starPuncture G u (insert v S)) N w havoid
  simp only [← SimpleGraph.ncard_neighborSet] at hs hn he ⊢
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff]
  omega

/-- In each contact row the hub is either a selected star leaf or an
endpoint of a deleted mate. Both interfaces flip its parity. -/
theorem long_joint_covered_hub_odd
    (u v x : V) (S : Finset V) (N : List (V × V))
    (hS : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t))
    (hdis : N.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ N, e.1 ≠ u ∧ e.2 ≠ u ∧
      e.1 ∉ insert v S ∧ e.2 ∉ insert v S)
    (hedges : ∀ e ∈ N, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcover : x ∈ S ∨ ∃ e ∈ N, x = e.1 ∨ x = e.2) :
    Odd ((ordinaryMatePuncture (starPuncture G u (insert v S)) N).degree x) := by
  classical
  rcases hcover with hx | ⟨e,he,hx⟩
  · apply long_joint_selected_leaf_odd u v x S N hx (hS x hx).1 (hS x hx).2
    intro e he
    obtain ⟨_,_,hp,hq⟩ := havoid e he
    exact ⟨fun hh => hp (hh ▸ Finset.mem_insert_of_mem hx),
      fun hh => hq (hh ▸ Finset.mem_insert_of_mem hx)⟩
  · have ho := ordinary_star_mates_endpoints_odd (G := G) u (insert v S) N
      hdis havoid hedges e he
    rcases hx with hx | hx
    · exact hx ▸ ho.1
    · exact hx ▸ ho.2

omit [DecidableEq V] in
/-- Complete first-side contact coverage gives a zero E-degree witness.
The only newly even vertex is the reserved endpoint, whose edge is absent;
all original even contacts are deleted leaves or odd mate endpoints. -/
theorem long_joint_contact_center_eDegree_zero
    (u v : V) (S : Finset V) (N : List (V × V))
    (J : SimpleGraph V) [DecidableRel J.Adj] (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = v)
    (hreserved : ¬ J.Adj u v)
    (hleaves : ∀ t ∈ S, ¬ J.Adj u t)
    (hmates : ∀ e ∈ N, Odd (J.degree e.1) ∧ Odd (J.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ ∃ e ∈ N, t = e.1 ∨ t = e.2) :
    eDegree J u = 0 := by
  classical
  apply eDegree_eq_zero_of_no_even_neighbor
  intro t hut ht
  rcases hprofile t ht with htG | htv
  · rcases hcontacts t (hsub hut) htG with hs | ⟨e,he,hte⟩
    · exact hleaves t hs hut
    · obtain ⟨hp,hq⟩ := hmates e he
      rcases hte with hte | hte
      · subst t
        exact (Nat.not_even_iff_odd.mpr hp) ht
      · subst t
        exact (Nat.not_even_iff_odd.mpr hq) ht
  · subst t
    exact hreserved hut

/-- The shared parity and second-endpoint classification yield the full
joint auxiliary cap as soon as its deleted hub is odd. The statement does
not assume connectedness or any path decomposition of the auxiliary. -/
theorem bare_long_joint_cap_of_profile
    (h v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (J : SimpleGraph V) [DecidableRel J.Adj] (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = v)
    (hxOdd : Odd (J.degree x))
    (hcenter : ∀ t, J.Adj v t → Even (J.degree t) → t = h) :
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧
      eDegree J v ≤ 1 ∧ eDegree J h ≤ 1 := by
  classical
  have hvCap : eDegree J v ≤ 1 := by
    have hs : evenNeighbors J v ⊆ {h} := by
      intro t ht
      obtain ⟨hvt,he⟩ := (mem_evenNeighbors (G := J) v t).mp ht
      exact Finset.mem_singleton.mpr (hcenter t hvt he)
    exact (Finset.card_le_card hs).trans (by simp)
  obtain ⟨_,_,_,_,_,hhzero,hcap⟩ := H.counterexample.1
  have hhCap : eDegree J h ≤ 1 := by
    have hs : evenNeighbors J h ⊆ {v} := by
      intro t ht
      obtain ⟨hht,he⟩ := (mem_evenNeighbors (G := J) h t).mp ht
      apply Finset.mem_singleton.mpr
      rcases hprofile t he with ho | htv
      · have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨hsub hht,ho⟩
        have hp : 0 < eDegree G h := Finset.card_pos.mpr ⟨t,hm⟩
        omega
      · exact htv
    exact (Finset.card_le_card hs).trans (by simp)
  refine ⟨?_,hvCap,hhCap⟩
  intro t ht
  by_cases htv : t = v
  · subst t
    exact hvCap.trans (by decide)
  by_cases hth : t = h
  · subst t
    exact hhCap.trans (by decide)
  have htx : t ≠ (x : V) := by
    intro heq
    subst t
    exact (Nat.not_even_iff_odd.mpr hxOdd) ht
  have htG := (hprofile t ht).resolve_right htv
  have hs : evenNeighbors J t ⊆ evenNeighbors G t := by
    intro w hw
    obtain ⟨htw,he⟩ := (mem_evenNeighbors (G := J) t w).mp hw
    rcases hprofile w he with ho | hwv
    · exact (mem_evenNeighbors (G := G) t w).mpr ⟨hsub htw,ho⟩
    · subst w
      exact False.elim (hth (hcenter t htw.symm ht))
  exact (Finset.card_le_card hs).trans (hcap t htG hth htx)

end Gallai.TwoException
