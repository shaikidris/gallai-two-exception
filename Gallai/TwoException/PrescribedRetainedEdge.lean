/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareMinimality
public import Gallai.Inputs.PartialOddStarRestore
public import Gallai.Structure.PartialEvenStar
public import Gallai.TwoException.Bare
public import Gallai.Inputs.OddEvenStarRestore

@[expose] public section

/-! # Retained-edge reduction for a prescribed even vertex -/

namespace Gallai.TwoException
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The retained leaf supplies endpoints by edge induction. No bareness
condition is imposed on the prescribed hub. -/
theorem prescribed_retained_edge_of_connected_puncture (h x v : V)
    (hhne : h ≠ x)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hv : v ∈ evenNeighbors G h)
    (hpar : Even (eDegree G h))
    (hconn : (starPuncture G h ((evenNeighbors G h).erase v)).Connected)
    (hcap : ∀ w, Even (G.degree w) → w ≠ h → w ≠ x → eDegree G w ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  obtain ⟨hhv, hvEven⟩ := (mem_evenNeighbors h v).mp hv
  have hvx : v ≠ x := by rintro rfl; exact hhx hhv
  let S := (evenNeighbors G h).erase v
  let J := starPuncture G h S
  let : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hS : S ⊆ evenNeighbors G h := Finset.erase_subset _ _
  have hhS : h ∉ S := fun hw => (show h ∉ evenNeighbors G h by simp) (hS hw)
  have hvS : v ∉ S := Finset.notMem_erase _ _
  have hxS : x ∉ S := by
    intro hw
    exact hhx ((mem_evenNeighbors h x).mp (hS hw)).1
  have hc : #S + 1 = eDegree G h := Finset.card_erase_add_one hv
  have ho : Odd #S := by
    rw [Nat.even_iff] at hpar
    rw [Nat.odd_iff]
    omega
  have hret : J.Adj h v := by
    refine ⟨hhv, ?_⟩
    intro hw
    exact hvS ((star_sup_adj_center h S hhS v).mp hw)
  have hlt : J.edgeFinset.card < G.edgeFinset.card := by
    have hs : J < G := by
      refine lt_of_le_not_ge (fun _ _ ha => ha.1) ?_
      intro hle
      obtain ⟨w, hw⟩ := Finset.card_pos.mp ho.pos
      exact starPuncture_missing G h S hhS w hw
        (hle ((mem_evenNeighbors h w).mp (hS hw)).1)
    have ht := Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hs)
    simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using ht
  have hdv : J.degree v = G.degree v := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G h S v hhv.ne.symm hvS
  have hdx : J.degree x = G.degree x := by
    have hxh : x ≠ h := hhne.symm
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G h S x hxh hxS
  have hcapJ := partialEvenStar_cap_two_exceptions G h x S hS hhEven ho hcap
  obtain ⟨D, hsize, hvend⟩ := hind J
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using hlt)
    hconn v x hvx hret.degree_pos_right
    (by rwa [hdv]) (by rwa [hdx]) (fun w hw _ hwx => hcapJ w hw hwx)
  have hhend : 0 < D.endpointCount h :=
    D.endpointCount_pos_of_odd_degree h (partialEvenStar_odd_center G h S hS hhEven ho)
  have hneigh (w : V) (hw : G.Adj h w) : 0 < D.endpointCount w := by
    by_cases hwv : w = v
    · subst w; omega
    · exact D.endpointCount_pos_of_odd_degree w (retainedEvenStar_odd_neighbor G h v w hw hwv)
  have hleaf (w : V) (hw : w ∈ S) : #((evenNeighbors G w).erase h) ≤ 2 := by
    obtain ⟨ha, he⟩ := (mem_evenNeighbors h w).mp (hS hw)
    have hwx : w ≠ x := by rintro rfl; exact hhx ha
    have hm : h ∈ evenNeighbors G w := (mem_evenNeighbors w h).mpr ⟨ha.symm, hhEven⟩
    have heq := Finset.card_erase_add_one hm
    have hb := hcap w he ha.ne.symm hwx
    change #(evenNeighbors G w) ≤ 3 at hb
    omega
  obtain ⟨P, hs, hp, _⟩ := D.restore_partial_odd_even_star h S hS ho hleaf hhend hneigh
  exact ⟨P, by omega, hp⟩

/-- The non-cut retained-edge reduction supplies puncture connectivity to
the general connected-puncture induction step. -/
theorem prescribed_retained_edge (h x v : V)
    (hhne : h ≠ x) (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hv : v ∈ evenNeighbors G h)
    (hpar : Even (eDegree G h))
    (hcut : (G.induce {w | w ≠ h}).Connected)
    (hcap : ∀ w, Even (G.degree w) → w ≠ h → w ≠ x → eDegree G w ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  let S := (evenNeighbors G h).erase v
  have hhS : h ∉ S := fun ha => (show h ∉ evenNeighbors G h by simp)
    (Finset.mem_of_mem_erase ha)
  have hret : (starPuncture G h S).Adj h v := by
    refine ⟨((mem_evenNeighbors h v).mp hv).1, ?_⟩
    intro hs
    exact (Finset.notMem_erase v _) ((star_sup_adj_center h S hhS v).mp hs)
  exact prescribed_retained_edge_of_connected_puncture h x v hhne hhEven hxEven hhx
    hv hpar (starPuncture_connected G h S hcut ⟨v, hret⟩) hcap hind

/-- An odd full even-neighbour star restores within the one-exception
budget. The other exception is retained, not used as a pending leaf. -/
theorem prescribed_odd_star (h x : V) (hhne : h ≠ x)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hxpos : 0 < G.degree x) (hhx : ¬ G.Adj h x)
    (ho : Odd (eDegree G h))
    (hcut : (G.induce {w | w ≠ h}).Connected)
    (hcap : ∀ w, Even (G.degree w) → w ≠ h → w ≠ x → eDegree G w ≤ 3) :
    BareConclusion G h := by
  classical
  let S := evenNeighbors G h
  let J := starPuncture G h S
  let : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hconn : J.Connected := odd_evenStarPuncture_connected G h hhEven ho hcut
  have hhOdd : Odd (J.degree h) :=
    partialEvenStar_odd_center G h S (by rfl) hhEven ho
  have hxS : x ∉ S := by
    intro hw
    exact hhx ((mem_evenNeighbors h x).mp hw).1
  have hdx : J.degree x = G.degree x := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G h S x hhne.symm hxS
  have hcJ := partialEvenStar_cap_two_exceptions G h x S (by rfl) hhEven ho hcap
  obtain ⟨D, hsize, _⟩ := one_exception_endpoint J x hconn
    (by rwa [hdx]) (by rwa [hdx]) hcJ
  have hleaf (w : V) (hw : w ∈ evenNeighbors G h) : eDegree G w ≤ 3 := by
    obtain ⟨ha, he⟩ := (mem_evenNeighbors h w).mp hw
    exact hcap w he ha.ne.symm (by rintro rfl; exact hhx ha)
  obtain ⟨P, hs, hp⟩ := D.restore_odd_even_star_exposing h hhEven ho hleaf
  exact ⟨P, by omega, hp⟩

/-- The complete non-cut trichotomy for the prescribed endpoint theorem.
Only the retained-edge branch consumes the smaller-instance induction. -/
theorem prescribed_noncut_reducible (h x : V)
    (hconn : G.Connected) (hhne : h ≠ x) (hhpos : 0 < G.degree h)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hcut : (G.induce {w | w ≠ h}).Connected)
    (hcap : ∀ w, Even (G.degree w) → w ≠ h → w ≠ x → eDegree G w ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  by_cases hxpos : 0 < G.degree x
  · by_cases hz : eDegree G h = 0
    · exact bare_endpoint h x ⟨hconn, hhne, hhpos, hhEven, hxEven, hz, hcap⟩
    · by_cases he : Even (eDegree G h)
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < eDegree G h by omega)
        exact prescribed_retained_edge h x v hhne hhEven hxEven hhx hv he hcut hcap hind
      · exact prescribed_odd_star h x hhne hhEven hxEven hxpos hhx
          (Nat.not_even_iff_odd.mp he) hcut hcap
  · apply one_exception_endpoint G h hconn hhpos hhEven
    intro w hw hwh
    by_cases hwx : w = x
    · subst w
      have hb := eDegree_le_degree (G := G) x
      omega
    · exact hcap w hw hwh hwx

end Gallai.TwoException
