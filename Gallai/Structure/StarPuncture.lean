/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddHubReserve

@[expose] public section

/-! # Exact degree changes after deleting a star -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [DecidableEq V]

/-- Away from the centre, a star edge joins a selected leaf to that centre. -/
theorem star_sup_adj_off_center (u : V) (B : Finset V) (v w : V) (hv : v ≠ u) :
    (B.sup (SimpleGraph.edge u)).Adj v w ↔ v ∈ B ∧ w = u := by
  induction B using Finset.induction with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.sup_insert, SimpleGraph.sup_adj, ih]
    by_cases hw : w = u
    · subst w
      simp [SimpleGraph.edge_adj, hv]
    · simp [SimpleGraph.edge_adj, hv, hw]

/-- Delete exactly the selected hub spokes without deleting vertices. -/
abbrev starPuncture (G : SimpleGraph V) (u : V) (B : Finset V) : SimpleGraph V :=
  G \ B.sup (SimpleGraph.edge u)

/-- Deleting a star centred outside an induced vertex set does not change the
induced graph.  This is the vertex-deletion transport used when a source proof
first punctures spokes at a hub and subsequently discards that hub. -/
theorem induce_starPuncture_eq_of_notMem (G : SimpleGraph V) (u : V)
    (B : Finset V) (S : Set V) (hu : u ∉ S) :
    (starPuncture G u B).induce S = G.induce S := by
  ext a b
  constructor
  · exact fun h => ((SimpleGraph.sdiff_adj _ _ _ _).mp h).1
  · intro h
    refine (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨h, ?_⟩
    intro hab
    have hau : a.val ≠ u := fun he => hu (he ▸ a.property)
    have hbu : b.val ≠ u := fun he => hu (he ▸ b.property)
    exact hbu ((star_sup_adj_off_center u B a.val b.val hau).mp hab).2

/-- Every selected spoke is absent in the puncture. -/
theorem starPuncture_missing (G : SimpleGraph V) (u : V) (B : Finset V)
    (hu : u ∉ B) (v : V) (hv : v ∈ B) : ¬ (starPuncture G u B).Adj u v := by
  simp [starPuncture, SimpleGraph.sdiff_adj, star_sup_adj_center u B hu, hv]

omit [DecidableEq V] in
/-- Restoring a genuine deleted star recovers exactly the original graph. -/
theorem starPuncture_restore (G : SimpleGraph V) (u : V) (B : Finset V)
    (hb : ∀ v ∈ B, G.Adj u v) :
    starPuncture G u B ⊔ B.sup (SimpleGraph.edge u) = G := by
  have hs : B.sup (SimpleGraph.edge u) ≤ G := by
    apply Finset.sup_le
    intro v hv a b ha
    rw [SimpleGraph.edge_adj] at ha
    rcases ha.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hb _ hv
    · exact (hb _ hv).symm
  ext v w
  simp only [SimpleGraph.sup_adj, starPuncture, SimpleGraph.sdiff_adj]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact hs h
  · intro h
    by_cases ha : (B.sup (SimpleGraph.edge u)).Adj v w
    · exact Or.inr ha
    · exact Or.inl ⟨h, ha⟩

/-- Adding back the selected star after a puncture is exactly the original
graph together with that star.  No hypothesis says that the spokes were
present before puncturing; this Boolean graph identity is the transport used
when a repair star is added to an already-punctured auxiliary. -/
theorem starPuncture_sup_star_eq_sup (G : SimpleGraph V) (u : V) (B : Finset V) :
    starPuncture G u B ⊔ B.sup (SimpleGraph.edge u) =
      G ⊔ B.sup (SimpleGraph.edge u) := by
  ext v w
  simp only [SimpleGraph.sup_adj, starPuncture, SimpleGraph.sdiff_adj]
  tauto

/-- Restoring one genuine spoke removes its leaf from the pending star. -/
theorem starPuncture_restore_leaf (G : SimpleGraph V) (u p : V) (B : Finset V)
    (hu : u ∉ B) (hp : p ∈ B) (hup : G.Adj u p) :
    starPuncture G u B ⊔ SimpleGraph.edge p u = starPuncture G u (B.erase p) := by
  have hstar : B.sup (SimpleGraph.edge u) =
      (B.erase p).sup (SimpleGraph.edge u) ⊔ SimpleGraph.edge u p := by
    calc
      B.sup (SimpleGraph.edge u) = (insert p (B.erase p)).sup (SimpleGraph.edge u) := by
        rw [Finset.insert_erase hp]
      _ = _ := by rw [Finset.sup_insert,sup_comm]
  have heG : SimpleGraph.edge u p ≤ G := by
    intro v w hvw
    rw [SimpleGraph.edge_adj] at hvw
    rcases hvw.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hup
    · exact hup.symm
  have hseparate : ∀ v w, (SimpleGraph.edge u p).Adj v w →
      ¬ ((B.erase p).sup (SimpleGraph.edge u)).Adj v w := by
    intro v w hvw
    rw [SimpleGraph.edge_adj] at hvw
    rcases hvw.1 with ⟨hv,hw⟩ | ⟨hv,hw⟩
    · rw [hv,hw,star_sup_adj_center u (B.erase p)
        (fun ht => hu (Finset.mem_of_mem_erase ht))]
      simp
    · rw [hv,hw,star_sup_adj_off_center u (B.erase p) p u hup.ne.symm]
      simp
  rw [SimpleGraph.edge_comm p u]
  ext v w
  simp only [starPuncture,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj,hstar]
  constructor
  · rintro (⟨hG,hnot⟩ | he)
    · exact ⟨hG,fun hA => hnot (Or.inl hA)⟩
    · exact ⟨heG he,hseparate v w he⟩
  · rintro ⟨hG,hA⟩
    by_cases he : (SimpleGraph.edge u p).Adj v w
    · exact Or.inr he
    · exact Or.inl ⟨hG,fun ht => ht.elim hA he⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local adjacency decision for finite puncture degree calculations. -/
noncomputable local instance starPunctureDecidableAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- At the hub, the selected neighbour set is removed exactly. -/
theorem starPuncture_neighbors_center (u : V) (B : Finset V) (hu : u ∉ B) :
    (starPuncture G u B).neighborFinset u = G.neighborFinset u \ B := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, starPuncture, SimpleGraph.sdiff_adj,
    star_sup_adj_center u B hu, Finset.mem_sdiff]

/-- At a selected leaf, the only lost neighbour is the hub. -/
theorem starPuncture_neighbors_leaf (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∈ B) :
    (starPuncture G u B).neighborFinset v = (G.neighborFinset v).erase u := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, starPuncture, SimpleGraph.sdiff_adj,
    star_sup_adj_off_center u B v w hv, hb, true_and, Finset.mem_erase]
  tauto

/-- Every unselected nonhub keeps exactly its old neighbours. -/
theorem starPuncture_neighbors_other (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∉ B) :
    (starPuncture G u B).neighborFinset v = G.neighborFinset v := by
  ext w
  simp [starPuncture, SimpleGraph.sdiff_adj, star_sup_adj_off_center u B v w hv, hb]

/-- Hub degree accounting for a genuine deleted star. -/
theorem starPuncture_degree_center (u : V) (B : Finset V) (hu : u ∉ B)
    (hb : B ⊆ G.neighborFinset u) :
    (starPuncture G u B).degree u + #B = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, starPuncture_neighbors_center G u B hu,
    Finset.card_sdiff_add_card_eq_card hb, SimpleGraph.card_neighborFinset_eq_degree]

/-- A selected genuine leaf loses exactly one incident edge. -/
theorem starPuncture_degree_leaf (u : V) (B : Finset V) (v : V)
    (hv : v ∈ B) (ha : G.Adj u v) :
    (starPuncture G u B).degree v + 1 = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    starPuncture_neighbors_leaf G u B v ha.ne.symm hv]
  simpa using Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr ha.symm)

/-- Every other nonhub keeps its degree. -/
theorem starPuncture_degree_other (u : V) (B : Finset V) (v : V)
    (hv : v ≠ u) (hb : v ∉ B) : (starPuncture G u B).degree v = G.degree v := by
  simpa using congrArg Finset.card (starPuncture_neighbors_other G u B v hv hb)

end Gallai
