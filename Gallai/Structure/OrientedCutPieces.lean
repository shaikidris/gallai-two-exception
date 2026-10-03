/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.CutVertexPieces

@[expose] public section

/-! # Orient a cut partition away from a designated vertex -/

namespace Gallai

variable {V : Type*} (G : SimpleGraph V)

/-- A disconnected deletion at a non-isolated vertex gives two separated
surviving vertices. Non-isolation rules out the empty deletion convention. -/
theorem separated_vertices_of_disconnected_deletion (z : V)
    (hincident : ∃ w, G.Adj z w)
    (hn : ¬ (G.induce {v | v ≠ z}).Connected) :
    ∃ (a b : V) (ha : a ≠ z) (hb : b ≠ z),
      ¬ (G.induce {v | v ≠ z}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  classical
  obtain ⟨w, hw⟩ := hincident
  have : Nonempty {v : V | v ≠ z} := ⟨⟨w, hw.ne.symm⟩⟩
  have h : ¬ ∀ a b : {v : V | v ≠ z}, (G.induce {v | v ≠ z}).Reachable a b :=
    fun h => hn ⟨h⟩
  obtain ⟨a, ha⟩ := not_forall.mp h
  obtain ⟨b, hb⟩ := not_forall.mp ha
  exact ⟨a.val, b.val, a.property, b.property, hb⟩

/-- Choose the nontrivial side not containing the designated vertex. Both
connected pieces and the side orientation are derived from disconnectedness. -/
theorem cut_vertex_pieces_away_from (hconn : G.Connected) (z x : V)
    (hxz : x ≠ z) (hincident : ∃ w, G.Adj z w)
    (hn : ¬ (G.induce {v | v ≠ z}).Connected) :
    ∃ S T : Set V, z ∈ S ∧ z ∈ T ∧ x ∉ S ∧ x ∈ T ∧
      (∃ a ∈ S, a ≠ z) ∧ S ∪ T = Set.univ ∧ S ∩ T = {z} ∧
      (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G ∧
      (G.induce S).Connected ∧ (G.induce T).Connected := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := separated_vertices_of_disconnected_deletion G z hincident hn
  obtain ⟨S, T, hcover, hinter, haS, hbT, hgraph, hcS, hcT⟩ :=
    cut_vertex_pieces G hconn z a b ha hb hab
  have hz : z ∈ S ∩ T := by rw [hinter]; exact Set.mem_singleton z
  have hj (v : V) (hs : v ∈ S) (ht : v ∈ T) : v = z := by
    have h : v ∈ S ∩ T := ⟨hs, ht⟩
    simpa only [hinter, Set.mem_singleton_iff] using h
  by_cases hxS : x ∈ S
  · have hxT : x ∉ T := fun h => hxz (hj x hxS h)
    exact ⟨T, S, hz.2, hz.1, hxT, hxS, ⟨b, hbT, hb⟩,
      (Set.union_comm T S).trans hcover, (Set.inter_comm T S).trans hinter,
      (sup_comm _ _).trans hgraph, hcT, hcS⟩
  · have hxT : x ∈ T := by
      have h : x ∈ S ∪ T := by rw [hcover]; trivial
      exact h.resolve_left hxS
    exact ⟨S, T, hz.1, hz.2, hxS, hxT, ⟨a, haS, ha⟩,
      hcover, hinter, hgraph, hcS, hcT⟩

end Gallai
