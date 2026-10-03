/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryComponentPartition

@[expose] public section

/-! # Whole-component three-contact gain in the actual half-star graph -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3StarAdj (G : SimpleGraph V) (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance t3HalfAdj (G : SimpleGraph V) (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- All three contacts of a whole ordinary triangle contribute at least
one selected-minus-pending unit in a tight half-star failure. -/
theorem ordinary_native_t3_gain
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (haB : (a : V) ∈ B) (hbB : (b : V) ∈ B) (hcB : (c : V) ∈ B)
    (D : Decomposition (starPuncture G u B))
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #({(a : V), (b : V), (c : V)} \ A) + 1 ≤
      #({(a : V), (b : V), (c : V)} ∩ A) := by
  classical
  have habne : (a : V) ≠ b := hab.ne
  have hbcne : (b : V) ≠ c := hbc.ne
  have hacne : (a : V) ≠ c := hca.ne.symm
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    rw [heq]
    exact fun _ _ ha => ha.1
  have hp := ordinary_half_star_even_preserved u B A hAB hadj hleaves
  have hpos : ∀ t ∈ B, 0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    exact ordinary_star_mates_leaves_odd u B [] hadj hleaves (by simp) t ht
  have hmissing : ∀ t ∈ B \ A,
      ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj t u := by
    intro t ht
    rw [heq]
    have hu : u ∉ B \ A := fun hu => G.irrefl (hadj u (Finset.mem_sdiff.mp hu).1)
    exact fun ha => starPuncture_missing G u (B \ A) hu t ht ha.symm
  have hsA : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hsC : C.supp = {a,c,b} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hnA := triangle_component_even_neighbors C b a c hsA
  have hnB := triangle_component_even_neighbors C a b c hsupp
  have hnC := triangle_component_even_neighbors C a c b hsC
  apply ordinary_three_packet_half_star_contribution D u
    {(a : V), (b : V), (c : V)} A (by simp [habne, hacne, hbcne]) E hvec
  intro w hw
  obtain ⟨hwL, hwA⟩ := Finset.mem_sdiff.mp hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwL
  rcases hwL with rfl | rfl | rfl
  · have ht := Finset.mem_sdiff.mpr ⟨haB, hwA⟩
    exact ⟨b, c, by simp [habne, hacne], hpos b hbB, hpos c hcB,
      ordinary_pending_outside_slots_positive E u a b c hsub hp hnA (hmissing a ht), htight a ht⟩
  · have ht := Finset.mem_sdiff.mpr ⟨hbB, hwA⟩
    exact ⟨a, c, by ext t; simp; aesop, hpos a haB, hpos c hcB,
      ordinary_pending_outside_slots_positive E u b a c hsub hp hnB (hmissing b ht), htight b ht⟩
  · have ht := Finset.mem_sdiff.mpr ⟨hcB, hwA⟩
    exact ⟨a, b, by ext t; simp; aesop, hpos a haB, hpos b hbB,
      ordinary_pending_outside_slots_positive E u c a b hsub hp hnC (hmissing c ht), htight c ht⟩

section Prepared
variable {J : SimpleGraph V} [DecidableRel J.Adj]
noncomputable local instance preparedT3HalfAdj (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Three positive contacts retain their +1 contribution after unrelated
preparation edges have been deleted or restored. -/
theorem ordinary_prepared_t3_gain
    (u : V) (S A : Finset V)
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (haS : (a : V) ∈ S) (hbS : (b : V) ∈ S) (hcS : (c : V) ∈ S)
    (D : Decomposition J)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hp : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hpos : ∀ t ∈ S, 0 < D.endpointCount t)
    (hmissing : ∀ t ∈ S \ A, ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj t u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #({(a : V),(b : V),(c : V)} \ A) + 1 ≤
      #({(a : V),(b : V),(c : V)} ∩ A) := by
  classical
  have habne : (a : V) ≠ b := hab.ne
  have hbcne : (b : V) ≠ c := hbc.ne
  have hacne : (a : V) ≠ c := hca.ne.symm
  have hsA : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hsC : C.supp = {a,c,b} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hnA := triangle_component_even_neighbors C b a c hsA
  have hnB := triangle_component_even_neighbors C a b c hsupp
  have hnC := triangle_component_even_neighbors C a c b hsC
  apply ordinary_three_packet_half_star_contribution D u
    {(a : V),(b : V),(c : V)} A (by simp [habne,hacne,hbcne]) E hvec
  intro w hw
  obtain ⟨hwL,hwA⟩ := Finset.mem_sdiff.mp hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hwL
  rcases hwL with rfl | rfl | rfl
  · have ht := Finset.mem_sdiff.mpr ⟨haS,hwA⟩
    exact ⟨b,c,by simp [habne,hacne],hpos b hbS,hpos c hcS,
      ordinary_pending_outside_slots_positive E u a b c hsub hp hnA (hmissing a ht),
      htight a ht⟩
  · have ht := Finset.mem_sdiff.mpr ⟨hbS,hwA⟩
    exact ⟨a,c,by ext t; simp; aesop,hpos a haS,hpos c hcS,
      ordinary_pending_outside_slots_positive E u b a c hsub hp hnB (hmissing b ht),
      htight b ht⟩
  · have ht := Finset.mem_sdiff.mpr ⟨hcS,hwA⟩
    exact ⟨a,b,by ext t; simp; aesop,hpos a haS,hpos b hbS,
      ordinary_pending_outside_slots_positive E u c a b hsub hp hnC (hmissing c ht),
      htight c ht⟩
end Prepared

end Gallai.TwoException
