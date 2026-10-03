/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeT3

@[expose] public section

/-! # Native regular and special triangle contributions -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance triangleGainStarAdj (G : SimpleGraph V) (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance triangleGainHalfAdj (G : SimpleGraph V) (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A regular T1/T2's single deleted contact contributes +1 after the
opposite mate has supplied two endpoints to its recipient. -/
theorem ordinary_native_regular_gain
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (haB : (a : V) ∈ B)
    (D : Decomposition (starPuncture G u B)) (hb : 2 ≤ D.endpointCount b)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #({(a : V)} \ A) + 1 ≤ #({(a : V)} ∩ A) := by
  classical
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    rw [heq]
    exact fun _ _ ha => ha.1
  have hp := ordinary_half_star_even_preserved u B A hAB hadj hleaves
  have hs : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hn := triangle_component_even_neighbors C b a c hs
  have hbE := ordinary_recipient_positive_after_half_star D u b A E hb hvec
  have haA : (a : V) ∈ A := by
    by_contra haA
    have ht := Finset.mem_sdiff.mpr ⟨haB, haA⟩
    have hu : u ∉ B \ A := fun hu => G.irrefl (hadj u (Finset.mem_sdiff.mp hu).1)
    have hmissing : ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj a u := by
      rw [heq]
      exact fun ha => starPuncture_missing G u (B \ A) hu a ht ha.symm
    have hone := ordinary_regular_pending_passing_le_one E u a b c hsub hp hn hmissing hbE
    have htwo := htight a ht
    omega
  simp [haA]

/-- In a special T2, both genuine deleted contacts are initially odd.
Their actual half-star transformation gives the nonnegative packet gain. -/
theorem ordinary_native_special_gain
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (hab : G.Adj a b)
    (haB : (a : V) ∈ B) (hbB : (b : V) ∈ B)
    (D : Decomposition (starPuncture G u B))
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #({(a : V), (b : V)} \ A) ≤ #({(a : V), (b : V)} ∩ A) := by
  classical
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    rw [heq]
    exact fun _ _ ha => ha.1
  have hp := ordinary_half_star_even_preserved u B A hAB hadj hleaves
  have hs : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hn := triangle_component_even_neighbors C b a c hs
  have huB : u ∉ B := fun hu => G.irrefl (hadj u hu)
  have hau : (a : V) ≠ u := fun he => huB (he ▸ haB)
  have hbD : 0 < D.endpointCount b := by
    apply D.endpointCount_pos_of_odd_degree
    exact ordinary_star_mates_leaves_odd u B [] hadj hleaves (by simp) b hbB
  have hmissing : ¬ (starPuncture G u B).Adj a u :=
    fun ha => starPuncture_missing G u B huB a haB ha.symm
  have hsel := ordinary_special_contacts_selected D u a b c B A haB hau hbD
    hmissing E hsub hp hn hvec htight
  apply ordinary_special_packet_contribution {(a : V), (b : V)} A (by simp [hab.ne])
  rcases hsel with haA | hbA
  · exact ⟨a, Finset.mem_inter.mpr ⟨by simp, haA⟩⟩
  · exact ⟨b, Finset.mem_inter.mpr ⟨by simp, hbA⟩⟩

section Prepared

variable {J : SimpleGraph V} [DecidableRel J.Adj]
noncomputable local instance preparedTriangleHalfAdj (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A restored ordinary mate still supplies regular-packet gain when
the prepared graph retains other unpaid deletions. -/
theorem ordinary_prepared_regular_triangle_gain
    (D : Decomposition J) (u : V) (S A : Finset V)
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (haS : (a : V) ∈ S)
    (hau : (a : V) ≠ u) (hmissing : ¬ J.Adj a u)
    (hb : 2 ≤ D.endpointCount b)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #({(a : V)} \ A) + 1 ≤ #({(a : V)} ∩ A) := by
  classical
  have hs : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hn := triangle_component_even_neighbors C b a c hs
  have hbE := ordinary_recipient_positive_after_half_star D u b A E hb hvec
  have haA : (a : V) ∈ A := by
    by_contra hnA
    have hm : ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj a u := by
      rintro (hj | ha)
      · exact hmissing hj
      · exact hnA ((star_sup_adj_off_center u A a u hau).mp ha).1
    exact (by
      have hone := ordinary_regular_pending_passing_le_one E u a b c
        hsub hprofile hn hm hbE
      have htwo := htight a (Finset.mem_sdiff.mpr ⟨haS,hnA⟩)
      omega)
  simp [haA]

/-- Positive untouched special contacts give nonnegative gain in an
arbitrary prepared half-star, with no plain-puncture representation. -/
theorem ordinary_prepared_special_triangle_gain
    (D : Decomposition J) (u : V) (S A : Finset V)
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (hab : G.Adj a b)
    (haS : (a : V) ∈ S) (hau : (a : V) ≠ u)
    (hmissing : ¬ J.Adj a u) (hb : 0 < D.endpointCount b)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #({(a : V),(b : V)} \ A) ≤ #({(a : V),(b : V)} ∩ A) := by
  classical
  have hs : C.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp [or_comm, or_left_comm]
  have hn := triangle_component_even_neighbors C b a c hs
  have hsel := ordinary_special_contacts_selected D u a b c S A haS hau hb
    hmissing E hsub hprofile hn hvec htight
  apply ordinary_special_packet_contribution {(a : V),(b : V)} A (by simp [hab.ne])
  rcases hsel with haA | hbA
  · exact ⟨a, Finset.mem_inter.mpr ⟨by simp,haA⟩⟩
  · exact ⟨b, Finset.mem_inter.mpr ⟨by simp,hbA⟩⟩

end Prepared

end Gallai.TwoException
