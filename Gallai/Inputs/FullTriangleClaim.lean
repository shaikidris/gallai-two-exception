/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FullTriangleFloor
public import Gallai.Inputs.OddNeighborClaim

@[expose] public section

/-! # Odd neighbours of a vertex touching an even triangle -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Source Claim 7: an odd neighbour of a vertex touching an even
component must itself have an even neighbour, under strict minimality. -/
theorem minimal_counterexample_odd_neighbor_has_even_neighbor
    (u v : V) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent)
    (htouch : ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj u w) :
    ∃ w, G.Adj v w ∧ Even (G.degree w) := by
  classical
  by_cases hue : Even (G.degree u)
  · exact ⟨u, huv.symm, hue⟩
  have hu : Odd (G.degree u) := Nat.not_even_iff_odd.mp hue
  by_contra hfail
  have hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w) := by
    intro w ha he
    exact hfail ⟨w, ha, he⟩
  have ht : ComponentsAreTriangles (evenSubgraph G) :=
    minimal_counterexample_even_components_triangles hconn hcap hnot hset hmin
  have hfull := minimal_counterexample_odd_neighbor_forces_full u v hu hv huv hNv
    hconn hcap hnot hset hmin C htouch
  obtain ⟨a, b, c, hab, hac, hbc, hm, _, _, _, _, _⟩ :=
    even_triangle_hub_labels u C (ht C).1 (ht C).2 htouch
  let A : Finset V := {(a : V), (b : V), (c : V)}
  have habN : (a : V) ≠ b := fun h => hab (Subtype.ext h)
  have hacN : (a : V) ≠ c := fun h => hac (Subtype.ext h)
  have hbcN : (b : V) ≠ c := fun h => hbc (Subtype.ext h)
  have hA : #A = 3 := by simp [A, habN, hacN, hbcN]
  have hmA (q : evenVertices G) : (q : V) ∈ A ↔ q ∈ C.supp := by
    rw [hm q]
    simp only [A, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · rintro (rfl | rfl | rfl) <;> simp
  have hn : evenNeighbors G u = A := by
    ext w
    constructor
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
      let q : evenVertices G := ⟨w, he⟩
      let E := (evenSubgraph G).connectedComponentMk q
      have hqE : q ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hCE := minimal_counterexample_odd_neighbors_one_component u hu
        hconn hcap hnot hset hmin C E htouch ⟨q, hqE, ha⟩
      apply (hmA q).mpr
      rw [hCE]
      exact hqE
    · intro hw
      have he : Even (G.degree w) := by
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact a.property
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact b.property
        have hwc := Finset.mem_singleton.mp hw
        exact hwc ▸ c.property
      let q : evenVertices G := ⟨w, he⟩
      exact (mem_evenNeighbors u w).mpr ⟨hfull q ((hmA q).mp hw), he⟩
  have hthree : eDegree G u = 3 := by change #(evenNeighbors G u) = 3; rw [hn, hA]
  have hlocal : ∀ w ∈ evenNeighbors G u, eDegree G w ≤ 2 := by
    intro w hw
    have he := ((mem_evenNeighbors u w).mp hw).2
    let q : evenVertices G := ⟨w, he⟩
    have hwA : w ∈ A := hn ▸ hw
    have hqC := (hmA q).mp hwA
    have hs : evenNeighbors G w ⊆ A.erase w := by
      intro t ht
      obtain ⟨ha, het⟩ := (mem_evenNeighbors w t).mp ht
      let r : evenVertices G := ⟨t, het⟩
      exact Finset.mem_erase.mpr ⟨ha.ne.symm,
        (hmA r).mpr (C.mem_supp_of_adj_mem_supp hqC ha)⟩
    have hc := Finset.card_le_card hs
    have hec := Finset.card_erase_add_one hwA
    change #(evenNeighbors G w) ≤ 2
    omega
  obtain ⟨D, hD⟩ := full_triangle_odd_neighbor_floor u v hu hv huv hNv hthree ht
    hconn hcap hnot hset hmin
  obtain ⟨P, hP⟩ := D.restore_full_triangle_odd_neighbor u v hu hv huv hNv hthree hlocal
  exact hnot ⟨P, hP.le.trans hD⟩

end Gallai
