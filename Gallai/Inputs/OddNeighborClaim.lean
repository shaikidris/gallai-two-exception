/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddNeighborFloor
public import Gallai.Inputs.OddNeighborRestore
public import Gallai.Inputs.NoEvenIsolates

@[expose] public section

/-! # An odd neighbour without even neighbours forces a full triangle

The component labels are constructed from the actual all-triangle structure.
Both the punctured floor witness and its same-count restoration are consumed.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Source Claim 6: an odd vertex touching an even component is adjacent to
all its vertices if it has an odd neighbour without any even neighbour. -/
theorem minimal_counterexample_odd_neighbor_forces_full
    (u v : V) (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent)
    (htouch : ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj u w) :
    ∀ w : evenVertices G, w ∈ C.supp → G.Adj u w := by
  classical
  by_contra hfail
  have ht : ComponentsAreTriangles (evenSubgraph G) :=
    minimal_counterexample_even_components_triangles hconn hcap hnot hset hmin
  obtain ⟨a, b, c, hab, hac, hbc, hm, _, _, hbcE, hua, horder⟩ :=
    even_triangle_hub_labels u C (ht C).1 (ht C).2 htouch
  have hnc : ¬ G.Adj u c := by
    intro hc
    apply hfail
    intro w hw
    rcases (hm w).mp hw with rfl | rfl | rfl
    · exact hua
    · exact horder hc
    · exact hc
  have hNu : ∀ w, G.Adj u w → Even (G.degree w) → w = a ∨ w = b := by
    intro w huw hwEven
    let q : evenVertices G := ⟨w, hwEven⟩
    let E := (evenSubgraph G).connectedComponentMk q
    have hqE : q ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hCE := minimal_counterexample_odd_neighbors_one_component u hu
      hconn hcap hnot hset hmin C E htouch ⟨q, hqE, huw⟩
    have hqC : q ∈ C.supp := by rw [hCE]; exact hqE
    rcases (hm q).mp hqC with hqa | hqb | hqc
    · exact Or.inl (congrArg Subtype.val hqa)
    · exact Or.inr (congrArg Subtype.val hqb)
    · have hwc : w = (c : V) := congrArg Subtype.val hqc
      exact (hnc (hwc ▸ huw)).elim
  have hNb : ∀ w, G.Adj b w → Even (G.degree w) → w = a ∨ w = c := by
    intro w hbw hwEven
    let q : evenVertices G := ⟨w, hwEven⟩
    have hbC : b ∈ C.supp := (hm b).mpr (Or.inr (Or.inl rfl))
    have hqC : q ∈ C.supp := C.mem_supp_of_adj_mem_supp hbC hbw
    rcases (hm q).mp hqC with hqa | hqb | hqc
    · exact Or.inl (congrArg Subtype.val hqa)
    · exact (hbw.ne (congrArg Subtype.val hqb).symm).elim
    · exact Or.inr (congrArg Subtype.val hqc)
  have huaN : u ≠ (a : V) := ComponentDeletionChoice.hub_ne_even hu a
  have hubN : u ≠ (b : V) := ComponentDeletionChoice.hub_ne_even hu b
  have hucN : u ≠ (c : V) := ComponentDeletionChoice.hub_ne_even hu c
  have hvaN : v ≠ (a : V) := ComponentDeletionChoice.hub_ne_even hv a
  have hvbN : v ≠ (b : V) := ComponentDeletionChoice.hub_ne_even hv b
  have hvcN : v ≠ (c : V) := ComponentDeletionChoice.hub_ne_even hv c
  have habN : (a : V) ≠ b := fun h => hab (Subtype.ext h)
  have hacN : (a : V) ≠ c := fun h => hac (Subtype.ext h)
  have hbcN : (b : V) ≠ c := fun h => hbc (Subtype.ext h)
  have hd : [u, v, (a : V), (b : V), (c : V)].Nodup := by
    simp [huv.ne, huaN, hubN, hucN, hvaN, hvbN, hvcN, habN, hacN, hbcN]
  obtain ⟨D, hD⟩ := oddNeighborDeletion_floor u v a b c hd huv hua hbcE
    hu hv a.property b.property c.property hNu hNv ht hconn hcap hnot hset hmin
  obtain ⟨P, hP⟩ := D.restore_odd_neighbor_puncture u v a b c hd
    (oddNeighborDeletion_le u v a b c huv hua hbcE)
    hu hv a.property b.property c.property hNu hNv hNb
  exact hnot ⟨P, hP.le.trans hD⟩

end Gallai
