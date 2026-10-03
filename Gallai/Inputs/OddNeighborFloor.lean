/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddNeighborParity

@[expose] public section

/-! # The actual floor witness for the partial-triangle puncture

The neighbourhood hypotheses describe the original graph. Deleted degrees,
new parities and the punctured E-degree cap are all derived internally.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The three-edge deletion supplies a floor decomposition under the source's
strict minimality guards, with no punctured parity or degree cap assumed. -/
theorem oddNeighborDeletion_floor (u v x y z : V) (hd : [u, v, x, y, z].Nodup)
    (huv : G.Adj u v) (hux : G.Adj u x) (hyz : G.Adj y z)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hx : Even (G.degree x)) (hy : Even (G.degree y)) (hz : Even (G.degree z))
    (hNu : ∀ w, G.Adj u w → Even (G.degree w) → w = x ∨ w = y)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ oddNeighborDeletion u v x y z) (Fintype.card V / 2) := by
  classical
  have hle := oddNeighborDeletion_le u v x y z huv hux hyz
  obtain ⟨_, _, _, _, _, hk⟩ := oddNeighborDeletion_parity u v x y z hd hle hu hv hx hy hz
  obtain ⟨hcu, hcv⟩ := oddNeighborDeletion_centres u v x y z hd hle hu hv hx hy hz hNu hNv
  have hcapP := even_degree_cap_of_isolated_exception (G := G)
    (H := G \ oddNeighborDeletion u v x y z) (fun _ _ h => h.1) v hk hcv 3 hcap
  have hm : ∀ w, w ≠ u → (oddNeighborDeletion u v x y z).degree w ≤ 1 := by
    intro w hwu
    rw [oddNeighborDeletion_degree u v x y z hd w]
    simp only [if_neg hwu]
    split_ifs <;> omega
  have he : ∀ w, w ≠ u → w ≠ v →
      0 < (oddNeighborDeletion u v x y z).degree w → Even (G.degree w) := by
    intro w hwu hwv hp
    by_cases hwx : w = x
    · exact hwx ▸ hx
    by_cases hwy : w = y
    · exact hwy ▸ hy
    by_cases hwz : w = z
    · exact hwz ▸ hz
    rw [oddNeighborDeletion_degree u v x y z hd w] at hp
    simp [hwu, hwv, hwx, hwy, hwz] at hp
  have hdv : (oddNeighborDeletion u v x y z).degree v = 1 := by
    rw [oddNeighborDeletion_degree u v x y z hd v]
    simp [huv.ne.symm]
  have hfv : (oddNeighborDeletion u v x y z).Adj u v :=
    Or.inl (Or.inl ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv.ne⟩))
  exact odd_star_puncture_floor hle u v hm he hu hv hdv hfv hcu ht hcapP
    hconn hcap hnot hset hmin

end Gallai
