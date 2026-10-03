/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FanPunctureFloor

@[expose] public section

/-! # The partial-triangle odd-neighbour deletion

The three removed edges are uv, ux and yz. All graph and parity statements
refer to this actual deletion; no passing-neighbour data is postulated.
-/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two-spoke star and opposite triangle edge used for the partial case. -/
def oddNeighborDeletion (u v x y z : V) : SimpleGraph V :=
  SimpleGraph.edge u v ⊔ SimpleGraph.edge u x ⊔ SimpleGraph.edge y z

instance (u v x y z : V) : DecidableRel (oddNeighborDeletion u v x y z).Adj :=
  inferInstanceAs (DecidableRel
    (SimpleGraph.edge u v ⊔ SimpleGraph.edge u x ⊔ SimpleGraph.edge y z).Adj)

/-- The centre loses two edges, all four other labels one, and no other
vertex loses an edge. Distinctness is explicit. -/
theorem oddNeighborDeletion_degree (u v x y z : V) (hd : [u, v, x, y, z].Nodup)
    (t : V) :
    (oddNeighborDeletion u v x y z).degree t =
      if t = u then 2 else if t ∈ ({v, x, y, z} : Finset V) then 1 else 0 := by
  classical
  have huv : u ≠ v := by simp_all
  have hux : u ≠ x := by simp_all
  have huy : u ≠ y := by simp_all
  have huz : u ≠ z := by simp_all
  have hvx : v ≠ x := by simp_all
  have hvy : v ≠ y := by simp_all
  have hvz : v ≠ z := by simp_all
  have hxy : x ≠ y := by simp_all
  have hxz : x ≠ z := by simp_all
  have hyz : y ≠ z := by simp_all
  have hn : (oddNeighborDeletion u v x y z).neighborFinset t =
      if t = u then {v, x} else if t = v ∨ t = x then {u}
      else if t = y then {z} else if t = z then {y} else ∅ := by
    ext w
    simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.mem_neighborSet]
    simp only [oddNeighborDeletion, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
    split_ifs <;> simp_all <;> aesop
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
  split_ifs <;> simp_all

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The three displayed original edges make the deletion a subgraph. -/
theorem oddNeighborDeletion_le (u v x y z : V)
    (huv : G.Adj u v) (hux : G.Adj u x) (hyz : G.Adj y z) :
    oddNeighborDeletion u v x y z ≤ G :=
  sup_le (sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr huv))
    ((SimpleGraph.edge_le_iff G).mpr (Or.inr hux)))
    ((SimpleGraph.edge_le_iff G).mpr (Or.inr hyz))

end Gallai
