/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareMinimality
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-! # Shortest corridors in the even subgraph

The bare two-exception reduction chooses an E-degree-three vertex at minimum
distance from an exceptional hub in the induced even subgraph.  This file
records the first, purely metric, consequence: an internal vertex of the
chosen shortest corridor cannot itself have E-degree three.

This is intentionally independent of the deletion and path-decomposition
machinery.  Later corridor auxiliaries may consume it without inheriting a
particular puncture representation.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Regard an even-subgraph corridor as a walk in the ambient graph. -/
def shortestEvenCorridorLift {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) : G.Walk (x : V) (a : V) :=
  p.map (evenSubgraphInclusion G)

@[simp] theorem shortestEvenCorridorLift_length {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) :
    (shortestEvenCorridorLift p).length = p.length := by
  change (p.map (evenSubgraphInclusion G)).length = p.length
  exact SimpleGraph.Walk.length_map (f := evenSubgraphInclusion G) p

@[simp] theorem shortestEvenCorridorLift_getVert {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) (i : ℕ) :
    (shortestEvenCorridorLift p).getVert i = (p.getVert i : V) := by
  change (p.map (evenSubgraphInclusion G)).getVert i = (p.getVert i : V)
  rw [SimpleGraph.Walk.getVert_map]
  rfl

theorem shortestEvenCorridorLift_isPath {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath) :
    (shortestEvenCorridorLift p).IsPath := by
  exact (SimpleGraph.Walk.isPath_map_iff_of_injective
    (f := evenSubgraphInclusion G) (p := p) Subtype.val_injective).mpr hp

/-- Every ambient vertex on a lifted even-subgraph corridor has even degree
in the original graph.  This packages the subtype membership carried by the
even-subgraph walk in the form consumed by auxiliary parity arguments. -/
theorem shortestEvenCorridorLift_support_even {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) (w : V)
    (hw : w ∈ (shortestEvenCorridorLift p).support) :
    Even (G.degree w) := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
  obtain ⟨i, hi, _⟩ := hw
  rw [shortestEvenCorridorLift_getVert] at hi
  rw [← hi]
  exact (p.getVert i).property

/-- Every vertex of a lifted corridor is either an endpoint or is represented
by a proper internal index.  This is the support-entry trichotomy consumed by
corridor-auxiliary component arguments. -/
theorem shortestEvenCorridorLift_support_cases {x a : evenVertices G}
    (p : (evenSubgraph G).Walk x a) {z : V}
    (hz : z ∈ (shortestEvenCorridorLift p).support) :
    z = x ∨ z = a ∨ ∃ i : ℕ, 0 < i ∧ i < p.length ∧ z = (p.getVert i : V) := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨i, hi, hile⟩ := hz
  rw [shortestEvenCorridorLift_getVert] at hi
  by_cases hi0 : i = 0
  · left
    subst i
    simpa using hi.symm
  by_cases hilast : i = p.length
  · right; left
    subst i
    simpa using hi.symm
  · right; right
    refine ⟨i, Nat.pos_of_ne_zero hi0, ?_, hi.symm⟩
    exact Nat.lt_of_le_of_ne (by simpa using hile) hilast

/-- If `a` is a closest E-degree-three even vertex to `x`, then an internal
vertex of a shortest even-subgraph path from `x` to `a` does not have
E-degree three. -/
theorem shortest_even_corridor_internal_not_eDegree_three
    (x a : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (i : ℕ) (hiend : i < p.length) :
    eDegree G (p.getVert i : V) ≠ 3 := by
  intro hthree
  have hprefix : (evenSubgraph G).dist x (p.getVert i) ≤ i := by
    calc
      (evenSubgraph G).dist x (p.getVert i) ≤ (p.take i).length :=
        SimpleGraph.dist_le (p.take i)
      _ = i := by
        rw [SimpleGraph.Walk.take_length, min_eq_left (Nat.le_of_lt hiend)]
  have hmin := hclosest (p.getVert i) (p.take i).reachable hthree
  rw [← hdist] at hmin
  omega

/-- An internal position of a simple even-subgraph path has two distinct
even neighbours: its predecessor and successor on the path. -/
theorem shortest_even_corridor_internal_eDegree_ge_two
    [DecidableEq V]
    (x a : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hp : p.IsPath)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    2 ≤ eDegree G (p.getVert i : V) := by
  let u : evenVertices G := p.getVert (i - 1)
  let v : evenVertices G := p.getVert (i + 1)
  have hu_adj : (evenSubgraph G).Adj u (p.getVert i) := by
    dsimp [u]
    have hpred : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)
    rw [← hpred]
    exact p.adj_getVert_succ (i := i - 1) (by omega)
  have hv_adj : (evenSubgraph G).Adj (p.getVert i) v := by
    dsimp [v]
    exact p.adj_getVert_succ (i := i) hiend
  have huv : u ≠ v := by
    intro huv
    have hindices : i - 1 = i + 1 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) (by simpa [u, v] using huv)
    omega
  have huv_val : (u : V) ≠ v := by
    intro e
    apply huv
    exact Subtype.ext e
  have hu_mem : (u : V) ∈ evenNeighbors G (p.getVert i : V) := by
    apply (mem_evenNeighbors (G := G) (p.getVert i : V) (u : V)).mpr
    exact ⟨hu_adj.symm, u.property⟩
  have hv_mem : (v : V) ∈ evenNeighbors G (p.getVert i : V) := by
    apply (mem_evenNeighbors (G := G) (p.getVert i : V) (v : V)).mpr
    exact ⟨hv_adj, v.property⟩
  have hsubset : ({(u : V), (v : V)} : Finset V) ⊆
      evenNeighbors G (p.getVert i : V) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu_mem
    · exact hv_mem
  have hpair : ({(u : V), (v : V)} : Finset V).card = 2 := by
    simp [huv_val]
  have hle := Finset.card_le_card hsubset
  rw [hpair] at hle
  exact hle

/-- In the bare minimal-counterexample stage, an internal vertex of a
shortest corridor to a closest E-degree-three vertex has E-degree exactly
two.  The lower bound comes from the two path neighbours; the upper bound is
the bare cap after excluding the two designated vertices. -/
theorem shortest_even_corridor_internal_eDegree_eq_two_of_bare
    [DecidableEq V]
    (h : V) (x a : evenVertices G)
    (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    eDegree G (p.getVert i : V) = 2 := by
  have hge := shortest_even_corridor_internal_eDegree_ge_two x a p hp i hi hiend
  have hnot := shortest_even_corridor_internal_not_eDegree_three x a p hdist hclosest i hiend
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hbare, hcap⟩
  have hzx : (p.getVert i : V) ≠ x := by
    intro hz
    have hpath_eq : p.getVert i = p.getVert 0 := by
      apply Subtype.ext
      simpa using hz
    have hindex_eq : i = 0 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) hpath_eq
    omega
  have hzh : (p.getVert i : V) ≠ h := by
    intro hz
    subst h
    rw [hbare] at hge
    omega
  have hle : eDegree G (p.getVert i : V) ≤ 3 :=
    hcap _ (p.getVert i).property hzh hzx
  omega

/-- A shortest even-subgraph corridor has no chord from its start to a
position at distance at least two.  The chord followed by the remaining tail
would otherwise be a shorter walk from the start to the terminal. -/
theorem shortest_even_corridor_start_not_adj_getVert
    (x a : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (j : ℕ) (hj : 1 < j) (hjle : j ≤ p.length) :
    ¬ (evenSubgraph G).Adj x (p.getVert j) := by
  intro hadj
  have hshort : (evenSubgraph G).dist x a ≤
      (hadj.toWalk.append (p.drop j)).length :=
    SimpleGraph.dist_le (hadj.toWalk.append (p.drop j))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk,
    SimpleGraph.Walk.drop_length, ← hdist] at hshort
  omega

/-- A distance-realizing corridor has no forward chord between two positions
separated by an intervening path edge.  This is the local geodesic fact needed
when a later restoration must remain invisible to all earlier restored
corridor edges. -/
theorem shortest_even_corridor_not_adj_getVert
    (x a : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (i j : ℕ) (hgap : i + 1 < j) (hjle : j ≤ p.length) :
    ¬ (evenSubgraph G).Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hile : i ≤ p.length := by omega
  have hshort : (evenSubgraph G).dist x a ≤
      ((p.take i).append (hadj.toWalk.append (p.drop j))).length :=
    SimpleGraph.dist_le ((p.take i).append (hadj.toWalk.append (p.drop j)))
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_append,
    SimpleGraph.Adj.length_toWalk, SimpleGraph.Walk.take_length,
    min_eq_left hile, SimpleGraph.Walk.drop_length, ← hdist] at hshort
  omega

/-- An even neighbour of the terminal vertex of a shortest corridor cannot
occur at a proper internal corridor position: adjoining that edge would give
a shorter walk to the terminal. -/
theorem shortest_even_corridor_terminal_neighbor_not_internal
    (x a q : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hqa : (evenSubgraph G).Adj q a)
    (i : ℕ) (hi : 0 < i) (hilast : i + 1 < p.length) :
    p.getVert i ≠ q := by
  intro hiq
  have hshort : (evenSubgraph G).dist x a ≤
      ((p.take i).append (hiq ▸ hqa).toWalk).length :=
    SimpleGraph.dist_le ((p.take i).append (hiq ▸ hqa).toWalk)
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk,
    SimpleGraph.Walk.take_length, min_eq_left (by omega)] at hshort
  rw [← hdist] at hshort
  omega

/-- A terminal even neighbour of a shortest corridor is outside the ambient
corridor unless it is the predecessor of the terminal.  This is the exact
separation fact needed to choose the two extra leaves at an E-degree-three
terminal. -/
theorem shortest_even_corridor_terminal_neighbor_not_mem_support
    [DecidableEq V]
    (x a q : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hqa : (evenSubgraph G).Adj q a) (hlen : 1 < p.length)
    (hqpred : p.getVert (p.length - 1) ≠ q) :
    (q : V) ∉ (shortestEvenCorridorLift p).support := by
  intro hq
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hq
  obtain ⟨i, hi, hile⟩ := hq
  rw [shortestEvenCorridorLift_getVert] at hi
  have hqx : q ≠ x := by
    intro h
    subst q
    have hle : (evenSubgraph G).dist x a ≤ hqa.toWalk.length :=
      SimpleGraph.dist_le hqa.toWalk
    rw [SimpleGraph.Adj.length_toWalk, ← hdist] at hle
    omega
  have hqa' : q ≠ a := hqa.ne
  by_cases hi0 : i = 0
  · subst i
    rw [p.getVert_zero] at hi
    exact hqx (Subtype.ext hi.symm)
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  by_cases hilast : i = p.length
  · subst i
    rw [p.getVert_length] at hi
    exact hqa' (Subtype.ext hi.symm)
  have hile' : i ≤ p.length := by simpa using hile
  have hilt : i < p.length := Nat.lt_of_le_of_ne hile' hilast
  by_cases hipred : i = p.length - 1
  · subst i
    exact hqpred (Subtype.ext hi)
  have hbefore : i + 1 < p.length := by omega
  have hnot := shortest_even_corridor_terminal_neighbor_not_internal
    x a q p hdist hqa i hipos hbefore
  exact hnot (Subtype.ext hi)

end Gallai.TwoException
