/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Even-vertex count and graph-order parity

This elementary handshaking consequence supplies the order-parity fact
needed for SET exclusion. It does not assert a path-decomposition theorem.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of even-degree vertices has the parity of the graph order. -/
theorem even_vertex_count_mod_two :
    (#{v : V | Even (G.degree v)}) % 2 = Fintype.card V % 2 := by
  have hcount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (fun v => Even (G.degree v))
  simp only [Nat.not_even_iff_odd, Finset.card_univ] at hcount
  have hodd := Nat.even_iff.mp G.even_card_odd_degree_vertices
  omega

/-- Exactly three even-degree vertices force odd order, independently of SET structure. -/
theorem odd_order_of_three_even_vertices (h : #{v : V | Even (G.degree v)} = 3) :
    Odd (Fintype.card V) := by
  have hp := even_vertex_count_mod_two G
  rw [h] at hp
  rw [Nat.odd_iff]
  omega

/-- An even-order graph cannot have exactly the three even vertices required by a SET graph. -/
theorem even_order_ne_three_even_vertices (h : Even (Fintype.card V)) :
    #{v : V | Even (G.degree v)} ≠ 3 := by
  have hp := even_vertex_count_mod_two G
  rw [Nat.even_iff] at h
  omega

end Gallai
