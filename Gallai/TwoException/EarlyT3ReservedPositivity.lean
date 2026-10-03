/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTriangleComponent

@[expose] public section

/-! # Retained-neighbour positivity at the T3 reserved endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3ReservedAux (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- In the actual T3 contact puncture, all retained neighbours of the
reserved triangle vertex are odd. Its original even neighbours are exactly
the two mate ends, both flipped by deleting the opposite edge. -/
theorem t3_reserved_neighbours_odd
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c) :
    ∀ t, ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).Adj a t →
      Odd (((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).degree t) := by
  classical
  obtain ⟨hprofile,hbOdd,hcOdd⟩ := ordinary_triangle_puncture_profile u b c B
    hadj hleaves hbu hcu hbB hcB hbc b.property c.property
  have hs : Z.supp = {b,a,c} := by
    rw [hsupp]
    ext t
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  intro t hat
  by_contra hn
  have he := (Nat.even_or_odd
    (((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).degree t)).resolve_right hn
  rcases hprofile t he with heG | htu
  · rcases triangle_component_even_neighbors Z b a c hs t hat.1.1 heG with htb | htc
    · subst t
      simp only [← SimpleGraph.ncard_neighborSet] at hn hbOdd
      exact hn hbOdd
    · subst t
      simp only [← SimpleGraph.ncard_neighborSet] at hn hcOdd
      exact hn hcOdd
  · subst t
    have hmissing : ¬ (starPuncture G u B).Adj u a := by
      have huB : u ∉ B := fun hu => G.irrefl (hadj u hu)
      intro hua
      exact hua.2 ((star_sup_adj_center u B huB a).mpr haB)
    exact hmissing hat.1.symm

/-- Every decomposition of that puncture supplies the reserved-endpoint
neighbour positivity required by contact restoration. -/
theorem t3_reserved_neighbours_positive
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c)
    (D : Decomposition ((starPuncture G u B).deleteEdges {s((b : V),(c : V))})) :
    ∀ t, ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).Adj a t →
      0 < D.endpointCount t := by
  intro t ht
  exact D.endpointCount_pos_of_odd_degree t
    (t3_reserved_neighbours_odd Z a b c hsupp u B hadj hleaves haB
      hbu hcu hbB hcB hbc t ht)

end Gallai.TwoException
