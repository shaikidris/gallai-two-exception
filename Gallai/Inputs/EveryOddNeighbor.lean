/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FullTriangleClaim

@[expose] public section

/-! # Every odd vertex has an even neighbour

Claim 7 propagates an even-neighbour witness through the connected graph.
The previously proved triangle structure makes it a triangle neighbour.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Source Claim 8: every odd vertex touches the even subgraph under the
strict minimal-counterexample guards. Its components are already triangles. -/
theorem minimal_counterexample_odd_has_even_neighbor
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (v : V) (hv : Odd (G.degree v)) :
    ∃ w, G.Adj v w ∧ Even (G.degree w) := by
  classical
  have hex : ∃ a, Even (G.degree a) := by
    by_contra hn
    apply hnot
    apply pathBudget_of_at_most_one_even G
    intro a ha b hb
    exact (hn ⟨a, ha⟩).elim
  let R := fun a => Even (G.degree a) ∨ ∃ w, G.Adj a w ∧ Even (G.degree w)
  have hstep (a b : V) (hab : G.Adj a b) (ha : R a) : R b := by
    by_cases hb : Even (G.degree b)
    · exact Or.inl hb
    apply Or.inr
    rcases ha with ha | ⟨w, haw, hw⟩
    · exact ⟨a, hab.symm, ha⟩
    · let q : evenVertices G := ⟨w, hw⟩
      let C := (evenSubgraph G).connectedComponentMk q
      have hqC : q ∈ C.supp := by simp [C, SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact minimal_counterexample_odd_neighbor_has_even_neighbor a b
        (Nat.not_even_iff_odd.mp hb) hab hconn hcap hnot hset hmin C ⟨q, hqC, haw⟩
  have hwalk : ∀ {a b : V}, G.Walk a b → R a → R b := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b c hab p ih => exact fun ha => ih (hstep a b hab ha)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨p⟩ := hconn.preconnected a v
  rcases hwalk p (Or.inl ha) with he | he
  · exact (Nat.not_even_iff_odd.mpr hv he).elim
  · exact he

end Gallai
