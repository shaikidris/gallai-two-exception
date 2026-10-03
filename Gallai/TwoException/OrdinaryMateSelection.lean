/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMateProfile

@[expose] public section

/-! # Disjoint mate families from distinct even components -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Choosing one mate in each distinct even component automatically gives
the vertex-disjoint family required by simultaneous puncture parity. -/
theorem ordinary_component_mates_pairwise_disjoint
    {I : Type*} (M : List I)
    (component : I → (evenSubgraph G).ConnectedComponent)
    (left right : I → evenVertices G)
    (hunique : M.Pairwise (fun i j => component i ≠ component j))
    (hleft : ∀ i ∈ M, left i ∈ (component i).supp)
    (hright : ∀ i ∈ M, right i ∈ (component i).supp) :
    (M.map (fun i => ((left i : V), (right i : V)))).Pairwise
      (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by
  rw [List.pairwise_map]
  apply hunique.imp_of_mem
  intro i j hi hj hij
  have hne : ∀ v w : evenVertices G,
      v ∈ (component i).supp → w ∈ (component j).supp → (v : V) ≠ w := by
    intro v w hv hw he
    have heq : v = w := Subtype.ext he
    subst w
    exact hij (SimpleGraph.ConnectedComponent.eq_of_common_vertex hv hw)
  exact ⟨hne (left i) (left j) (hleft i hi) (hleft j hj),
    hne (left i) (right j) (hleft i hi) (hright j hj),
    hne (right i) (left j) (hright i hi) (hleft j hj),
    hne (right i) (right j) (hright i hi) (hright j hj)⟩

end Gallai.TwoException
