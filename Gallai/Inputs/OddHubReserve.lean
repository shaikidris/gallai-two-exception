/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.HalfStar
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-! # Odd-hub reserve after inward and outward star transformations

Botler--Sambinelli Lemma 9, retaining the actual successive decompositions.
-/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} [DecidableEq V]

/-- A star with no loop has precisely its leaf set as the hub neighbourhood. -/
theorem star_sup_adj_center (u : V) (B : Finset V) (hu : u ∉ B) (v : V) :
    (B.sup (SimpleGraph.edge u)).Adj u v ↔ v ∈ B := by
  induction B using Finset.induction with
  | empty => simp
  | @insert b B hb ih =>
    have hub : u ≠ b := fun h => hu (by simp [h])
    have huB : u ∉ B := fun h => hu (Finset.mem_insert_of_mem h)
    rw [Finset.sup_insert, SimpleGraph.sup_adj, ih huB]
    by_cases hv : v = b <;> simp [SimpleGraph.edge_adj, hub, hv]

variable [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Local adjacency decision for a restored finite star. -/
noncomputable local instance oddHubStarDecidableAdj (u : V) (B : Finset V) :
    DecidableRel (H ⊔ B.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restoring an absent star increases the hub degree by its number of leaves. -/
theorem degree_sup_missing_star (u : V) (B : Finset V) (hu : u ∉ B)
    (hm : ∀ v ∈ B, ¬ H.Adj u v) :
    (H ⊔ B.sup (SimpleGraph.edge u)).degree u = H.degree u + #B := by
  classical
  have hs : (H ⊔ B.sup (SimpleGraph.edge u)).neighborFinset u = H.neighborFinset u ∪ B := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj,
      star_sup_adj_center u B hu, Finset.mem_union]
  have hd : Disjoint (H.neighborFinset u) B := by
    apply Finset.disjoint_left.mpr
    intro v hv hb
    exact hm v hb ((H.mem_neighborFinset u v).mp hv)
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hs, Finset.card_union_of_disjoint hd,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Inward restoration of at least half an odd hub's missing star leaves
strictly more endpoints than residual edges, even after outward restoration. -/
theorem Decomposition.odd_hub_reserve (u : V) (B A₁ A₂ : Finset V)
    (hu : u ∉ B) (hm : ∀ v ∈ B, ¬ H.Adj u v)
    (hodd : Odd ((H ⊔ B.sup (SimpleGraph.edge u)).degree u))
    (h₁ : A₁ ⊆ B) (h₂ : A₂ ⊆ B) (hdis : Disjoint A₁ A₂) (hhalf : #B ≤ 2 * #A₁)
    (D₀ : Decomposition H)
    (D₁ : Decomposition (H ⊔ A₁.sup (SimpleGraph.edge u)))
    (D₂ : Decomposition ((H ⊔ A₁.sup (SimpleGraph.edge u)) ⊔ A₂.sup (SimpleGraph.edge u)))
    (hin : D₁.endpointCount u = D₀.endpointCount u + #A₁)
    (hout : D₂.endpointCount u + #A₂ = D₁.endpointCount u) :
    #(B \ (A₁ ∪ A₂)) < D₂.endpointCount u := by
  rw [degree_sup_missing_star H u B hu hm, Nat.odd_iff] at hodd
  have hp := D₀.endpointCount_mod_two u
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.union_subset h₁ h₂)
  rw [Finset.card_union_of_disjoint hdis] at hc
  omega

end Gallai
