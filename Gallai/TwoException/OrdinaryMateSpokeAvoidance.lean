/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationExistence
public import Gallai.TwoException.OrdinaryMateSelection

@[expose] public section

/-! # Global mate avoidance from original component separation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance mateSpokeComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Local avoidance extends to the entire selected spoke family because
every other packet lies in a different original even component. -/
theorem ordinary_component_vertex_avoids_spoke_union
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (C : (evenSubgraph G).ConnectedComponent) (t : evenVertices G)
    (htC : t ∈ C.supp) (hlocal : t ∉ P C) :
    (t : V) ∉ (F.biUnion P).image Subtype.val := by
  classical
  intro ht
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ht
  have hvt : v = t := Subtype.val_injective he
  subst v
  obtain ⟨D,hD,htD⟩ := Finset.mem_biUnion.mp hv
  have hDC : D = C := SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (hsupp D hD t htD) htC
  subst D
  exact hlocal htD

/-- Every selected local mate avoids all ordinary spokes and an additional
hub spoke whose hub is outside that original component. -/
theorem ordinary_mates_avoid_assembled_spokes
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (M : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hmates : ∀ C ∈ F, ∀ e ∈ M C,
      e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (x : evenVertices G) (hx : ∀ C ∈ F, x ∉ C.supp) :
    ∀ C ∈ F, ∀ e ∈ M C,
      (e.1 : V) ∉ insert (x : V) ((F.biUnion P).image Subtype.val) ∧
      (e.2 : V) ∉ insert (x : V) ((F.biUnion P).image Subtype.val) := by
  classical
  intro C hC e he
  obtain ⟨hl,hr,hlP,hrP⟩ := hmates C hC e he
  have hlX : (e.1 : V) ≠ x := by
    intro h
    have heq : e.1 = x := Subtype.val_injective h
    exact hx C hC (heq ▸ hl)
  have hrX : (e.2 : V) ≠ x := by
    intro h
    have heq : e.2 = x := Subtype.val_injective h
    exact hx C hC (heq ▸ hr)
  have hlU := ordinary_component_vertex_avoids_spoke_union G F P hsupp C e.1 hl hlP
  have hrU := ordinary_component_vertex_avoids_spoke_union G F P hsupp C e.2 hr hrP
  simp only [Finset.mem_insert, not_or]
  exact ⟨⟨hlX,hlU⟩,⟨hrX,hrU⟩⟩

end Gallai.TwoException
