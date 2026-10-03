/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTriangleRestoration

@[expose] public section

/-! # Component-derived ordinary triangle restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance componentMateAdj (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A whole three-vertex even component has no additional even neighbour
at any of its vertices. The conclusion is in the original ambient graph. -/
theorem triangle_component_even_neighbors
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) :
    ∀ t, G.Adj b t → Even (G.degree t) → t = (a : V) ∨ t = (c : V) := by
  intro t hbt ht
  let te : evenVertices G := ⟨t, ht⟩
  have hb : b ∈ C.supp := by rw [hsupp]; simp
  have htC : te ∈ C.supp := C.mem_supp_of_adj_mem_supp hb hbt
  rw [hsupp] at htC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htC
  rcases htC with ha | hb | hc
  · exact Or.inl (congrArg Subtype.val ha)
  · have he : t = (b : V) := congrArg Subtype.val hb
    exact False.elim (G.irrefl (he ▸ hbt))
  · exact Or.inr (congrArg Subtype.val hc)

/-- The literal mate restoration for a whole ordinary triangle derives
its original even-neighbourhood and parity guards from component support
and deletion data. Only the schedule's centre reserve remains explicit. -/
theorem restore_ordinary_triangle_component_mate
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hab : (a : V) ≠ b) (hac : (a : V) ≠ c)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c)
    (D : Decomposition ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}))
    (hcentre : ¬ ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).Adj b u ∨
      0 < D.endpointCount u) :
    ∃ E : Decomposition (((starPuncture G u B).deleteEdges {s((b : V),(c : V))}) ⊔
      SimpleGraph.edge (b : V) (c : V)), E.size = D.size ∧ 2 ≤ E.endpointCount b ∧
      ∀ t, E.endpointCount t + (if (c : V) = t then 1 else 0) =
        D.endpointCount t + if (b : V) = t then 1 else 0 := by
  exact restore_ordinary_triangle_puncture_mate u a b c B hadj hleaves haB hab hac
    hbu hcu hbB hcB hbc b.property c.property
    (triangle_component_even_neighbors C a b c hsupp) D hcentre

end Gallai.TwoException
