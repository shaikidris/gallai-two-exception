/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.HubPieceUnion
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # Deletion-piece assembly over actual even components -/

namespace Gallai

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Distinct actual even components have disjoint original vertex sets. -/
theorem evenComponentVertices_disjoint (C D : (evenSubgraph G).ConnectedComponent)
    (hCD : C ≠ D) : Disjoint (evenComponentVertices C) (evenComponentVertices D) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, heq⟩ := hw
  have hba : b = a := Subtype.ext heq
  subst b
  exact Set.disjoint_left.mp
    ((evenSubgraph G).pairwise_disjoint_supp_connectedComponent hCD) ha hb

/-- Decision instance for a finite union of component pieces. -/
noncomputable local instance componentPiecesAdj
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V) :
    DecidableRel (s.sup K).Adj := fun _ _ => Classical.propDecidable _

/-- Off-hub degree-one bounds survive assembly over actual even components.
The separation is derived from connected components, not assumed by callers. -/
theorem even_component_piece_union_degree_le_one
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V)
    [∀ C, DecidableRel (K C).Adj] (u : V)
    (hs : ∀ C ∈ s, ∀ v w, (K C).Adj v w → v = u ∨ v ∈ evenComponentVertices C)
    (hl : ∀ C ∈ s, ∀ v, v ≠ u → (K C).degree v ≤ 1)
    (v : V) (hvu : v ≠ u) : (s.sup K).degree v ≤ 1 := by
  exact hub_piece_union_degree_le_one s K evenComponentVertices u
    (fun C _ D _ hCD => evenComponentVertices_disjoint C D hCD) hs hl v hvu

/-- Every active non-hub vertex in the assembled deletion is originally even. -/
theorem even_component_piece_union_active_even
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V) (u : V)
    (hs : ∀ C ∈ s, ∀ v w, (K C).Adj v w → v = u ∨ v ∈ evenComponentVertices C)
    (v : V) (hvu : v ≠ u) (hv : 0 < (s.sup K).degree v) : Even (G.degree v) := by
  obtain ⟨w, hw⟩ := ((s.sup K).degree_pos_iff_exists_adj v).mp hv
  rw [Finset.sup_eq_iSup] at hw
  simp only [SimpleGraph.iSup_adj] at hw
  obtain ⟨C, hC, h⟩ := hw
  exact even_of_mem_evenComponent C ((hs C hC v w h).resolve_left hvu)

end Gallai
