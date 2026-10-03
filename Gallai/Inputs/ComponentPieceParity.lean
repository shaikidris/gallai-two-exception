/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EvenComponentPieceUnion
public import Gallai.Inputs.EvenStarPuncture

@[expose] public section

/-! # Parity of the assembled component-piece puncture -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Adjacency decision for assembled deletion graphs. -/
noncomputable local instance deletionUnionAdj
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V) :
    DecidableRel (s.sup K).Adj := fun _ _ => Classical.propDecidable _

/-- Assembling supported component pieces preserves the off-hub parity
interface needed by the even-leaf Fan theorem. -/
theorem component_piece_puncture_parity
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V)
    [∀ C, DecidableRel (K C).Adj] (u : V)
    (hle : ∀ C ∈ s, K C ≤ G)
    (hs : ∀ C ∈ s, ∀ v w, (K C).Adj v w → v = u ∨ v ∈ evenComponentVertices C)
    (hl : ∀ C ∈ s, ∀ v, v ≠ u → (K C).degree v ≤ 1) :
    (∀ v, v ≠ u → 0 < (s.sup K).degree v → Odd ((G \ s.sup K).degree v)) ∧
    (∀ v, v ≠ u → Even ((G \ s.sup K).degree v) → Even (G.degree v)) := by
  exact even_star_puncture_parity (Finset.sup_le hle) u
    (even_component_piece_union_degree_le_one s K u hs hl)
    (even_component_piece_union_active_even s K u hs)

/-- Covering every originally even hub neighbour by a deletion incidence
makes every retained hub neighbour odd in the puncture. A retained edge to
an originally even neighbour is allowed: its other removed edge changes parity. -/
theorem component_piece_puncture_centre
    (s : Finset (evenSubgraph G).ConnectedComponent)
    (K : (evenSubgraph G).ConnectedComponent → SimpleGraph V)
    [∀ C, DecidableRel (K C).Adj] (u : V)
    (hle : ∀ C ∈ s, K C ≤ G)
    (hs : ∀ C ∈ s, ∀ v w, (K C).Adj v w → v = u ∨ v ∈ evenComponentVertices C)
    (hl : ∀ C ∈ s, ∀ v, v ≠ u → (K C).degree v ≤ 1)
    (hcover : ∀ v, G.Adj u v → Even (G.degree v) → 0 < (s.sup K).degree v) :
    ∀ v, (G \ s.sup K).Adj u v → ¬ Even ((G \ s.sup K).degree v) := by
  intro v hv he
  have hvu := hv.ne.symm
  obtain ⟨ho, hk⟩ := component_piece_puncture_parity s K u hle hs hl
  exact (Nat.not_even_iff_odd.mpr (ho v hvu (hcover v hv.1 (hk v hvu he)))) he

end Gallai
