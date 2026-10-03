/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.PendantExtension
public import Gallai.Operations.DecompositionMap

@[expose] public section

/-! # Common carrier space for Xie's odd/odd hub-cut auxiliaries

Xie's Claim 1, Case 2.2 attaches a fresh pendant leaf at the shared hub on
each of two cut pieces.  Each recursive auxiliary must remain connected on its
own `V ⊕ Unit` type.  When their decompositions are spliced, however, the two
fresh leaves must be distinct.  This file supplies only that type-correct
transport into `V ⊕ Bool`; it does not assert connectedness after transport
(the unused Boolean leaf is isolated), and it contains no reconstruction.
-/

namespace Gallai

universe u

variable {V : Type u}

/-- Embed a pendant extension as the `false`-leaf copy of a common two-leaf
carrier space. -/
def leftPendantEmbedding : V ⊕ Unit ↪ V ⊕ Bool where
  toFun
    | .inl v => .inl v
    | .inr _ => .inr false
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp_all

/-- Embed a pendant extension as the `true`-leaf copy of a common two-leaf
carrier space. -/
def rightPendantEmbedding : V ⊕ Unit ↪ V ⊕ Bool where
  toFun
    | .inl v => .inl v
    | .inr _ => .inr true
  inj' := by
    intro a b hab
    cases a <;> cases b <;> simp_all

/-- The left pendant graph, viewed in the common two-leaf carrier space. -/
abbrev twoPendantLeft (G : SimpleGraph V) (h : V) : SimpleGraph (V ⊕ Bool) :=
  G.map (Function.Embedding.inl : V ↪ V ⊕ Bool) ⊔
    SimpleGraph.edge (.inl h) (.inr false)

/-- The right pendant graph, viewed in the common two-leaf carrier space. -/
abbrev twoPendantRight (G : SimpleGraph V) (h : V) : SimpleGraph (V ⊕ Bool) :=
  G.map (Function.Embedding.inl : V ↪ V ⊕ Bool) ⊔
    SimpleGraph.edge (.inl h) (.inr true)

private theorem map_sup_embedding {U W : Type*} (f : U ↪ W)
    (A B : SimpleGraph U) :
    (A ⊔ B).map f = A.map f ⊔ B.map f := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  aesop

private theorem map_edge_embedding {U W : Type*} (f : U ↪ W) (a b : U) :
    (SimpleGraph.edge a b).map f = SimpleGraph.edge (f a) (f b) := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.edge_adj]
  aesop

/-- Mapping the connected one-leaf auxiliary by the left embedding produces
exactly its false-leaf representation. -/
theorem map_pendantExtension_left (G : SimpleGraph V) (h : V) :
    (pendantExtension G h).map leftPendantEmbedding = twoPendantLeft G h := by
  rw [pendantExtension, map_sup_embedding, map_edge_embedding, SimpleGraph.map_map]
  rfl

/-- Mapping the connected one-leaf auxiliary by the right embedding produces
exactly its true-leaf representation. -/
theorem map_pendantExtension_right (G : SimpleGraph V) (h : V) :
    (pendantExtension G h).map rightPendantEmbedding = twoPendantRight G h := by
  rw [pendantExtension, map_sup_embedding, map_edge_embedding, SimpleGraph.map_map]
  rfl

/-- The two transported fresh leaves are distinct. -/
theorem two_pendant_fresh_leaves_ne (h : V) :
    (.inr false : V ⊕ Bool) ≠ .inr true := by
  simp

/-- A decomposition transported into the false-leaf carrier space preserves
both its path count and every old endpoint count. -/
theorem Decomposition.map_left_pendant_size_endpoints [DecidableEq V]
    (G : SimpleGraph V) (h : V) (D : Decomposition (pendantExtension G h)) :
    (D.map leftPendantEmbedding).size = D.size ∧
      ∀ v : V, (D.map leftPendantEmbedding).endpointCount (.inl v) =
        D.endpointCount (.inl v) := by
  refine ⟨D.map_size leftPendantEmbedding, ?_⟩
  intro v
  change (D.map leftPendantEmbedding).endpointCount
      (leftPendantEmbedding (.inl v)) = D.endpointCount (.inl v)
  exact D.map_endpointCount leftPendantEmbedding (.inl v)

/-- The analogous transport statement for the true-leaf carrier space. -/
theorem Decomposition.map_right_pendant_size_endpoints [DecidableEq V]
    (G : SimpleGraph V) (h : V) (D : Decomposition (pendantExtension G h)) :
    (D.map rightPendantEmbedding).size = D.size ∧
      ∀ v : V, (D.map rightPendantEmbedding).endpointCount (.inl v) =
        D.endpointCount (.inl v) := by
  refine ⟨D.map_size rightPendantEmbedding, ?_⟩
  intro v
  change (D.map rightPendantEmbedding).endpointCount
      (rightPendantEmbedding (.inl v)) = D.endpointCount (.inl v)
  exact D.map_endpointCount rightPendantEmbedding (.inl v)

end Gallai
