/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTrianglePrefix

@[expose] public section

/-! # The exact graph remaining after the three-edge prefix -/

namespace Gallai

private theorem map_sup_embedding {U V : Type*} (f : U ↪ V) (A B : SimpleGraph U) :
    (A ⊔ B).map f = A.map f ⊔ B.map f := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  aesop

private theorem map_edge_embedding {U V : Type*} (f : U ↪ V) (a b : U) :
    (SimpleGraph.edge a b).map f = SimpleGraph.edge (f a) (f b) := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨i, j, ⟨h, hn⟩, rfl, rfl⟩
    exact ⟨h.elim (fun ⟨h1, h2⟩ => Or.inl ⟨congrArg f h1, congrArg f h2⟩)
      (fun ⟨h1, h2⟩ => Or.inr ⟨congrArg f h1, congrArg f h2⟩), f.injective.ne hn⟩
  · rintro ⟨h, hn⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨a, b, ⟨Or.inl ⟨rfl, rfl⟩, fun h => hn (congrArg f h)⟩, rfl, rfl⟩
    · exact ⟨b, a, ⟨Or.inr ⟨rfl, rfl⟩, fun h => hn (congrArg f h)⟩, rfl, rfl⟩

/-- The left piece is either the full three-star or a spoke and an opposite edge. -/
abbrev twoTriangleLeftTemplate (leftFull : Bool) : SimpleGraph (Fin 8) :=
  if leftFull then
    SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 0 3 ⊔ SimpleGraph.edge 0 4
  else SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 3 4

/-- The three edges restored by the prefix are disjoint from the left piece. -/
theorem twoTriangleTemplate_split (leftFull : Bool) :
    twoTriangleTemplate leftFull false =
      (SimpleGraph.edge 6 7 ⊔ SimpleGraph.edge 1 5 ⊔ SimpleGraph.edge 0 1) ⊔
      twoTriangleLeftTemplate leftFull := by
  ext i j
  cases leftFull <;> fin_cases i <;> fin_cases j <;>
    simp only [twoTriangleLeftTemplate, Bool.false_eq_true, if_false, if_true,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj] <;> decide

variable {V : Type*}

/-- The full/full deletion is the hub edge together with both three-spoke stars. -/
theorem twoTriangleTemplate_full_split :
    twoTriangleTemplate true true = SimpleGraph.edge 0 1 ⊔
      (SimpleGraph.edge 0 2 ⊔ SimpleGraph.edge 0 3 ⊔ SimpleGraph.edge 0 4) ⊔
      (SimpleGraph.edge 1 5 ⊔ SimpleGraph.edge 1 6 ⊔ SimpleGraph.edge 1 7) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj] <;> decide

/-- Exact embedded seven-edge deletion, with the original anchor sets. -/
theorem twoTriangleDeletion_full_split [DecidableEq V] (f : Fin 8 ↪ V) :
    twoTriangleDeletion true true f = SimpleGraph.edge (f 0) (f 1) ⊔
      ({f 2, f 3, f 4} : Finset V).sup (SimpleGraph.edge (f 0)) ⊔
      ({f 5, f 6, f 7} : Finset V).sup (SimpleGraph.edge (f 1)) := by
  unfold twoTriangleDeletion
  rw [twoTriangleTemplate_full_split]
  simp only [map_sup_embedding, map_edge_embedding, Finset.sup_insert,
    Finset.sup_singleton, sup_assoc]

/-- The actual left piece in the ambient graph. -/
abbrev twoTriangleLeftDeletion (leftFull : Bool) (f : Fin 8 ↪ V) : SimpleGraph V :=
  (twoTriangleLeftTemplate leftFull).map f

/-- Exact decomposition of the ambient deletion into prefix and left piece. -/
theorem twoTriangleDeletion_split (leftFull : Bool) (f : Fin 8 ↪ V) :
    twoTriangleDeletion leftFull false f =
      (SimpleGraph.edge (f 6) (f 7) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
        SimpleGraph.edge (f 0) (f 1)) ⊔ twoTriangleLeftDeletion leftFull f := by
  unfold twoTriangleDeletion
  rw [twoTriangleTemplate_split]
  simp only [map_sup_embedding, map_edge_embedding, twoTriangleLeftDeletion]

/-- The remaining left piece has no edge in the already restored prefix. -/
theorem twoTriangleLeftDeletion_disjoint (leftFull : Bool) (f : Fin 8 ↪ V) :
    Disjoint (SimpleGraph.edge (f 6) (f 7) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
      SimpleGraph.edge (f 0) (f 1)) (twoTriangleLeftDeletion leftFull f) := by
  rw [disjoint_iff]
  apply bot_unique
  intro u v h
  obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj f _ u v).mp h.2
  have hp := h.1
  simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, f.injective.eq_iff] at hp
  cases leftFull <;> fin_cases i <;> fin_cases j <;>
    simp_all [twoTriangleLeftTemplate, SimpleGraph.sup_adj, SimpleGraph.edge_adj]

/-- Restoring the prefix leaves exactly the left-piece puncture, not a graph
that merely has the same degree parities. -/
theorem twoTrianglePrefix_graph (G : SimpleGraph V) (leftFull : Bool) (f : Fin 8 ↪ V)
    (hle : twoTriangleDeletion leftFull false f ≤ G) :
    ((G \ twoTriangleDeletion leftFull false f) ⊔ SimpleGraph.edge (f 6) (f 7)) ⊔
      SimpleGraph.edge (f 1) (f 5) ⊔ SimpleGraph.edge (f 0) (f 1) =
      G \ twoTriangleLeftDeletion leftFull f := by
  rw [twoTriangleDeletion_split] at hle ⊢
  have hd := twoTriangleLeftDeletion_disjoint leftFull f
  rw [disjoint_iff] at hd
  ext u v
  simp only [SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]
  have hi : ((SimpleGraph.edge (f 6) (f 7) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
      SimpleGraph.edge (f 0) (f 1)).Adj u v ∨
      (twoTriangleLeftDeletion leftFull f).Adj u v) → G.Adj u v := fun h => hle h
  have hn : ¬ ((SimpleGraph.edge (f 6) (f 7) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
      SimpleGraph.edge (f 0) (f 1)).Adj u v ∧
      (twoTriangleLeftDeletion leftFull f).Adj u v) := by
    intro h
    have h' : ((SimpleGraph.edge (f 6) (f 7) ⊔ SimpleGraph.edge (f 1) (f 5) ⊔
        SimpleGraph.edge (f 0) (f 1)) ⊓ twoTriangleLeftDeletion leftFull f).Adj u v := h
    rw [hd] at h'
    exact h'
  simp only [SimpleGraph.sup_adj] at hi hn
  tauto

/-- In full mode, the remaining piece is the three-spoke star. -/
theorem twoTriangleLeftDeletion_full [DecidableEq V] (f : Fin 8 ↪ V) :
    twoTriangleLeftDeletion true f =
      ({f 2, f 3, f 4} : Finset V).sup (SimpleGraph.edge (f 0)) := by
  simp only [twoTriangleLeftDeletion, twoTriangleLeftTemplate, if_true,
    map_sup_embedding, map_edge_embedding, Finset.sup_insert, Finset.sup_singleton]
  ac_rfl

/-- In partial mode, the remaining piece is one spoke and its opposite edge. -/
theorem twoTriangleLeftDeletion_partial (f : Fin 8 ↪ V) :
    twoTriangleLeftDeletion false f =
      SimpleGraph.edge (f 0) (f 2) ⊔ SimpleGraph.edge (f 3) (f 4) := by
  simp only [twoTriangleLeftDeletion, twoTriangleLeftTemplate, Bool.false_eq_true,
    if_false, map_sup_embedding, map_edge_embedding]

end Gallai
