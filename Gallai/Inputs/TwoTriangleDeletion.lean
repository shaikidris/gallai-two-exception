/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ActiveOddPuncture

@[expose] public section

/-! # The two-triangle deletion template

Vertices 0 and 1 are the hubs. Each adjacent triangle contributes either
all three hub spokes or one spoke and its opposite triangle edge.
-/

namespace Gallai

/-- The five-, six-, or seven-edge deletion used in Claim 10 and the endgame. -/
abbrev twoTriangleTemplate (leftFull rightFull : Bool) : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet
    (↑({s(0, 1), s(0, 2), s(1, 5)} ∪
      (if leftFull then {s(0, 3), s(0, 4)} else {s(3, 4)}) ∪
      (if rightFull then {s(1, 6), s(1, 7)} else {s(6, 7)}) :
      Finset (Sym2 (Fin 8))))

/-- Both hubs lose an even number of edges; each of the six leaves loses one. -/
theorem twoTriangleTemplate_degree (leftFull rightFull : Bool) (i : Fin 8) :
    (twoTriangleTemplate leftFull rightFull).degree i =
      if i = 0 then (if leftFull then 4 else 2)
      else if i = 1 then (if rightFull then 4 else 2) else 1 := by
  cases leftFull <;> cases rightFull <;> fin_cases i <;> decide

/-- The hub edge and a spoke at each hub are present in every mode. -/
theorem twoTriangleTemplate_required (leftFull rightFull : Bool) :
    (twoTriangleTemplate leftFull rightFull).Adj 0 1 ∧
    (twoTriangleTemplate leftFull rightFull).Adj 0 2 ∧
    (twoTriangleTemplate leftFull rightFull).Adj 1 5 := by
  cases leftFull <;> cases rightFull <;> decide

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Embed the eight distinct labels in an arbitrary ambient vertex set. -/
abbrev twoTriangleDeletion (leftFull rightFull : Bool) (f : Fin 8 ↪ V) : SimpleGraph V :=
  (twoTriangleTemplate leftFull rightFull).map f

instance (leftFull rightFull : Bool) (f : Fin 8 ↪ V) :
    DecidableRel (twoTriangleDeletion leftFull rightFull f).Adj := fun a b =>
  decidable_of_iff (∃ i j : Fin 8,
    (twoTriangleTemplate leftFull rightFull).Adj i j ∧ f i = a ∧ f j = b)
    (SimpleGraph.map_adj f (twoTriangleTemplate leftFull rightFull) a b).symm

/-- Embedding preserves the exact deleted degree at every template vertex. -/
theorem twoTriangleDeletion_degree (leftFull rightFull : Bool) (f : Fin 8 ↪ V)
    (i : Fin 8) :
    (twoTriangleDeletion leftFull rightFull f).degree (f i) =
      (twoTriangleTemplate leftFull rightFull).degree i := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
    ← Set.ncard_eq_toFinset_card', twoTriangleDeletion, SimpleGraph.neighborSet_map]
  exact Set.ncard_image_of_injective _ f.injective

/-- An active deleted vertex is one of the actual eight labels. -/
theorem twoTriangleDeletion_active_image (leftFull rightFull : Bool) (f : Fin 8 ↪ V)
    (w : V) (hw : 0 < (twoTriangleDeletion leftFull rightFull f).degree w) :
    ∃ i, f i = w := by
  obtain ⟨t, ht⟩ := (SimpleGraph.degree_pos_iff_exists_adj _ _).mp hw
  obtain ⟨i, j, _, hi, _⟩ := (SimpleGraph.map_adj f _ w t).mp ht
  exact ⟨i, hi⟩

end Gallai
