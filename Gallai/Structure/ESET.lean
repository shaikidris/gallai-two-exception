/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SET
public import Mathlib.Combinatorics.SimpleGraph.Operations

@[expose] public section

/-! # Extended single even triangle graphs with a connection vertex

The two alternatives are structural: a SET graph, or its one-vertex extension
by edges to one odd and one even core vertex. No decomposition is assumed.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The literal two-case ESET definition at its permitted connection vertex.
The type-ii core is the graph induced away from that vertex. -/
def IsESETAt (z : V) : Prop :=
  IsSET G ∨
    (IsSET (G.induce {v | v ≠ z}) ∧
      ∃ x y : {v : V // v ≠ z},
        Odd ((G.induce {v | v ≠ z}).degree x) ∧
        Even ((G.induce {v | v ≠ z}).degree y) ∧
        G = (((G.induce {v | v ≠ z}).map (Function.Embedding.subtype _) ⊔
          SimpleGraph.edge z x.val) ⊔ SimpleGraph.edge z y.val))

variable {G}

/-- Every vertex of a SET graph is a permitted ESET connection. -/
theorem IsSET.isESETAt (h : IsSET G) (z : V) : IsESETAt G z := Or.inl h

end Gallai
