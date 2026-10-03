/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Gallai.Foundations.Endpoints

@[expose] public section

/-! # Reversing a decomposition without changing edge ownership or endpoints -/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Reverse every carrier while retaining its index and its unordered edges. -/
def reverse (D : Decomposition G) : Decomposition G where
  size := D.size
  path := fun i => (D.path i).reverse
  covers := by
    intro e he
    simpa only [NonemptyPath.reverse_edges, List.mem_reverse] using D.covers e he

/-- Reversing orientations does not change the path count. -/
@[simp] theorem reverse_size (D : Decomposition G) : D.reverse.size = D.size := rfl

/-- Reversing orientations does not change any endpoint multiplicity. -/
@[simp] theorem reverse_endpointCount [DecidableEq V] (D : Decomposition G) (v : V) :
    D.reverse.endpointCount v = D.endpointCount v := by
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.add_comm _ _

end Gallai.Decomposition
