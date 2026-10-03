/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Decomposition
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Endpoint counting

The sum formula counts the two ends of each nonempty path. The degree-parity
identity is derived separately in Gallai.Foundations.Parity, not assumed here.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Number of paths of the decomposition ending at a vertex. -/
def Decomposition.endpointCount (D : Decomposition G) (v : V) : ℕ :=
  ∑ i : Fin D.size,
    ((if (D.path i).start = v then 1 else 0) +
     (if (D.path i).finish = v then 1 else 0))

/-- Each path contributes exactly two endpoint incidences. -/
theorem Decomposition.sum_endpointCount [Fintype V] (D : Decomposition G) :
    ∑ v : V, D.endpointCount v = 2 * D.size := by
  simp only [endpointCount]
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib, eq_comm, Nat.mul_comm]

end Gallai
