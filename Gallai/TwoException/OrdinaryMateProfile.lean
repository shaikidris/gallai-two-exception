/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMateDegree

@[expose] public section

/-! # Odd boundary witnesses for every ordinary mate -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mateOddAdj (G : SimpleGraph V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture G M).Adj := fun _ _ => Classical.propDecidable _

/-- Every originally even mate endpoint is odd after the entire family
of disjoint mate deletions, regardless of family size. -/
theorem ordinaryMatePuncture_endpoints_odd
    (M : List (V × V))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ e ∈ M, Odd ((ordinaryMatePuncture G M).degree e.1) ∧
      Odd ((ordinaryMatePuncture G M).degree e.2) := by
  intro e he
  obtain ⟨hp, hq⟩ := ordinaryMatePuncture_endpoint_degree (G := G) M hdis
    (fun f hf => (hedges f hf).1) e he
  obtain ⟨_, hep, heq⟩ := hedges e he
  simp only [← SimpleGraph.ncard_neighborSet] at hp hq hep heq ⊢
  rw [Nat.even_iff] at hep heq
  constructor <;> rw [Nat.odd_iff] <;> omega

end Gallai.TwoException
