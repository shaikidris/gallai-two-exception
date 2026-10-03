/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Union
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Assembly of finitely many edge-disjoint path budgets -/

namespace Gallai

/-- Pairwise edge-disjoint graphs assemble with the sum of their path budgets.
The empty family is allowed; no connectivity or positive-budget premise is needed. -/
theorem pathBudget_finset_sup {V I : Type*} (s : Finset I)
    (K : I → SimpleGraph V) (k : I → ℕ)
    (hd : (s : Set I).Pairwise fun i j => Disjoint (K i).edgeSet (K j).edgeSet)
    (hb : ∀ i ∈ s, HasPathBudget (K i) (k i)) :
    HasPathBudget (s.sup K) (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty_hasPathBudget (V := V))
  | @insert a s ha ih =>
    have hds : (s : Set I).Pairwise fun i j => Disjoint (K i).edgeSet (K j).edgeSet :=
      fun _ hi _ hj hij => hd (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨D, hD⟩ := hb a (Finset.mem_insert_self a s)
    obtain ⟨E, hE⟩ := ih hds (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have hdis : Disjoint (K a).edgeSet (s.sup K).edgeSet := by
      rw [Finset.sup_eq_iSup]
      simp only [SimpleGraph.edgeSet_iSup, Set.disjoint_iUnion_right]
      intro i hi
      exact hd (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    obtain ⟨F, hF⟩ := D.union_disjoint E hdis
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact ⟨F, hF.trans_le (Nat.add_le_add hD hE)⟩

end Gallai
