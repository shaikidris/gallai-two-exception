/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MultiDonor

@[expose] public section

/-!
# Inward star restoration

Fan's Lemma 3.5 is expressed without truncated subtraction: a restored subset
has twice its size plus the initial passing count at least the missing-star
size. Lemma 3.6 first restores a prescribed spoke, then applies that bound.
All endpoint equations concern the same constructed decomposition.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- Adding one missing spoke inward creates at most one new passing neighbour
of the hub: the donor of that spoke. -/
theorem passing_neighbors_le_add_one (D : Decomposition G) (a b : V)
    (E : Decomposition (G ⊔ SimpleGraph.edge a b))
    (hbalance : ∀ v, E.endpointCount v + (if b = v then 1 else 0) =
      D.endpointCount v + if a = v then 1 else 0) :
    #{v ∈ (G ⊔ SimpleGraph.edge a b).neighborFinset a | E.endpointCount v = 0} ≤
      #{v ∈ G.neighborFinset a | D.endpointCount v = 0} + 1 := by
  classical
  have hsub :
      ((G ⊔ SimpleGraph.edge a b).neighborFinset a).filter (fun v => E.endpointCount v = 0) ⊆
        insert b ((G.neighborFinset a).filter (fun v => D.endpointCount v = 0)) := by
    intro v hv
    obtain ⟨hadj, hz⟩ := Finset.mem_filter.mp hv
    have hadj := ((G ⊔ SimpleGraph.edge a b).mem_neighborFinset a v).mp hadj
    by_cases hb : b = v
    · exact Finset.mem_insert.mpr (Or.inl hb.symm)
    · have ha : a ≠ v := hadj.ne
      have hold : G.Adj a v := by
        rcases hadj with h | h
        · exact h
        · rw [SimpleGraph.edge_adj] at h
          rcases h.1 with h | h
          · exact (hb h.2.symm).elim
          · exact (ha h.2.symm).elim
      have he := hbalance v
      simp only [hb, ha, if_false, hz, Nat.add_zero] at he
      exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset a v).mpr hold, he.symm⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- Restore an inward subset of a missing star, losing at most the initial
passing-neighbour deficit in the twice-cardinality bound (Fan's Lemma 3.5). -/
theorem inward_star_addibility (D : Decomposition G) (a : V) (S : Finset V)
    (ha : a ∉ S) (hmissing : ∀ b ∈ S, ¬ G.Adj a b)
    (hpositive : ∀ b ∈ S, 0 < D.endpointCount b) :
    ∃ A : Finset V, A ⊆ S ∧
      #S ≤ 2 * #A + #{v ∈ G.neighborFinset a | D.endpointCount v = 0} ∧
      ∃ E : Decomposition (G ⊔ A.sup (SimpleGraph.edge a)), E.size = D.size ∧
        ∀ v, E.endpointCount v + (if v ∈ A then 1 else 0) =
          D.endpointCount v + if a = v then #A else 0 := by
  classical
  induction S using Finset.strongInductionOn generalizing G with
  | _ S ih =>
    by_cases hsmall : #S ≤ #{v ∈ G.neighborFinset a | D.endpointCount v = 0}
    · refine ⟨∅, Finset.empty_subset _, by simpa using hsmall, ?_⟩
      rw [Finset.sup_empty, sup_bot_eq]
      simpa using (show ∃ E : Decomposition G, E.size = D.size ∧
        ∀ v, E.endpointCount v = D.endpointCount v from ⟨D, rfl, fun _ => rfl⟩)
    · have hsupply : #S ≤ ∑ b ∈ S, D.endpointCount b := by
        calc
          #S = ∑ _b ∈ S, (1 : ℕ) := by simp
          _ ≤ ∑ b ∈ S, D.endpointCount b :=
            Finset.sum_le_sum (fun b hb => hpositive b hb)
      obtain ⟨b, hb, E, hsize, hend⟩ := D.multi_donor_addibility a S ha hmissing
        (lt_of_lt_of_le (Nat.lt_of_not_ge hsmall) hsupply)
      have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
      have hrem : ∀ c ∈ S.erase b, ¬ (G ⊔ SimpleGraph.edge a b).Adj a c := by
        intro c hc h
        obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
        rcases h with h | h
        · exact hmissing c hcS h
        · rw [SimpleGraph.edge_adj] at h
          rcases h.1 with h | h
          · exact hcb h.2
          · exact hab h.1
      have hpos : ∀ c ∈ S.erase b, 0 < E.endpointCount c := by
        intro c hc
        obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
        have hac : a ≠ c := fun h => ha (h.symm ▸ hcS)
        have he := hend c
        simp only [Ne.symm hcb, hac, if_false, Nat.add_zero] at he
        rw [he]
        exact hpositive c hcS
      obtain ⟨A, hAS, hcount, Q, hQsize, hQend⟩ :=
        ih (S.erase b) (Finset.erase_ssubset hb) E
          (fun h => ha (Finset.mem_of_mem_erase h)) hrem hpos
      have hbA : b ∉ A := fun h => (Finset.mem_erase.mp (hAS h)).1 rfl
      have hcard := Finset.card_erase_add_one hb
      have hpass := D.passing_neighbors_le_add_one a b E hend
      refine ⟨insert b A, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hb (fun c hc => Finset.mem_of_mem_erase (hAS hc))
      · rw [Finset.card_insert_of_notMem hbA]
        omega
      · have hgraph : (G ⊔ SimpleGraph.edge a b) ⊔ A.sup (SimpleGraph.edge a) =
            G ⊔ (insert b A).sup (SimpleGraph.edge a) := by
          rw [Finset.sup_insert]
          exact sup_assoc _ _ _
        rw [← hgraph]
        refine ⟨Q, hQsize.trans hsize, ?_⟩
        intro v
        have he := hend v
        have hq := hQend v
        rw [Finset.card_insert_of_notMem hbA]
        by_cases hbv : b = v
        · subst v
          simp only [if_true, hab, hbA, if_false, Finset.mem_insert_self,
            Nat.add_zero] at he hq ⊢
          omega
        · have hvb : v ≠ b := Ne.symm hbv
          simp only [hbv, if_false, Nat.add_zero] at he
          simp only [Finset.mem_insert, hvb, false_or]
          by_cases hav : a = v <;> by_cases hvA : v ∈ A <;>
            simp only [hav, hvA, if_true, if_false, Nat.add_zero] at he hq ⊢ <;> omega

end Gallai.Decomposition
