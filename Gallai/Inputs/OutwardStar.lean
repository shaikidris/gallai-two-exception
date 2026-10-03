/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SingleEdge

@[expose] public section

/-!
# Outward restoration of a finite star

Iterating the single-edge lemma requires control of passing neighbours after
each endpoint transfer. A positive remaining donor prevents new passing
neighbours at every untouched leaf.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V]
  [DecidableRel G.Adj]

/-- An endpoint transfer with a still-positive donor creates no passing
neighbours at a vertex different from the two ends of the added edge. -/
theorem passing_neighbors_mono_after_transfer (D : Decomposition G) (a b t : V)
    (E : Decomposition (G ⊔ SimpleGraph.edge a b)) (hta : t ≠ a) (htb : t ≠ b)
    (hbalance : ∀ v, E.endpointCount v + (if b = v then 1 else 0) =
      D.endpointCount v + if a = v then 1 else 0)
    (hpositive : 0 < E.endpointCount b) :
    #{v ∈ (G ⊔ SimpleGraph.edge a b).neighborFinset t | E.endpointCount v = 0} ≤
      #{v ∈ G.neighborFinset t | D.endpointCount v = 0} := by
  classical
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, hz⟩ := Finset.mem_filter.mp hv
  have hadj := ((G ⊔ SimpleGraph.edge a b).mem_neighborFinset t v).mp hv
  have hold : G.Adj t v := by
    rcases hadj with h | h
    · exact h
    · rw [SimpleGraph.edge_adj] at h
      rcases h.1 with h | h
      · exact (hta h.1).elim
      · exact (htb h.1).elim
  have hb : b ≠ v := by
    intro h
    subst v
    omega
  have he := hbalance v
  simp only [hb, if_false, hz, Nat.zero_add] at he
  exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset t v).mpr hold, by omega⟩

/-- Restore a finite set of absent spokes outward, preserving size and the
exact endpoint vector. This is the nonnegative-reserve form of FHZ Lemma 5,
reproduced as Xie Lemma 2.4, derived here from single-edge addibility. -/
theorem outward_star_addibility (D : Decomposition G) (w : V) (S : Finset V) (l : ℕ)
    (hw : w ∉ S) (hmissing : ∀ x ∈ S, ¬ G.Adj w x)
    (hpassing : ∀ x ∈ S,
      #{v ∈ G.neighborFinset x | D.endpointCount v = 0} ≤ l)
    (hreserve : l + #S ≤ D.endpointCount w) :
    ∃ E : Decomposition (G ⊔ S.sup (SimpleGraph.edge w)), E.size = D.size ∧
      ∀ v, E.endpointCount v + (if w = v then #S else 0) =
        D.endpointCount v + if v ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq]
    simpa using (show ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v from ⟨D, rfl, fun _ => rfl⟩)
  | @insert x S hx ih =>
    have hwx : w ≠ x := fun h => hw (h ▸ Finset.mem_insert_self x S)
    have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
    have hcard : #(insert x S) = #S + 1 := Finset.card_insert_of_notMem hx
    have hp := hpassing x (Finset.mem_insert_self x S)
    have hs : #{v ∈ G.neighborFinset x | D.endpointCount v = 0} <
        D.endpointCount w := by omega
    obtain ⟨E, hsize, he⟩ := D.single_edge_addibility x w hwx.symm
      (fun h => hmissing x (Finset.mem_insert_self x S) h.symm) hs
    have hew : E.endpointCount w + 1 = D.endpointCount w := by
      simpa only [if_true, hwx.symm, if_false, Nat.add_zero] using he w
    have hrem : l + #S ≤ E.endpointCount w := by omega
    have hm : ∀ t ∈ S, ¬ (G ⊔ SimpleGraph.edge x w).Adj w t := by
      intro t ht h
      rcases h with h | h
      · exact hmissing t (Finset.mem_insert_of_mem ht) h
      · rw [SimpleGraph.edge_adj] at h
        rcases h.1 with h | h
        · exact hwx h.1
        · exact hx (h.2 ▸ ht)
    have hpass : ∀ t ∈ S,
        #{v ∈ (G ⊔ SimpleGraph.edge x w).neighborFinset t |
          E.endpointCount v = 0} ≤ l := by
      intro t ht
      have hpos : 0 < E.endpointCount w := by
        have hc : 0 < #S := Finset.card_pos.mpr ⟨t, ht⟩
        omega
      have htx : t ≠ x := fun h => hx (h ▸ ht)
      have htw : t ≠ w := fun h => hwS (h ▸ ht)
      exact (D.passing_neighbors_mono_after_transfer x w t E htx htw he hpos).trans
        (hpassing t (Finset.mem_insert_of_mem ht))
    obtain ⟨F, hfsize, hf⟩ := ih E hwS hm hpass hrem
    have hgraph : G ⊔ (insert x S).sup (SimpleGraph.edge w) =
        (G ⊔ SimpleGraph.edge x w) ⊔ S.sup (SimpleGraph.edge w) := by
      rw [Finset.sup_insert, SimpleGraph.edge_comm w x, sup_assoc]
    rw [hgraph]
    refine ⟨F, hfsize.trans hsize, ?_⟩
    intro v
    have h₁ := he v
    have h₂ := hf v
    by_cases hvw : w = v
    · subst v
      simp only [if_true, hwx.symm, hwS, hw, if_false, Nat.add_zero] at h₁ h₂ ⊢
      omega
    · by_cases hvx : v = x
      · subst v
        simp only [hvw, hx, if_false, if_true, Finset.mem_insert_self,
          Nat.add_zero] at h₁ h₂ ⊢
        omega
      · simp only [hvw, Ne.symm hvx, if_false, Nat.add_zero] at h₁ h₂ ⊢
        simpa only [Finset.mem_insert, hvx, false_or] using (by omega :
          F.endpointCount v = D.endpointCount v + if v ∈ S then 1 else 0)

end Gallai.Decomposition
