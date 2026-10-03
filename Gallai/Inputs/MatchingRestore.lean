/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SingleEdge

@[expose] public section

/-!
# Restoration of an oriented matching

Botler–Sambinelli Lemma 8 follows from single-edge addibility. The necessary
separation is between recipients and other donors: same-side edges are allowed.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V] [Fintype V]
  [DecidableRel G.Adj]

/-- A donor that is not adjacent to an untouched vertex cannot become a new
passing neighbour there, even if it loses its final endpoint. -/
theorem passing_neighbors_mono_of_donor_not_adj (D : Decomposition G) (a b t : V)
    (E : Decomposition (G ⊔ SimpleGraph.edge a b)) (hta : t ≠ a) (htb : t ≠ b)
    (hbalance : ∀ v, E.endpointCount v + (if b = v then 1 else 0) =
      D.endpointCount v + if a = v then 1 else 0)
    (hnot : ¬ G.Adj t b) :
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
  have hb : b ≠ v := fun h => hnot (h ▸ hold)
  have he := hbalance v
  simp only [hb, if_false, hz, Nat.zero_add] at he
  exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset t v).mpr hold, by omega⟩

/-- Restore separated recipient-donor pairs without increasing the path count.
This includes induced matchings and allows edges within either side. -/
theorem matching_addibility (D : Decomposition G) (S : Finset (V × V))
    (hends : ∀ e ∈ S, e.1 ≠ e.2)
    (hsep : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hmissing : ∀ e ∈ S, ¬ G.Adj e.1 e.2)
    (hcross : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ¬ G.Adj e.1 f.2)
    (hpassing : ∀ e ∈ S,
      #{v ∈ G.neighborFinset e.1 | D.endpointCount v = 0} = 0)
    (hdonor : ∀ e ∈ S, 0 < D.endpointCount e.2) :
    ∃ E : Decomposition (G ⊔ S.sup (fun e => SimpleGraph.edge e.1 e.2)),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (∑ e ∈ S, if e.2 = v then 1 else 0) =
          D.endpointCount v + ∑ e ∈ S, if e.1 = v then 1 else 0 := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq]
    simpa using (show ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, E.endpointCount v = D.endpointCount v from ⟨D, rfl, fun _ => rfl⟩)
  | @insert e S heS ih =>
    have he : e ∈ insert e S := Finset.mem_insert_self e S
    have hmem : ∀ f ∈ S, f ∈ insert e S := fun _ hf => Finset.mem_insert_of_mem hf
    have hne : ∀ f ∈ S, e ≠ f := fun _ hf h => heS (h ▸ hf)
    have hs := hpassing e he
    have hd := hdonor e he
    obtain ⟨E, hsize, hb⟩ := D.single_edge_addibility e.1 e.2 (hends e he)
      (hmissing e he) (by omega)
    have hsep' := fun f hf => hsep e he f (hmem f hf) (hne f hf)
    have hretain : ∀ f ∈ S, ∀ v, (G ⊔ SimpleGraph.edge e.1 e.2).Adj f.1 v →
        G.Adj f.1 v := by
      intro f hf v h
      rcases h with h | h
      · exact h
      · rw [SimpleGraph.edge_adj] at h
        rcases h.1 with h | h
        · exact ((hsep' f hf).1 h.1.symm).elim
        · exact ((hsep' f hf).2.2.1 h.1.symm).elim
    have hpass : ∀ f ∈ S,
        #{v ∈ (G ⊔ SimpleGraph.edge e.1 e.2).neighborFinset f.1 |
          E.endpointCount v = 0} = 0 := by
      intro f hf
      have hm := D.passing_neighbors_mono_of_donor_not_adj e.1 e.2 f.1 E
        (hsep' f hf).1.symm (hsep' f hf).2.2.1.symm hb
        (hcross f (hmem f hf) e he (hne f hf).symm)
      have hz := hpassing f (hmem f hf)
      omega
    have hdon : ∀ f ∈ S, 0 < E.endpointCount f.2 := by
      intro f hf
      have h := hb f.2
      simp only [(hsep' f hf).2.1, (hsep' f hf).2.2.2, if_false, Nat.add_zero] at h
      rw [h]
      exact hdonor f (hmem f hf)
    obtain ⟨F, hfsize, hf⟩ := ih E
      (fun f h => hends f (hmem f h))
      (fun f h g k => hsep f (hmem f h) g (hmem g k))
      (fun f h hh => hmissing f (hmem f h) (hretain f h f.2 hh))
      (fun f h g k hfg hh => hcross f (hmem f h) g (hmem g k) hfg
        (hretain f h g.2 hh)) hpass hdon
    have hg : G ⊔ (insert e S).sup (fun f => SimpleGraph.edge f.1 f.2) =
        (G ⊔ SimpleGraph.edge e.1 e.2) ⊔ S.sup (fun f => SimpleGraph.edge f.1 f.2) := by
      rw [Finset.sup_insert, sup_assoc]
    rw [hg]
    refine ⟨F, hfsize.trans hsize, ?_⟩
    intro v
    rw [Finset.sum_insert heS, Finset.sum_insert heS]
    have h₁ := hb v
    have h₂ := hf v
    omega

end Gallai.Decomposition
