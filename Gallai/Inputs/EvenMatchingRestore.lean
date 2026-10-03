/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.MatchingRestore
public import Gallai.Inputs.MatchingPuncture
public import Gallai.Foundations.EndpointBounds

@[expose] public section

/-! # Parity-certified restoration of an even matching -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- A recipient whose original even neighbours all meet the removed even
matching has no passing neighbour in any decomposition of the puncture. -/
theorem Decomposition.no_passing_after_even_matching
    (hle : F ≤ G) (hm : ∀ v, F.degree v ≤ 1)
    (he : ∀ v, 0 < F.degree v → Even (G.degree v))
    (D : Decomposition (G \ F)) (u : V)
    (hc : ∀ v, G.Adj u v → Even (G.degree v) → 0 < F.degree v) :
    #{v ∈ (G \ F).neighborFinset u | D.endpointCount v = 0} = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hv
  have ha := ((G \ F).mem_neighborFinset u v).mp ha
  have hp := D.endpointCount_mod_two v
  have hev : Even ((G \ F).degree v) := by rw [Nat.even_iff]; omega
  have hg := matching_puncture_even_preserved hle hm he v hev
  have ho := matching_puncture_odd hle hm he v (hc v ha.1 hg)
  exact Nat.not_even_iff_odd.mpr ho hev

/-- Restore an oriented even matching with exact path count when every
recipient's even neighbours are active and cross recipient-donor edges are absent. -/
theorem Decomposition.restore_even_matching (S : Finset (V × V))
    (hF : F = S.sup (fun e => SimpleGraph.edge e.1 e.2))
    (hle : F ≤ G) (hm : ∀ v, F.degree v ≤ 1)
    (he : ∀ v, 0 < F.degree v → Even (G.degree v))
    (hends : ∀ e ∈ S, e.1 ≠ e.2)
    (hsep : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)
    (hcross : ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ¬ G.Adj e.1 f.2)
    (hcover : ∀ e ∈ S, ∀ v, G.Adj e.1 v → Even (G.degree v) → 0 < F.degree v)
    (D : Decomposition (G \ F)) :
    ∃ E : Decomposition G, E.size = D.size := by
  have ha (e : V × V) (heS : e ∈ S) : F.Adj e.1 e.2 := by
    rw [hF]
    apply (Finset.le_sup (f := fun e : V × V => SimpleGraph.edge e.1 e.2) heS)
    exact (SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hends e heS⟩
  obtain ⟨E, hE, _⟩ := D.matching_addibility S hends hsep
    (fun e heS h => h.2 (ha e heS))
    (fun e heS f hfS hef h => hcross e heS f hfS hef h.1)
    (fun e heS => D.no_passing_after_even_matching hle hm he e.1 (hcover e heS))
    (fun e heS => D.endpointCount_pos_of_odd_degree e.2
      (matching_puncture_odd hle hm he e.2 (ha e heS).degree_pos_right))
  have hg : (G \ F) ⊔ S.sup (fun e => SimpleGraph.edge e.1 e.2) = G := by
    rw [← hF]
    exact sdiff_sup_cancel hle
  have hout : ∃ E : Decomposition ((G \ F) ⊔ S.sup (fun e => SimpleGraph.edge e.1 e.2)),
      E.size = D.size := ⟨E, hE⟩
  rwa [hg] at hout

end Gallai
