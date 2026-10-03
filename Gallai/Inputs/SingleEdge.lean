/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.Selection
public import Gallai.Inputs.SwitchFamily
public import Gallai.Foundations.EdgeCounts

@[expose] public section

/-!
# Fan's single-edge addibility lemma

The finite predecessor argument supplies selected runs and an avoiding carrier.
Their simultaneous switch constructs the decomposition, preserving its size
and moving exactly one endpoint from the donor to the recipient.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Exact selected-run balance transports the actual family to an edge-union decomposition. -/
theorem exists_add_of_selected_runs (D : Decomposition G) (a b v : V)
    (hab : a ≠ b) (hmissing : ¬ G.Adj a b) (R : Finset (D.RunSlot a))
    (hshape : ∀ r ∈ R, D.runEndpoint a r = b ∨ G.Adj a (D.runEndpoint a r))
    (hvshape : v = b ∨ G.Adj a v)
    (hbalance : ∀ f : V → ℕ,
      (∑ r ∈ R, f (D.runEndpoint a r)) + f v =
        (∑ r ∈ R, f (D.runNeighbor a r)) + f b)
    (k : Fin D.size) (hv : (D.path k).start = v ∨ (D.path k).finish = v)
    (ha : a ∉ (D.path k).walk.support) :
    ∃ E : Decomposition (G ⊔ SimpleGraph.edge a b), E.size = D.size ∧
      ∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  classical
  let K := G ⊔ SimpleGraph.edge a b
  have hroot : K.Adj a b := by
    apply Or.inr
    rw [← SimpleGraph.mem_edgeSet, SimpleGraph.edgeSet_edge_of_ne hab]
    exact Set.mem_singleton _
  have hnew : ∀ r ∈ R, K.Adj (D.runEndpoint a r) a := by
    intro r hr
    rcases hshape r hr with he | he
    · rw [he]
      exact hroot.symm
    · exact Or.inl he.symm
  have hav : K.Adj a v := by
    rcases hvshape with he | he
    · rw [he]
      exact hroot
    · exact Or.inl he
  obtain ⟨paths, he, hw⟩ := D.exists_switch_family a v R k hv ha le_sup_left hnew hav
  have hcounts (e : Sym2 V) : (∑ i, (paths i).walk.edges.count e) =
      (∑ i : Fin D.size, (D.path i).walk.edges.count e) + if s(a, b) = e then 1 else 0 := by
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => he i e)
    simp only [Finset.sum_add_distrib, D.sum_selectedOwnerSum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
    have hb := hbalance (fun w => if s(a, w) = e then 1 else 0)
    omega
  have hcover : ∀ e ∈ K.edgeSet, (∑ i, (paths i).walk.edges.count e) = 1 := by
    intro e heK
    rw [hcounts, D.sum_edge_count]
    change e ∈ (G ⊔ SimpleGraph.edge a b).edgeSet at heK
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hab] at heK
    rcases heK with heG | heq
    · have hn : s(a, b) ≠ e := fun hh =>
        hmissing (show s(a, b) ∈ G.edgeSet from hh.symm ▸ heG)
      simp only [heG, hn, if_true, if_false, Nat.add_zero]
    · have heq' : e = s(a, b) := heq
      subst e
      simp only [show s(a, b) ∉ G.edgeSet from hmissing, if_false, if_true, Nat.zero_add]
  let E := ofEdgeCounts paths hcover
  refine ⟨E, rfl, ?_⟩
  intro w
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hw i w)
  simp only [Finset.sum_add_distrib, D.sum_selectedOwnerSum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  have hb := hbalance (fun t => if t = w then 1 else 0)
  change (∑ i, ((if (paths i).start = w then 1 else 0) +
      (if (paths i).finish = w then 1 else 0))) + (if b = w then 1 else 0) =
    (∑ i : Fin D.size, ((if (D.path i).start = w then 1 else 0) +
      (if (D.path i).finish = w then 1 else 0))) + if a = w then 1 else 0
  simp only [Finset.sum_add_distrib]
  omega

/-- Fan's strict-inequality single-edge lemma, with no assumed favourable carrier or sequence. -/
theorem single_edge_addibility [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (a b : V) (hab : a ≠ b) (hmissing : ¬ G.Adj a b)
    (hstrict : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} < D.endpointCount b) :
    ∃ E : Decomposition (G ⊔ SimpleGraph.edge a b), E.size = D.size ∧
      ∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  obtain ⟨v, k, hreach, _, hv, ha⟩ := D.exists_reachable_avoiding_endpoint a b hab hmissing hstrict
  obtain ⟨R, _, hshape, hbalance⟩ := D.exists_selected_runs a b v hmissing hreach
  exact D.exists_add_of_selected_runs a b v hab hmissing R hshape
    (D.reachable_eq_root_or_adj a b v hreach) hbalance k hv ha

end Gallai.Decomposition
