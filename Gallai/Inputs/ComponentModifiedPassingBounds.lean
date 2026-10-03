/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentModifiedPassing

@[expose] public section

/-! # The two actual passing-neighbour tiers for modified restoration -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- A component with an opposite pair has exactly its witnessed donor. -/
theorem ComponentDeletionChoice.pair_donors_eq
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (e : V × V) (he : e ∈ d.pairs) : d.pairs.image Prod.snd = {e.2} := by
  classical
  ext w
  constructor
  · rintro hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
    have h := d.pair_unique f e hf he
    subst f
    exact Finset.mem_singleton_self _
  · intro hw
    exact Finset.mem_image.mpr ⟨e, he, (Finset.mem_singleton.mp hw).symm⟩

/-- The exceptional local candidate set has at most two members, and only
one unless exactly one of its two selected spokes remains. -/
theorem componentExceptionalLeaves_candidates_bounds
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (C : (evenSubgraph G).ConnectedComponent) (e : V × V) (he : e ∈ (d C).pairs)
    (B : Finset V) (v : V) (hv : v ∈ componentExceptionalLeaves d C e) (hn : v ∉ B) :
    #(((componentExceptionalLeaves d C e ∩ B) ∪ (d C).pairs.image Prod.snd).erase v) ≤ 2 ∧
      (v ∉ componentModifiedDifficultLeaves d C e B →
        #(((componentExceptionalLeaves d C e ∩ B) ∪ (d C).pairs.image Prod.snd).erase v) ≤ 1) := by
  classical
  have hcard := componentExceptionalLeaves_card d C e he
  have hsplit := Finset.card_sdiff_add_card_inter (componentExceptionalLeaves d C e) B
  have hpositive : 0 < #(componentExceptionalLeaves d C e \ B) :=
    Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hn⟩⟩
  have hle := Finset.card_le_card (Finset.erase_subset (s :=
    (componentExceptionalLeaves d C e ∩ B) ∪ (d C).pairs.image Prod.snd) v)
  have hunion := Finset.card_union_le (componentExceptionalLeaves d C e ∩ B)
    ((d C).pairs.image Prod.snd)
  have hdonor : #((d C).pairs.image Prod.snd) = 1 := by
    rw [(d C).pair_donors_eq e he]
    exact Finset.card_singleton _
  refine ⟨by omega, ?_⟩
  intro hnot
  have hne : #(componentExceptionalLeaves d C e \ B) ≠ 1 := by
    intro h
    exact hnot ((mem_componentModifiedDifficultLeaves d C e B v).mpr
      (Or.inr ⟨h, hv, hn⟩))
  omega

/-- The actual modified endpoint vector supplies both passing bounds required
by two-tier outward restoration, with no passing-free assumption. -/
theorem Decomposition.modified_passing_bounds
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (C₀ : (evenSubgraph G).ConnectedComponent)
    (e : V × V) (he : e ∈ (d C₀).pairs) (ha : G.Adj u e.1)
    (D : Decomposition (G \ componentModifiedDeletion d e))
    {K : SimpleGraph V} [DecidableRel K.Adj] (hKG : K ≤ G) (Q : Decomposition K)
    (B : Finset V) (hB : B ⊆ insert e.1 (componentDeletionLeaves d))
    (hqu : 0 < Q.endpointCount u)
    (hbal : ∀ w, Q.endpointCount w + (if w ∈ B then 1 else 0) +
        (∑ f ∈ (componentDeletionPairs d).erase e, if f.2 = w then 1 else 0) =
      D.endpointCount w +
        (∑ f ∈ (componentDeletionPairs d).erase e, if f.1 = w then 1 else 0) +
        if u = w then #B else 0)
    (v : V) (hv : v ∈ (insert e.1 (componentDeletionLeaves d)) \ B) :
    #{w ∈ K.neighborFinset v | Q.endpointCount w = 0} ≤ 2 ∧
      (v ∉ componentModifiedDifficultLeaves d C₀ e B →
        #{w ∈ K.neighborFinset v | Q.endpointCount w = 0} ≤ 1) := by
  classical
  obtain ⟨hv, hn⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨C, hvC⟩ := componentModifiedLocalLeaves_exists d C₀ e v hv
  have hbound := Finset.card_le_card
    (D.modified_passing_subset d hu C₀ e he ha hKG Q B hB hqu hbal C v hvC)
  by_cases hC : C = C₀
  · subst C
    simp only [componentModifiedLocalLeaves, if_true] at hvC hbound
    have hc := componentExceptionalLeaves_candidates_bounds d C₀ e he B v hvC hn
    exact ⟨hbound.trans hc.1, fun h => hbound.trans (hc.2 h)⟩
  · simp only [componentModifiedLocalLeaves, hC, if_false] at hvC hbound
    have hc := (d C).residual_candidates_bounds B v hvC hn
    refine ⟨hbound.trans hc.1, ?_⟩
    intro hnot
    apply hbound.trans (hc.2 ?_)
    intro h
    apply hnot
    apply (mem_componentModifiedDifficultLeaves d C₀ e B v).mpr
    exact Or.inl (Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, h⟩)

end Gallai
