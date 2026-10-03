/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ComponentPassing

@[expose] public section

/-! # The two passing-neighbour tiers of actual component restoration -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {u : V}

/-- A residual leaf has at most two local loss candidates, and at most one
unless its full triangle has exactly two selected spokes. -/
theorem ComponentDeletionChoice.residual_candidates_bounds
    {C : (evenSubgraph G).ConnectedComponent} (d : ComponentDeletionChoice G u C)
    (B : Finset V) (v : V) (hv : v ∈ d.leaves) (hn : v ∉ B) :
    #(((d.leaves ∩ B) ∪ d.pairs.image Prod.snd).erase v) ≤ 2 ∧
      (v ∉ d.difficultLeaves B →
        #(((d.leaves ∩ B) ∪ d.pairs.image Prod.snd).erase v) ≤ 1) := by
  classical
  cases d with
  | untouched => simp [ComponentDeletionChoice.leaves] at hv
  | isolate a hC ha =>
    have hv : v = a := by simpa [ComponentDeletionChoice.leaves] using hv
    subst v
    simp [ComponentDeletionChoice.leaves, ComponentDeletionChoice.pairs, hn]
  | triangle a b c hab hac hbc hC habE hacE hbcE hua ho =>
    let d' : ComponentDeletionChoice G u C :=
      .triangle a b c hab hac hbc hC habE hacE hbcE hua ho
    change #(((d'.leaves ∩ B) ∪ d'.pairs.image Prod.snd).erase v) ≤ 2 ∧ _
    change v ∈ d'.leaves at hv
    by_cases h : G.Adj u c
    · have hab' : (a : V) ≠ b := fun he => hab (Subtype.ext he)
      have hac' : (a : V) ≠ c := fun he => hac (Subtype.ext he)
      have hbc' : (b : V) ≠ c := fun he => hbc (Subtype.ext he)
      have hc : #d'.leaves = 3 := by
        simp [d', ComponentDeletionChoice.leaves, h, hab', hac', hbc']
      have heq : ((d'.leaves ∩ B) ∪ d'.pairs.image Prod.snd).erase v = d'.leaves ∩ B := by
        simp [d', ComponentDeletionChoice.pairs, h, Finset.erase_eq_of_notMem
          (show v ∉ d'.leaves ∩ B from fun hv => hn (Finset.mem_inter.mp hv).2)]
      have hcount := Finset.card_sdiff_add_card_inter d'.leaves B
      have hpos : 0 < #(d'.leaves \ B) := Finset.card_pos.mpr
        ⟨v, Finset.mem_sdiff.mpr ⟨hv, hn⟩⟩
      rw [heq]
      refine ⟨by omega, ?_⟩
      intro hnot
      have hne : #(d'.leaves ∩ B) ≠ 2 := by
        intro he
        exact hnot ((d'.mem_difficultLeaves B v).mpr ⟨hc, he, hv, hn⟩)
      omega
    · have hva : v = a := by simpa [d', ComponentDeletionChoice.leaves, h] using hv
      subst v
      have hac' : (a : V) ∉ ({(c : V)} : Finset V) := by
        simpa using (show (a : V) ≠ c from fun he => hac (Subtype.ext he))
      simp [d', ComponentDeletionChoice.leaves, ComponentDeletionChoice.pairs, h, hn,
        Finset.erase_eq_of_notMem hac']

/-- Decision instance for the initial puncture in the outward consumer. -/
noncomputable local instance componentPassingBoundsUnionAdj
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C) :
    DecidableRel (componentDeletionUnion d).Adj := fun _ _ => Classical.propDecidable _

/-- The actual combined endpoint vector implies the two passing-neighbour
bounds required by outward restoration. Both bounds concern the same Q. -/
theorem Decomposition.component_passing_bounds
    (d : ∀ C : (evenSubgraph G).ConnectedComponent, ComponentDeletionChoice G u C)
    (hu : Odd (G.degree u)) (D : Decomposition (G \ componentDeletionUnion d))
    {K : SimpleGraph V} [DecidableRel K.Adj] (hKG : K ≤ G) (Q : Decomposition K)
    (B : Finset V) (hB : B ⊆ componentDeletionLeaves d)
    (hqu : 0 < Q.endpointCount u)
    (hbal : ∀ w, Q.endpointCount w + (if w ∈ B then 1 else 0) +
        (∑ e ∈ componentDeletionPairs d, if e.2 = w then 1 else 0) =
      D.endpointCount w + (∑ e ∈ componentDeletionPairs d, if e.1 = w then 1 else 0) +
        if u = w then #B else 0)
    (v : V) (hv : v ∈ componentDeletionLeaves d \ B) :
    #{w ∈ K.neighborFinset v | Q.endpointCount w = 0} ≤ 2 ∧
      (v ∉ componentDifficultLeaves d B →
        #{w ∈ K.neighborFinset v | Q.endpointCount w = 0} ≤ 1) := by
  classical
  obtain ⟨hv, hn⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨C, _, hv⟩ := Finset.mem_biUnion.mp hv
  have hs := Finset.card_le_card (D.component_passing_subset d hu hKG Q B hB hqu hbal C v hv)
  have hc := (d C).residual_candidates_bounds B v hv hn
  refine ⟨hs.trans hc.1, ?_⟩
  intro hnot
  apply hs.trans (hc.2 ?_)
  intro h
  exact hnot (Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ C, h⟩)

end Gallai
