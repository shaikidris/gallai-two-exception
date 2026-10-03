/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Trim
public import Gallai.Foundations.Endpoints

@[expose] public section

/-! # Terminal-edge deletion while the shortened carrier remains nonempty -/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

omit [DecidableEq V] in
theorem other_avoids_first (D : Decomposition G) (i j : Fin D.size) (hji : j ≠ i) :
    s((D.path i).start, (D.path i).walk.snd) ∉ (D.path j).walk.edges := by
  intro hj
  have hi : s((D.path i).start, (D.path i).walk.snd) ∈ (D.path i).walk.edges := by
    rw [← (D.path i).firstEdge_cons_tail_edges]
    exact List.mem_cons_self
  obtain ⟨k, _, hu⟩ := D.covers _ ((D.path i).walk.edges_subset_edgeSet hi)
  exact hji ((hu j hj).trans (hu i hi).symm)

def trimFamily (D : Decomposition G) (i : Fin D.size)
    (hlong : 1 < (D.path i).walk.length) (j : Fin D.size) :
    NonemptyPath (G.deleteEdges {s((D.path i).start, (D.path i).walk.snd)}) :=
  if hji : j = i then (D.path i).trimFirst hlong else
    (D.path j).transfer _ (fun e he => by
      rw [SimpleGraph.edgeSet_deleteEdges]
      refine ⟨(D.path j).walk.edges_subset_edgeSet he, ?_⟩
      intro heq
      have : e = s((D.path i).start, (D.path i).walk.snd) := Set.mem_singleton_iff.mp heq
      exact D.other_avoids_first i j hji (this ▸ he))

omit [DecidableEq V] in
theorem trimFamily_edges (D : Decomposition G) (i j : Fin D.size)
    (hlong : 1 < (D.path i).walk.length) (e : Sym2 V) :
    e ∈ (trimFamily D i hlong j).walk.edges ↔
      e ∈ (D.path j).walk.edges ∧ e ≠ s((D.path i).start, (D.path i).walk.snd) := by
  by_cases hji : j = i
  · subst j
    have hpaths : trimFamily D i hlong i = (D.path i).trimFirst hlong := by
      simp [trimFamily]
    have hedges := congrArg (fun P : NonemptyPath _ => P.walk.edges) hpaths
    rw [hedges, NonemptyPath.trimFirst_edges, ← (D.path i).firstEdge_cons_tail_edges]
    simp only [List.mem_cons]
    constructor
    · intro he
      exact ⟨Or.inr he, fun h => (D.path i).firstEdge_notMem_tail_edges (h ▸ he)⟩
    · rintro ⟨he | he, hne⟩
      · exact False.elim (hne he)
      · exact he
  · have hedges : (trimFamily D i hlong j).walk.edges = (D.path j).walk.edges := by
      unfold trimFamily
      rw [dif_neg hji]
      exact NonemptyPath.transfer_edges ..
    rw [hedges]
    exact ⟨fun he => ⟨he, fun h => D.other_avoids_first i j hji (h ▸ he)⟩, And.left⟩

/-- Delete the first edge of a carrier of length at least two, without adding paths. -/
def trimFirst (D : Decomposition G) (i : Fin D.size)
    (hlong : 1 < (D.path i).walk.length) :
    Decomposition (G.deleteEdges {s((D.path i).start, (D.path i).walk.snd)}) where
  size := D.size
  path := trimFamily D i hlong
  covers := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges] at he
    obtain ⟨j, hj, hu⟩ := D.covers e he.1
    have hne : e ≠ s((D.path i).start, (D.path i).walk.snd) := he.2
    refine ⟨j, (trimFamily_edges D i j hlong e).mpr ⟨hj, hne⟩, ?_⟩
    intro k hk
    exact hu k ((trimFamily_edges D i k hlong e).mp hk).1

omit [DecidableEq V] in
/-- Trimming a longer terminal carrier leaves the number of paths unchanged. -/
@[simp] theorem trimFirst_size (D : Decomposition G) (i : Fin D.size)
    (hlong : 1 < (D.path i).walk.length) : (D.trimFirst i hlong).size = D.size := rfl

/-- Only the initial endpoint moves, from the old first to the old second vertex. -/
theorem trimFirst_endpointCount (D : Decomposition G) (i : Fin D.size)
    (hlong : 1 < (D.path i).walk.length) (w : V) :
    (D.trimFirst i hlong).endpointCount w + (if (D.path i).start = w then 1 else 0) =
      D.endpointCount w + if (D.path i).walk.snd = w then 1 else 0 := by
  let ends {K : SimpleGraph V} (P : NonemptyPath K) :=
    (if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0 : ℕ)
  have hsum :
      (∑ j : Fin D.size, (ends (trimFamily D i hlong j) +
        if j = i then (if (D.path i).start = w then 1 else 0) else 0)) =
      ∑ j : Fin D.size, (ends (D.path j) +
        if j = i then (if (D.path i).walk.snd = w then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simpa [trimFamily, ends] using (D.path i).trimFirst_endpoint_contribution hlong w
    · simp [trimFamily, hji, ends, NonemptyPath.transfer]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  change (∑ j : Fin D.size, ends (trimFamily D i hlong j)) +
    (if (D.path i).start = w then 1 else 0) =
    (∑ j : Fin D.size, ends (D.path j)) + if (D.path i).walk.snd = w then 1 else 0
  exact hsum

end Gallai.Decomposition
