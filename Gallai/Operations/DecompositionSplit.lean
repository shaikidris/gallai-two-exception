/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Split
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Splitting one decomposition carrier

Replace a path by its two nonempty pieces. Other carriers may share vertices
with either piece; only unique edge coverage is required and preserved.
-/

namespace Gallai.Decomposition

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

attribute [local simp] Fin.lastCases_castSucc Fin.lastCases_last

def splitFamily (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) : Fin (D.size + 1) → NonemptyPath G :=
  Fin.lastCases ((D.path i).dropFrom v hv ht)
    (fun j => if j = i then (D.path i).takeTo v hv hs else D.path j)

theorem splitFamily_covers (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) :
    ∀ e ∈ G.edgeSet, ∃! j, e ∈ (splitFamily D i v hv hs ht j).walk.edges := by
  intro e he
  obtain ⟨j, hj, huniq⟩ := D.covers e he
  have hleft := (D.path i).walk.edges_takeUntil_subset_edges hv
  have hright := (D.path i).walk.edges_dropUntil_subset_edges hv
  have hdisj := (D.path i).disjoint_prefix_suffix_edges v hv hs ht
  have hself : (splitFamily D i v hv hs ht i.castSucc).walk.edges =
      ((D.path i).takeTo v hv hs).walk.edges :=
    congrArg (fun P : NonemptyPath G => P.walk.edges) (by simp [splitFamily])
  have hlast : (splitFamily D i v hv hs ht (Fin.last D.size)).walk.edges =
      ((D.path i).dropFrom v hv ht).walk.edges :=
    congrArg (fun P : NonemptyPath G => P.walk.edges) (by simp [splitFamily])
  have hother (l : Fin D.size) (hli : l ≠ i) :
      (splitFamily D i v hv hs ht l.castSucc).walk.edges = (D.path l).walk.edges :=
    congrArg (fun P : NonemptyPath G => P.walk.edges) (by simp [splitFamily, hli])
  by_cases hji : j = i
  · subst j
    rw [← (D.path i).prefix_edges_append_suffix_edges v hv hs ht, List.mem_append] at hj
    rcases hj with hj | hj
    · refine ⟨i.castSucc, ?_, ?_⟩
      · change e ∈ (splitFamily D i v hv hs ht i.castSucc).walk.edges
        rw [hself]
        exact hj
      intro k hk
      refine Fin.lastCases ?_ (fun l => ?_) k hk
      · intro heLast
        exact False.elim (hdisj hj (hlast ▸ heLast))
      · intro hl
        by_cases hli : l = i
        · simp [hli]
        · have hold : e ∈ (D.path l).walk.edges := hother l hli ▸ hl
          exact False.elim (hli (huniq l hold))
    · refine ⟨Fin.last D.size, ?_, ?_⟩
      · change e ∈ (splitFamily D i v hv hs ht (Fin.last D.size)).walk.edges
        rw [hlast]
        exact hj
      intro k hk
      refine Fin.lastCases ?_ (fun l => ?_) k hk
      · intro _
        rfl
      · intro hl
        by_cases hli : l = i
        · subst l
          exact False.elim (hdisj (hself ▸ hl) hj)
        · have hold : e ∈ (D.path l).walk.edges := hother l hli ▸ hl
          exact False.elim (hli (huniq l hold))
  · refine ⟨j.castSucc, ?_, ?_⟩
    · change e ∈ (splitFamily D i v hv hs ht j.castSucc).walk.edges
      rw [hother j hji]
      exact hj
    intro k hk
    refine Fin.lastCases ?_ (fun l => ?_) k hk
    · intro heLast
      have hold : e ∈ (D.path i).walk.edges := hright (hlast ▸ heLast)
      exact False.elim (hji (huniq i hold).symm)
    · intro hl
      by_cases hli : l = i
      · subst l
        have hold : e ∈ (D.path i).walk.edges := hleft (hself ▸ hl)
        exact False.elim (hji (huniq i hold).symm)
      · have hold : e ∈ (D.path l).walk.edges := hother l hli ▸ hl
        exact congrArg Fin.castSucc (huniq l hold)

/-- Split an indexed carrier at an internal vertex, keeping all other paths. -/
def splitAt (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) : Decomposition G where
  size := D.size + 1
  path := splitFamily D i v hv hs ht
  covers := splitFamily_covers D i v hv hs ht

/-- Splitting an internal vertex increases the path count by exactly one. -/
@[simp] theorem splitAt_size (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) : (D.splitAt i v hv hs ht).size = D.size + 1 := rfl

/-- A carrier other than the split carrier is preserved verbatim. -/
theorem splitAt_path_of_ne (D : Decomposition G) (i j : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) (hji : j ≠ i) :
    (D.splitAt i v hv hs ht).path j.castSucc = D.path j := by
  simp [splitAt, splitFamily, hji]

/-- Splitting creates two endpoints at the cut and preserves all other counts. -/
theorem splitAt_endpointCount (D : Decomposition G) (i : Fin D.size) (v : V)
    (hv : v ∈ (D.path i).walk.support) (hs : (D.path i).start ≠ v)
    (ht : v ≠ (D.path i).finish) (w : V) :
    (D.splitAt i v hv hs ht).endpointCount w =
      D.endpointCount w + if v = w then 2 else 0 := by
  let ends (P : NonemptyPath G) :=
    (if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0 : ℕ)
  have hsum :
      (∑ j : Fin D.size, (ends (if j = i then (D.path i).takeTo v hv hs else D.path j) +
        if j = i then ends ((D.path i).dropFrom v hv ht) else 0)) =
      ∑ j : Fin D.size, (ends (D.path j) + if j = i then (if v = w then 2 else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j = i
    · subst j
      simpa [ends] using (D.path i).split_endpoint_contribution v hv hs ht w
    · simp [hji]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  change (∑ j : Fin (D.size + 1), ends (splitFamily D i v hv hs ht j)) = _
  rw [Fin.sum_univ_castSucc]
  simpa only [splitFamily, Fin.lastCases_castSucc, Fin.lastCases_last,
    endpointCount, ends] using hsum

end Gallai.Decomposition
