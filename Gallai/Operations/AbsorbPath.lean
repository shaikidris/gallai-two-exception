/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.EraseCarrier
public import Gallai.Operations.Orient
public import Gallai.Operations.Concatenate
public import Gallai.Operations.DecompositionInduce
public import Gallai.Operations.Split
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section

/-! # Absorb a path at an exposed endpoint with exact family accounting -/

namespace Gallai.Decomposition

universe u
variable {V : Type u} [DecidableEq V] {G H : SimpleGraph V}

private def absorbFamily (D : Decomposition G) (P : NonemptyPath H) (i : Fin D.size)
    (hle : G ≤ H) (hj : (D.path i).finish = P.start)
    (hint : ∀ w, w ∈ (D.path i).walk.support → w ∈ P.walk.support → w = P.start)
    (j : Fin D.size) : NonemptyPath H :=
  if j = i then
    ((D.path i).transfer H (fun _ he =>
      SimpleGraph.edgeSet_mono hle ((D.path i).walk.edges_subset_edgeSet he))).append
      P hj (fun w hw hp => (hint w (by simpa using hw) hp).trans hj.symm)
  else (D.path j).transfer H (fun _ he =>
    SimpleGraph.edgeSet_mono hle ((D.path j).walk.edges_subset_edgeSet he))

omit [DecidableEq V] in
private theorem absorbFamily_edges (D : Decomposition G) (P : NonemptyPath H)
    (i : Fin D.size) (hle : G ≤ H) (hj : (D.path i).finish = P.start)
    (hint : ∀ w, w ∈ (D.path i).walk.support → w ∈ P.walk.support → w = P.start)
    (j : Fin D.size) (e : Sym2 V) :
    e ∈ (absorbFamily D P i hle hj hint j).walk.edges ↔
      e ∈ (D.path j).walk.edges ∨ j = i ∧ e ∈ P.walk.edges := by
  unfold absorbFamily
  split_ifs with he
  · subst j
    rw [if_pos rfl]
    simp only [NonemptyPath.append, NonemptyPath.transfer, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_transfer, List.mem_append,
      true_and]
  · rw [if_neg he]
    simp [he]

/-- A terminal carrier can absorb a disjoint-edge path at its sole shared vertex. -/
theorem absorb_at_terminal (D : Decomposition G) (P : NonemptyPath H) (i : Fin D.size)
    (hle : G ≤ H) (hj : (D.path i).finish = P.start)
    (hint : ∀ w, w ∈ (D.path i).walk.support → w ∈ P.walk.support → w = P.start)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + (if P.start = w then 1 else 0) =
        D.endpointCount w + (if P.finish = w then 1 else 0) := by
  classical
  let paths := absorbFamily D P i hle hj hint
  have hcover : ∀ e ∈ H.edgeSet, ∃! j, e ∈ (paths j).walk.edges := by
    intro e he
    rcases (hedges e).mp he with he | he
    · obtain ⟨j, hj', hu⟩ := D.covers e he
      refine ⟨j, (absorbFamily_edges D P i hle hj hint j e).mpr (Or.inl hj'), ?_⟩
      intro k hk
      rcases (absorbFamily_edges D P i hle hj hint k e).mp hk with hk | hk
      · exact hu k hk
      · exact (hdis e hk.2 he).elim
    · refine ⟨i, (absorbFamily_edges D P i hle hj hint i e).mpr (Or.inr ⟨rfl, he⟩), ?_⟩
      intro k hk
      rcases (absorbFamily_edges D P i hle hj hint k e).mp hk with hk | hk
      · exact (hdis e he ((D.path k).walk.edges_subset_edgeSet hk)).elim
      · exact hk.1
  refine ⟨ofFamily paths hcover, by simp, ?_⟩
  intro w
  rw [ofFamily_endpointCount]
  have hrow (j : Fin D.size) :
      ((if (paths j).start = w then 1 else 0) + (if (paths j).finish = w then 1 else 0)) +
        (if j = i then (if P.start = w then 1 else 0) else 0) =
      ((if (D.path j).start = w then 1 else 0) + (if (D.path j).finish = w then 1 else 0)) +
        (if j = i then (if P.finish = w then 1 else 0) else 0 : ℕ) := by
    by_cases hji : j = i
    · subst j
      simp only [paths, absorbFamily, NonemptyPath.append,
        NonemptyPath.transfer, hj, ite_true]
      omega
    · simp [paths, absorbFamily, hji, NonemptyPath.transfer]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hrow j)
  simpa [Finset.sum_add_distrib, endpointCount] using hs

/-- Positive endpoint supply selects a carrier automatically, then absorbs the path. -/
theorem absorb_path (D : Decomposition G) (P : NonemptyPath H)
    (hle : G ≤ H) (hpos : 0 < D.endpointCount P.start)
    (hint : ∀ i w, w ∈ (D.path i).walk.support → w ∈ P.walk.support → w = P.start)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + (if P.start = w then 1 else 0) =
        D.endpointCount w + (if P.finish = w then 1 else 0) := by
  classical
  have hex : ∃ i, (D.path i).start = P.start ∨ (D.path i).finish = P.start := by
    by_contra hn
    have hz : D.endpointCount P.start = 0 := by
      unfold endpointCount
      apply Finset.sum_eq_zero
      intro i _
      have hs : (D.path i).start ≠ P.start := fun he => hn ⟨i, Or.inl he⟩
      have ht : (D.path i).finish ≠ P.start := fun he => hn ⟨i, Or.inr he⟩
      simp [hs, ht]
    omega
  obtain ⟨i, hi⟩ := hex
  have hinter (w : V) (hw : w ∈ ((D.orientToward P.start).path i).walk.support)
      (hp : w ∈ P.walk.support) : w = P.start :=
    hint i w (((D.path i).mem_toward_support P.start w).mp hw) hp
  obtain ⟨E, hs, hv⟩ := (D.orientToward P.start).absorb_at_terminal P i hle
    (D.orientToward_terminal P.start i hi) hinter hedges hdis
  refine ⟨E, hs, ?_⟩
  intro w
  simpa only [orientToward_endpointCount] using hv w

/-- Two arms consume two endpoints without increasing the path count.
The second arm's vertices away from the joint are isolated in the intermediate
graph, so its compatibility is derived for the actual first output. -/
theorem absorb_two_arms {K : SimpleGraph V} (D : Decomposition G)
    (P : NonemptyPath H) (Q : NonemptyPath K)
    (hj : Q.start = P.start) (hreserve : 2 ≤ D.endpointCount P.start)
    (hGH : G ≤ H) (hHK : H ≤ K)
    (hint : ∀ i w, w ∈ (D.path i).walk.support → w ∈ P.walk.support → w = P.start)
    (hP : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdP : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet)
    (hQ : ∀ e, e ∈ K.edgeSet ↔ e ∈ H.edgeSet ∨ e ∈ Q.walk.edges)
    (hdQ : ∀ e ∈ Q.walk.edges, e ∉ H.edgeSet)
    (hiso : ∀ w ∈ Q.walk.support, w ≠ Q.start → ∀ v, ¬ H.Adj w v) :
    ∃ E : Decomposition K, E.size = D.size ∧ ∀ w,
      E.endpointCount w + 2 * (if P.start = w then 1 else 0) =
        D.endpointCount w + (if P.finish = w then 1 else 0) +
          (if Q.finish = w then 1 else 0) := by
  obtain ⟨E, hs, hv⟩ := D.absorb_path P hGH (by omega) hint hP hdP
  have hpos : 0 < E.endpointCount Q.start := by
    have h := hv P.start
    simp only [ite_true] at h
    rw [hj]
    omega
  have hinter : ∀ i w, w ∈ (E.path i).walk.support →
      w ∈ Q.walk.support → w = Q.start := by
    intro i w hw hq
    by_contra hn
    exact (E.path i).notMem_support_of_isolated w (hiso w hq hn) hw
  obtain ⟨F, ht, hw⟩ := E.absorb_path Q hHK hpos hinter hQ hdQ
  refine ⟨F, ht.trans hs, ?_⟩
  intro w
  have h₁ := hv w
  have h₂ := hw w
  rw [hj] at h₂
  omega

/-- An internally attached simple path is absorbed within the original budget.
All vertices of the attached path other than its joint are isolated in the
old graph. The intermediate graph and both carriers are constructed here. -/
theorem absorb_internal_path_endpoints (D : Decomposition G) (P : NonemptyPath H)
    (v : V) (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ P.walk.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if P.start = w then 1 else 0) +
          (if P.finish = w then 1 else 0) := by
  classical
  let L := (P.takeTo v hv hs).reverse
  let R := P.dropFrom v hv ht
  let J := G ⊔ L.walk.toSubgraph.spanningCoe
  have hJL : ∀ e, e ∈ J.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ L.walk.edges := by
    intro e
    simp only [J, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  have hLsub : ∀ w ∈ L.walk.support, w ∈ P.walk.support := by
    intro w hw
    have hw' : w ∈ (P.walk.takeUntil v hv).support := by
      simpa [L, NonemptyPath.reverse, NonemptyPath.takeTo] using hw
    exact P.walk.support_takeUntil_subset_support hv hw'
  have hRsub : ∀ w ∈ R.walk.support, w ∈ P.walk.support :=
    fun _ hw => P.walk.support_dropUntil_subset_support hv hw
  have hparts (e : Sym2 V) : e ∈ P.walk.edges ↔
      e ∈ L.walk.edges ∨ e ∈ R.walk.edges := by
    rw [← P.prefix_edges_append_suffix_edges v hv hs ht]
    simp [L, R]
  have hLR : ∀ e ∈ R.walk.edges, e ∉ L.walk.edges := by
    intro e he hr
    have hr' : e ∈ (P.takeTo v hv hs).walk.edges := by simpa [L] using hr
    exact (P.disjoint_prefix_suffix_edges v hv hs ht) hr' he
  have hJH : J ≤ H := sup_le hle L.walk.toSubgraph.spanningCoe_le
  let L' := L.transfer J (fun e he => (hJL e).mpr (Or.inr he))
  have hinter : ∀ i w, w ∈ (D.path i).walk.support →
      w ∈ L'.walk.support → w = L'.start := by
    intro i w hw hl
    change w = v
    by_contra hn
    have hl' : w ∈ L.walk.support := by simpa [L'] using hl
    exact (D.path i).notMem_support_of_isolated w (hiso w (hLsub w hl') hn) hw
  have hsecond : ∀ w ∈ R.walk.support, w ≠ R.start → ∀ z, ¬ J.Adj w z := by
    intro w hw hn z hadj
    rcases hadj with hg | hl
    · exact hiso w (hRsub w hw) hn z hg
    · have hwl : w ∈ L.walk.support :=
        L.walk.mem_verts_toSubgraph.mp (L.walk.toSubgraph.edge_vert hl)
      have hwl' : w ∈ (P.takeTo v hv hs).walk.support := by
        simpa [L, NonemptyPath.reverse] using hwl
      exact hn ((P.mem_prefix_support_and_suffix_support_iff v hv hs ht w).mp ⟨hwl', hw⟩)
  obtain ⟨E, hsize, hends⟩ := D.absorb_two_arms L' R rfl hreserve le_sup_left hJH
    hinter (by simpa [L'] using hJL)
    (by intro e he; exact hdis e ((hparts e).mpr (Or.inl (by simpa [L'] using he))))
    (by intro e; rw [hedges, hJL, hparts]; tauto)
    (by
      intro e he hj
      rcases (hJL e).mp hj with hg | hl
      · exact hdis e ((hparts e).mpr (Or.inr he)) hg
      · exact hLR e he hl)
    hsecond
  refine ⟨E, hsize, ?_⟩
  intro w
  simpa only [L', L, R, NonemptyPath.transfer, NonemptyPath.reverse,
    NonemptyPath.takeTo, NonemptyPath.dropFrom] using hends w

/-- The count-only form of internal attached-path absorption. -/
theorem absorb_internal_path (D : Decomposition G) (P : NonemptyPath H)
    (v : V) (hv : v ∈ P.walk.support) (hs : P.start ≠ v) (ht : v ≠ P.finish)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ P.walk.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size := by
  obtain ⟨E, hsize, _⟩ := D.absorb_internal_path_endpoints P v hv hs ht
    hreserve hle hedges hdis hiso
  exact ⟨E, hsize⟩

/-- A nonempty attached path is absorbed at any supported attachment vertex.
The endpoint cases require only one arm; the internal case uses both. -/
theorem absorb_attached_path_endpoints (D : Decomposition G) (P : NonemptyPath H)
    (v : V) (hv : v ∈ P.walk.support) (hreserve : 2 ≤ D.endpointCount v)
    (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ P.walk.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if P.start = w then 1 else 0) +
          (if P.finish = w then 1 else 0) := by
  have terminal (Q : NonemptyPath H) (hq : Q.start = v)
      (hqe : ∀ e, e ∈ Q.walk.edges ↔ e ∈ P.walk.edges)
      (hqs : ∀ w, w ∈ Q.walk.support ↔ w ∈ P.walk.support) :
      ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
        E.endpointCount w + 2 * (if v = w then 1 else 0) =
          D.endpointCount w + (if Q.start = w then 1 else 0) +
            (if Q.finish = w then 1 else 0) := by
    have hint : ∀ i w, w ∈ (D.path i).walk.support →
        w ∈ Q.walk.support → w = Q.start := by
      intro i w hw hq'
      rw [hq]
      by_contra hn
      exact (D.path i).notMem_support_of_isolated w
        (hiso w ((hqs w).mp hq') hn) hw
    obtain ⟨E, hs, he⟩ := D.absorb_path Q hle (by rw [hq]; omega) hint
      (by intro e; rw [hedges, hqe])
      (fun e he => hdis e ((hqe e).mp he))
    refine ⟨E, hs, ?_⟩
    intro w
    have h := he w
    simp only [hq] at h ⊢
    omega
  by_cases hs : P.start = v
  · exact terminal P hs (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  by_cases ht : v = P.finish
  · obtain ⟨E, hsize, he⟩ := terminal P.reverse ht.symm
      (by intro e; simp) (by intro w; simp [NonemptyPath.reverse])
    refine ⟨E, hsize, ?_⟩
    intro w
    have h : E.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if P.finish = w then 1 else 0) +
          (if P.start = w then 1 else 0) := he w
    calc
      _ = D.endpointCount w + (if P.finish = w then 1 else 0) +
          (if P.start = w then 1 else 0) := h
      _ = _ := by omega
  exact D.absorb_internal_path_endpoints P v hv hs ht hreserve hle hedges hdis hiso

/-- Count-only attached-path absorption, retaining its original interface. -/
theorem absorb_attached_path (D : Decomposition G) (P : NonemptyPath H)
    (v : V) (hv : v ∈ P.walk.support) (hreserve : 2 ≤ D.endpointCount v)
    (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ P.walk.edges)
    (hdis : ∀ e ∈ P.walk.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ P.walk.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size := by
  obtain ⟨E, hs, _⟩ := D.absorb_attached_path_endpoints P v hv hreserve
    hle hedges hdis hiso
  exact ⟨E, hs⟩

/-- Attached-path absorption also permits a trivial path, which adds no edges. -/
theorem absorb_attached_walk_endpoints {a b : V} (D : Decomposition G) (p : H.Walk a b)
    (hp : p.IsPath) (v : V) (hv : v ∈ p.support)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ p.edges)
    (hdis : ∀ e ∈ p.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ p.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if a = w then 1 else 0) +
          (if b = w then 1 else 0) := by
  by_cases hn : p.Nil
  · cases p with
    | nil =>
      have hEq : H = G := by
        apply SimpleGraph.edgeSet_injective
        ext e
        simpa using hedges e
      subst H
      have hva : v = a := by simpa using hv
      refine ⟨D, rfl, ?_⟩
      intro w
      rw [hva]
      omega
    | cons h p => exact (SimpleGraph.Walk.not_nil_cons hn).elim
  · exact D.absorb_attached_path_endpoints ⟨a, b, p, hp, hn⟩ v hv hreserve
      hle hedges hdis hiso

/-- Count-only absorption including trivial attached walks. -/
theorem absorb_attached_walk {a b : V} (D : Decomposition G) (p : H.Walk a b)
    (hp : p.IsPath) (v : V) (hv : v ∈ p.support)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ p.edges)
    (hdis : ∀ e ∈ p.edges, e ∉ G.edgeSet)
    (hiso : ∀ w ∈ p.support, w ≠ v → ∀ z, ¬ G.Adj w z) :
    ∃ E : Decomposition H, E.size = D.size := by
  obtain ⟨E, hs, _⟩ := D.absorb_attached_walk_endpoints p hp v hv hreserve
    hle hedges hdis hiso
  exact ⟨E, hs⟩

/-- A literal single-vertex intersection derives edge disjointness and isolation. -/
theorem absorb_walk_of_vertex_intersection_endpoints {a b : V} (D : Decomposition G)
    (p : H.Walk a b) (hp : p.IsPath) (v : V) (hv : v ∈ p.support)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ p.edges)
    (hmeet : ∀ w ∈ p.support, (∃ z, G.Adj w z) → w = v) :
    ∃ E : Decomposition H, E.size = D.size ∧ ∀ w,
      E.endpointCount w + 2 * (if v = w then 1 else 0) =
        D.endpointCount w + (if a = w then 1 else 0) +
          (if b = w then 1 else 0) := by
  apply D.absorb_attached_walk_endpoints p hp v hv hreserve hle hedges
  · intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro he hg
      have hab : G.Adj a b := hg
      have ha := hmeet a (p.fst_mem_support_of_mem_edges he) ⟨b, hab⟩
      have hb := hmeet b (p.snd_mem_support_of_mem_edges he) ⟨a, hab.symm⟩
      exact hab.ne (ha.trans hb.symm)
  · intro w hw hn z hz
    exact hn (hmeet w hw ⟨z, hz⟩)

/-- Count-only form of absorption at a literal single-vertex intersection. -/
theorem absorb_walk_of_vertex_intersection {a b : V} (D : Decomposition G)
    (p : H.Walk a b) (hp : p.IsPath) (v : V) (hv : v ∈ p.support)
    (hreserve : 2 ≤ D.endpointCount v) (hle : G ≤ H)
    (hedges : ∀ e, e ∈ H.edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ p.edges)
    (hmeet : ∀ w ∈ p.support, (∃ z, G.Adj w z) → w = v) :
    ∃ E : Decomposition H, E.size = D.size := by
  obtain ⟨E, hs, _⟩ := D.absorb_walk_of_vertex_intersection_endpoints p hp v hv
    hreserve hle hedges hmeet
  exact ⟨E, hs⟩

end Gallai.Decomposition
