/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # Deleting the edges of a path

The long-corridor case removes an entire simple even-subgraph path before
attaching its terminal repair edges.  This file gives that operation a stable
graph-level interface.  It deliberately records only the literal deleted
edge set and its exact restoration; parity and component arguments belong to
the later corridor auxiliary.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete precisely the distinct edges traversed by a walk. -/
def walkPuncture {u v : V} (p : G.Walk u v) : SimpleGraph V :=
  G.deleteEdges p.edges.toFinset

@[simp]
theorem walkPuncture_le {u v : V} (p : G.Walk u v) : walkPuncture G p ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- The puncture keeps exactly the original edges not traversed by the walk. -/
theorem walkPuncture_adj_iff {u v x y : V} (p : G.Walk u v) :
    (walkPuncture G p).Adj x y ↔ G.Adj x y ∧ s(x, y) ∉ p.edges := by
  simp [walkPuncture]

/-- An original edge crossing a connected component of a path puncture was
deleted by that puncture.  This is the component-boundary interface used in
corridor SET audits. -/
theorem walkPuncture_component_crossing_is_deleted
    {u v s t : V} (p : G.Walk u v)
    (C : (walkPuncture G p).ConnectedComponent)
    (hs : s ∈ C.supp) (ht : t ∉ C.supp) (hst : G.Adj s t) :
    s(s, t) ∈ p.edges := by
  by_contra hnot
  have hpuncture : (walkPuncture G p).Adj s t :=
    (walkPuncture_adj_iff G p).mpr ⟨hst, hnot⟩
  exact ht (C.mem_supp_of_adj_mem_supp hs hpuncture)

/-- If a punctured-path component contains none of the positive-index path
vertices, its only possible original boundary edge is the first path edge.
This localizes a surviving SET component to the corridor start. -/
theorem walkPuncture_component_crossing_is_start_edge
    {u v s t : V} (p : G.Walk u v)
    (C : (walkPuncture G p).ConnectedComponent)
    (hno : ∀ i : ℕ, 0 < i → i ≤ p.length → p.getVert i ∉ C.supp)
    (hs : s ∈ C.supp) (ht : t ∉ C.supp) (hst : G.Adj s t) :
    s = u ∧ t = p.snd := by
  obtain ⟨i, hi, he⟩ := p.mk_mem_edges_iff_exists.mp
    (walkPuncture_component_crossing_is_deleted G p C hs ht hst)
  rcases Sym2.eq_iff.mp he with h | h
  · have hi0 : i = 0 := by
      by_contra hi0
      exact hno i (Nat.pos_of_ne_zero hi0) (Nat.le_of_lt hi) (h.1 ▸ hs)
    subst i
    exact ⟨by simpa using h.1.symm, by simpa [SimpleGraph.Walk.snd] using h.2.symm⟩
  · exact False.elim (hno (i + 1) (by omega) (by omega) (h.2 ▸ hs))

/-- If a punctured component contains the initial endpoint and another
vertex, while every original boundary edge is forced to be the first path
edge, then deleting the initial endpoint disconnects the original graph.
This is the graph-theoretic consumer of the first-edge-only boundary
classification in corridor arguments. -/
theorem walkPuncture_start_component_forces_not_connected
    {u v t : V} (p : G.Walk u v)
    (C : (walkPuncture G p).ConnectedComponent)
    (hno : ∀ i : ℕ, 0 < i → i ≤ p.length → p.getVert i ∉ C.supp)
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (htC : t ∈ C.supp) (htu : t ≠ u) :
    ¬ (G.induce {z | z ≠ u}).Connected := by
  have hlen : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
  have hvu : p.snd ≠ u := by
    intro hvu
    have hvertices : p.getVert 1 = p.getVert 0 := by
      simpa [SimpleGraph.Walk.snd] using hvu
    have hindex := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hvertices
    omega
  have hvC : p.snd ∉ C.supp := by
    simpa [SimpleGraph.Walk.snd] using hno 1 (by omega) (by omega)
  intro hconn
  have hreach : (G.induce {z | z ≠ u}).Reachable ⟨p.snd, hvu⟩ ⟨t, htu⟩ :=
    hconn ⟨p.snd, hvu⟩ ⟨t, htu⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hnoenter : ∀ {s w : {z : V | z ≠ u}},
      s.val ∉ C.supp → w.val ∈ C.supp →
        (G.induce {z | z ≠ u}).Adj s w → False := by
    intro s w hs hw hsw
    have hcross := walkPuncture_component_crossing_is_start_edge G p C hno hw hs hsw.symm
    exact w.property hcross.1
  have hstay : ∀ {w : {z : V | z ≠ u}},
      Relation.ReflTransGen (G.induce {z | z ≠ u}).Adj ⟨p.snd, hvu⟩ w →
        w.val ∉ C.supp := by
    intro w hw
    induction hw with
    | refl => exact hvC
    | tail _ hsw ih => exact fun hwC => hnoenter ih hwC hsw
  exact hstay hreach htC

/-- In a connected original graph, every component of a path puncture meets
the deleted path support.  Otherwise that component is closed under every
original edge and cannot be connected to the initial path endpoint. -/
theorem walkPuncture_component_meets_deleted_support
    {u v : V} (p : G.Walk u v)
    (C : (walkPuncture G p).ConnectedComponent)
    (hconn : G.Connected) :
    ∃ z : V, z ∈ C.supp ∧ z ∈ p.support := by
  by_contra hnone
  obtain ⟨s, hs⟩ := C.nonempty_supp
  have hclosed : ∀ r w : V, r ∈ C.supp → G.Adj r w → w ∈ C.supp := by
    intro r w hr hrw
    by_contra hw
    exact hnone ⟨r, hr,
      p.fst_mem_support_of_mem_edges
        (walkPuncture_component_crossing_is_deleted G p C hr hw hrw)⟩
  have hreach : G.Reachable s u := hconn s u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {w : V}, Relation.ReflTransGen G.Adj s w → w ∈ C.supp := by
    intro w hw
    induction hw with
    | refl => exact hs
    | tail _ hrw ih => exact hclosed _ _ ih hrw
  exact hnone ⟨u, hpreserve hreach, p.start_mem_support⟩

/-- Every traversed walk edge was an original graph edge. -/
theorem walk_edges_subset_edgeFinset {u v : V} (p : G.Walk u v) :
    p.edges.toFinset ⊆ G.edgeFinset := by
  intro e he
  apply SimpleGraph.mem_edgeFinset.mpr
  apply p.edges_subset_edgeSet
  simpa using he

/-- Deleting a walk's traversed edges and restoring that same finite edge set
recovers the original graph.  This gives the later corridor reconstruction a
single equality rather than an induction over individual deleted edges. -/
theorem walkPuncture_sup_fromEdgeSet_eq {u v : V} (p : G.Walk u v) :
    walkPuncture G p ⊔ SimpleGraph.fromEdgeSet (p.edges.toFinset : Set (Sym2 V)) = G := by
  ext x y
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · exact (walkPuncture_adj_iff G p).mp hxy |>.1
    · have hxy' : s(x, y) ∈ p.edges.toFinset ∧ x ≠ y := by
        simpa [SimpleGraph.fromEdgeSet] using hxy
      have hmem : s(x, y) ∈ p.edges.toFinset := hxy'.1
      exact SimpleGraph.mem_edgeFinset.mp (walk_edges_subset_edgeFinset G p hmem)
  · intro hxy
    by_cases hmem : s(x, y) ∈ p.edges
    · right
      have hne : x ≠ y := (p.adj_of_mem_edges hmem).ne
      simpa [SimpleGraph.fromEdgeSet] using And.intro hmem hne
    · left
      exact (walkPuncture_adj_iff G p).mpr ⟨hxy, hmem⟩

/-- A simple path has one distinct deleted edge per step. -/
theorem walkPuncture_card_eq_length {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.edges.toFinset.card = p.length := by
  rw [← SimpleGraph.Walk.length_edges p]
  exact List.toFinset_card_of_nodup hp.edges_nodup

/-- At the initial endpoint of a nontrivial simple path, the puncture deletes
exactly the first path edge and no other incident edge. -/
theorem neighborFinset_walkPuncture_start {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath) (hnil : ¬ p.Nil) :
    (walkPuncture G p).neighborFinset u = (G.neighborFinset u).erase p.snd := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  rw [walkPuncture_adj_iff]
  constructor
  · rintro ⟨huw, hnot⟩
    refine ⟨?_, huw⟩
    intro hws
    subst w
    exact hnot (p.mk_start_snd_mem_edges hnil)
  · rintro ⟨hne, huw⟩
    refine ⟨huw, ?_⟩
    intro he
    exact hne (hp.eq_snd_of_mem_edges he)

/-- At the terminal endpoint of a nontrivial simple path, the puncture
deletes exactly the final path edge and no other incident edge. -/
theorem neighborFinset_walkPuncture_end {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath) (hnil : ¬ p.Nil) :
    (walkPuncture G p).neighborFinset v = (G.neighborFinset v).erase p.penultimate := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  rw [walkPuncture_adj_iff]
  constructor
  · rintro ⟨hvw, hnot⟩
    refine ⟨?_, hvw⟩
    intro hwp
    subst w
    exact hnot (by
      simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hnil)
  · rintro ⟨hne, hvw⟩
    refine ⟨hvw, ?_⟩
    intro he
    exact hne (hp.eq_penultimate_of_mem_edges he)

/-- Deleting a nontrivial simple path flips parity at its initial endpoint. -/
theorem degree_walkPuncture_start_add_one {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath) (hnil : ¬ p.Nil) :
    (walkPuncture G p).degree u + 1 = G.degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_walkPuncture_start G p hp hnil,
    ← G.card_neighborFinset_eq_degree u]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset u p.snd).mpr
      (p.adj_of_mem_edges (p.mk_start_snd_mem_edges hnil)))

/-- Deleting a nontrivial simple path flips parity at its terminal endpoint. -/
theorem degree_walkPuncture_end_add_one {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath) (hnil : ¬ p.Nil) :
    (walkPuncture G p).degree v + 1 = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_walkPuncture_end G p hp hnil,
    ← G.card_neighborFinset_eq_degree v]
  exact Finset.card_erase_add_one
    ((G.mem_neighborFinset v p.penultimate).mpr
      (p.adj_of_mem_edges (p.mk_penultimate_end_mem_edges hnil)).symm)

/-- At an internal vertex of a simple path, the puncture deletes exactly the
two path edges incident with that vertex. -/
theorem neighborFinset_walkPuncture_internal {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    (walkPuncture G p).neighborFinset (p.getVert i) =
      ((G.neighborFinset (p.getVert i)).erase (p.getVert (i - 1))).erase
        (p.getVert (i + 1)) := by
  have hprev_index : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)
  have hprev_edge : s(p.getVert i, p.getVert (i - 1)) ∈ p.edges := by
    rw [Sym2.eq_swap]
    apply p.mk_mem_edges_iff_exists.mpr
    refine ⟨i - 1, by omega, ?_⟩
    rw [hprev_index]
  have hnext_edge : s(p.getVert i, p.getVert (i + 1)) ∈ p.edges := by
    apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨i, hiend, rfl⟩
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  rw [walkPuncture_adj_iff]
  constructor
  · rintro ⟨hadj, hnot⟩
    refine ⟨?_, ?_, hadj⟩
    · intro hw
      subst w
      exact hnot hnext_edge
    · intro hw
      subst w
      exact hnot hprev_edge
  · rintro ⟨hnext, hprev, hadj⟩
    refine ⟨hadj, ?_⟩
    intro hedge
    rcases p.mk_mem_edges_iff_exists.mp hedge with ⟨j, hj, hej⟩
    rcases Sym2.eq_iff.mp hej with hji | hji
    · have hj_eq : j = i := hp.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hji.1
      subst j
      exact hnext hji.2.symm
    · have hj_succ_eq : j + 1 = i := hp.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hji.2
      have hj_eq : j = i - 1 := by omega
      subst j
      exact hprev hji.1.symm

/-- Puncturing a simple path lowers the degree of each internal vertex by two. -/
theorem degree_walkPuncture_internal_add_two {u v : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hp : p.IsPath)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    (walkPuncture G p).degree (p.getVert i) + 2 = G.degree (p.getVert i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_walkPuncture_internal G p hp i hi hiend,
    ← G.card_neighborFinset_eq_degree (p.getVert i)]
  have hprev_ne_next : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro heq
    have : i - 1 = i + 1 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) heq
    omega
  have hprev_adj : G.Adj (p.getVert (i - 1)) (p.getVert i) := by
    rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]
    exact p.adj_getVert_succ (i := i - 1) (by omega)
  have hnext_adj : G.Adj (p.getVert i) (p.getVert (i + 1)) :=
    p.adj_getVert_succ (i := i) hiend
  have hprev_mem : p.getVert (i - 1) ∈ G.neighborFinset (p.getVert i) := by
    exact (G.mem_neighborFinset _ _).mpr hprev_adj.symm
  have hnext_mem : p.getVert (i + 1) ∈
      (G.neighborFinset (p.getVert i)).erase (p.getVert (i - 1)) := by
    simp only [Finset.mem_erase]
    exact ⟨hprev_ne_next.symm, (G.mem_neighborFinset _ _).mpr hnext_adj⟩
  have hcard : 2 ≤ (G.neighborFinset (p.getVert i)).card := by
    calc
      2 = ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card := by
        simp [hprev_ne_next]
      _ ≤ (G.neighborFinset (p.getVert i)).card := by
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hprev_mem
        · exact (G.mem_neighborFinset _ _).mpr hnext_adj
  rw [Finset.card_erase_of_mem hnext_mem, Finset.card_erase_of_mem hprev_mem]
  omega

/-- A vertex outside a walk's support is untouched by the walk puncture. -/
theorem neighborFinset_walkPuncture_of_not_mem_support {u v z : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hz : z ∉ p.support) :
    (walkPuncture G p).neighborFinset z = G.neighborFinset z := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  rw [walkPuncture_adj_iff]
  constructor
  · exact fun h => h.1
  · intro hzw
    refine ⟨hzw, ?_⟩
    intro he
    exact hz (p.fst_mem_support_of_mem_edges he)

/-- Consequently, a vertex outside the deleted walk support has unchanged
degree and hence unchanged parity. -/
theorem degree_walkPuncture_of_not_mem_support {u v z : V} (p : G.Walk u v)
    [DecidableRel (walkPuncture G p).Adj] (hz : z ∉ p.support) :
    (walkPuncture G p).degree z = G.degree z := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_walkPuncture_of_not_mem_support G p hz,
    ← SimpleGraph.card_neighborFinset_eq_degree]

/-- If every deleted-path vertex was originally even, then every surviving
even neighbour in the puncture was already an even neighbour in the original
graph. -/
theorem evenNeighbors_walkPuncture_subset_of_even_support
    {u v w : V} (p : G.Walk u v) [DecidableRel (walkPuncture G p).Adj]
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z)) :
    evenNeighbors (walkPuncture G p) w ⊆ evenNeighbors G w := by
  intro z hz
  obtain ⟨hwz, hzEven⟩ := (mem_evenNeighbors (G := walkPuncture G p) w z).mp hz
  have hwzG : G.Adj w z := (walkPuncture_adj_iff G p).mp hwz |>.1
  have hzEvenG : Even (G.degree z) := by
    by_cases hzSupport : z ∈ p.support
    · exact hsupport z hzSupport
    · rw [degree_walkPuncture_of_not_mem_support G p hzSupport] at hzEven
      exact hzEven
  exact (mem_evenNeighbors (G := G) w z).mpr ⟨hwzG, hzEvenG⟩

end Gallai
