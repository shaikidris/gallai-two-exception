/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareHubDegreeThree
public import Gallai.TwoException.ComponentBudget
public import Gallai.Structure.EdgeDeletion

@[expose] public section

/-! # Terminal ledger for an E-degree-one private vertex

The degree-one branch of the bare-hub normal-form argument punctures the
unique even edge at its terminal.  This module records the local parity
ledger independently of the later path-and-pendant reconstruction: the
terminal becomes odd and has no remaining even neighbour.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting the unique even incident edge of an even vertex makes that
vertex odd and removes every even neighbour.  This is the local terminal
invariant used by the degree-one private-vertex corridor puncture. -/
theorem eDegree_one_terminal_puncture
    (a b : V) (hab : G.Adj a b)
    (ha : Even (G.degree a)) (hb : Even (G.degree b))
    (hone : eDegree G a = 1) :
    Odd ((G.deleteEdges {s(a, b)}).degree a) ∧
      eDegree (G.deleteEdges {s(a, b)}) a = 0 := by
  let J : SimpleGraph V := G.deleteEdges {s(a, b)}
  have hodd : Odd (J.degree a) := by
    have hdeg := degree_delete_edge_add_one G a b hab
    rw [Nat.even_iff] at ha
    rw [Nat.odd_iff]
    dsimp [J]
    omega
  refine ⟨hodd, ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hac, hcEven⟩ := (mem_evenNeighbors (G := J) a c).mp hc
  have hacG : G.Adj a c := (SimpleGraph.deleteEdges_adj.mp hac).1
  have hca : c ≠ a := hac.ne.symm
  have hcb : c ≠ b := by
    intro hcb
    subst c
    have hdeg := degree_delete_edge_add_one G b a hab.symm
    rw [Sym2.eq_swap] at hdeg
    have hoddB : Odd (J.degree b) := by
      rw [Nat.even_iff] at hb
      rw [Nat.odd_iff]
      dsimp [J]
      omega
    exact (Nat.not_even_iff_odd.mpr hoddB) hcEven
  have hcEvenG : Even (G.degree c) := by
    rw [degree_delete_edge_of_ne G a b c hca hcb] at hcEven
    exact hcEven
  have hmem : c ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a c).mpr ⟨hacG, hcEvenG⟩
  have hbmem : b ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a b).mpr ⟨hab, hb⟩
  change (evenNeighbors G a).card = 1 at hone
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hone
  have hbd : b = d := by simpa [hd] using hbmem
  have hcd : c = d := by simpa [hd] using hmem
  have : c = b := hcd.trans hbd.symm
  exact hcb this

/-- The connected terminal puncture is not a SET graph: its newly odd
terminal has no even neighbour.  The disconnected corridor case still needs
a componentwise transport of this observation. -/
theorem eDegree_one_terminal_puncture_not_set
    (a b : V) (hab : G.Adj a b)
    (ha : Even (G.degree a)) (hb : Even (G.degree b))
    (hone : eDegree G a = 1) :
    ¬ IsSET (G.deleteEdges {s(a, b)}) := by
  intro hset
  obtain ⟨hodd, hzero⟩ := eDegree_one_terminal_puncture (G := G) a b hab ha hb hone
  exact hset.not_odd_of_eDegree_zero a hodd hzero

/-- The same terminal obstruction is component-local.  A connected component
is neighbour-closed, so inducing it preserves both the terminal degree and
its even-neighbour count.  This is the SET exclusion used when a degree-one
corridor puncture disconnects. -/
theorem eDegree_one_terminal_puncture_component_not_set
    (a b : V) (hab : G.Adj a b)
    (ha : Even (G.degree a)) (hb : Even (G.degree b))
    (hone : eDegree G a = 1)
    (C : (G.deleteEdges {s(a, b)}).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (haC : a ∈ C.supp) :
    ¬ IsSET ((G.deleteEdges {s(a, b)}).induce C.supp) := by
  let J : SimpleGraph V := G.deleteEdges {s(a, b)}
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hvw
    exact C.mem_supp_of_adj_mem_supp hv hvw
  obtain ⟨hodd, hzero⟩ := eDegree_one_terminal_puncture (G := G) a b hab ha hb hone
  have hoddC : Odd ((J.induce C.supp).degree ⟨a, haC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed a haC)]
    exact hodd
  have hzeroC : eDegree (J.induce C.supp) ⟨a, haC⟩ = 0 := by
    rw [eDegree_induce_of_closed J C.supp hclosed]
    exact hzero
  intro hset
  exact hset.not_odd_of_eDegree_zero ⟨a, haC⟩ hoddC hzeroC

/-- Puncturing a nontrivial simple corridor of originally even vertices has
the same terminal effect as deleting the terminal's unique even spoke: if
the terminal has E-degree one in the original graph, it is odd and has no
even neighbour afterwards.  This is the literal auxiliary used by the
degree-one shortest-corridor branch. -/
theorem eDegree_one_terminal_walkPuncture
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1) :
    Odd ((walkPuncture G p).degree a) ∧
      eDegree (walkPuncture G p) a = 0 := by
  have haeven : Even (G.degree a) := hsupport a p.end_mem_support
  have hodd : Odd ((walkPuncture G p).degree a) := by
    have hdegree := degree_walkPuncture_end_add_one G p hp hnil
    rw [Nat.even_iff] at haeven
    rw [Nat.odd_iff]
    omega
  refine ⟨hodd, ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hac, hcEven⟩ := (mem_evenNeighbors (G := walkPuncture G p) a c).mp hc
  have hacG : G.Adj a c := (walkPuncture_adj_iff G p).mp hac |>.1
  have hnotedge : s(a, c) ∉ p.edges := (walkPuncture_adj_iff G p).mp hac |>.2
  have hcEvenG : Even (G.degree c) := by
    by_cases hcSupport : c ∈ p.support
    · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hcSupport
      obtain ⟨i, hi, hile⟩ := hcSupport
      by_cases hi0 : i = 0
      · subst i
        have hcu : c = u := by simpa using hi.symm
        have hueven : Even (G.degree u) := hsupport u p.start_mem_support
        have huodd : Odd ((walkPuncture G p).degree u) := by
          have hdegree := degree_walkPuncture_start_add_one G p hp hnil
          rw [Nat.even_iff] at hueven
          rw [Nat.odd_iff]
          omega
        have hcEvenU : Even ((walkPuncture G p).degree u) := by
          rw [hcu] at hcEven
          exact hcEven
        exact False.elim ((Nat.not_even_iff_odd.mpr huodd) hcEvenU)
      by_cases hilast : i = p.length
      · subst i
        have hca : c = a := by simpa using hi.symm
        exact False.elim (hac.ne hca.symm)
      · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
        have hiLt : i < p.length := Nat.lt_of_le_of_ne hile hilast
        have hdegree := degree_walkPuncture_internal_add_two G p hp i hiPos hiLt
        rw [← hi] at hcEven
        rw [← hi, ← hdegree]
        rw [Nat.even_add]
        exact ⟨fun _ => by simp, fun _ => hcEven⟩
    · rw [degree_walkPuncture_of_not_mem_support G p hcSupport] at hcEven
      exact hcEven
  have hmem : c ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a c).mpr ⟨hacG, hcEvenG⟩
  have hpredAdj : G.Adj a p.penultimate :=
    (p.adj_of_mem_edges (p.mk_penultimate_end_mem_edges hnil)).symm
  have hpredEven : Even (G.degree p.penultimate) :=
    hsupport _ (p.getVert_mem_support (p.length - 1))
  have hpredMem : p.penultimate ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a p.penultimate).mpr ⟨hpredAdj, hpredEven⟩
  change (evenNeighbors G a).card = 1 at hone
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hone
  have hcd : c = d := by simpa [hd] using hmem
  have hpredD : p.penultimate = d := by simpa [hd] using hpredMem
  apply hnotedge
  rw [hcd, ← hpredD]
  simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hnil

/-- An internal all-even corridor vertex of original E-degree two remains
even and becomes E-isolated when the full simple corridor is punctured. -/
theorem eDegree_two_internal_walkPuncture
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (htwo : eDegree G (p.getVert i) = 2) :
    Even ((walkPuncture G p).degree (p.getVert i)) ∧
      eDegree (walkPuncture G p) (p.getVert i) = 0 := by
  let z := p.getVert i
  have hdegree := degree_walkPuncture_internal_add_two G p hp i hi hiend
  have hzevenG : Even (G.degree z) := hsupport z (p.getVert_mem_support i)
  have hzeven : Even ((walkPuncture G p).degree z) := by
    rw [← hdegree] at hzevenG
    exact (Nat.even_add.mp hzevenG).mpr (by simp)
  refine ⟨hzeven, ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hzc, hcEven⟩ := (mem_evenNeighbors (G := walkPuncture G p) z c).mp hc
  have hzcG : G.Adj z c := (walkPuncture_adj_iff G p).mp hzc |>.1
  have hnotedge : s(z, c) ∉ p.edges := (walkPuncture_adj_iff G p).mp hzc |>.2
  have hcEvenG : Even (G.degree c) := by
    by_cases hcSupport : c ∈ p.support
    · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hcSupport
      obtain ⟨j, hj, hjle⟩ := hcSupport
      by_cases hj0 : j = 0
      · subst j
        have hcu : c = u := by simpa using hj.symm
        have hueven : Even (G.degree u) := hsupport u p.start_mem_support
        have huodd : Odd ((walkPuncture G p).degree u) := by
          have hstart := degree_walkPuncture_start_add_one G p hp hnil
          rw [Nat.even_iff] at hueven
          rw [Nat.odd_iff]
          omega
        have hcEvenU : Even ((walkPuncture G p).degree u) := by
          rw [hcu] at hcEven
          exact hcEven
        exact False.elim ((Nat.not_even_iff_odd.mpr huodd) hcEvenU)
      by_cases hjlast : j = p.length
      · subst j
        have hca : c = a := by simpa using hj.symm
        have haeven : Even (G.degree a) := hsupport a p.end_mem_support
        have haodd : Odd ((walkPuncture G p).degree a) := by
          have hend := degree_walkPuncture_end_add_one G p hp hnil
          rw [Nat.even_iff] at haeven
          rw [Nat.odd_iff]
          omega
        have hcEvenA : Even ((walkPuncture G p).degree a) := by
          rw [hca] at hcEven
          exact hcEven
        exact False.elim ((Nat.not_even_iff_odd.mpr haodd) hcEvenA)
      · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
        have hjLt : j < p.length := Nat.lt_of_le_of_ne hjle hjlast
        have hinternal := degree_walkPuncture_internal_add_two G p hp j hjPos hjLt
        rw [← hj] at hcEven
        rw [← hj, ← hinternal]
        rw [Nat.even_add]
        exact ⟨fun _ => by simp, fun _ => hcEven⟩
    · rw [degree_walkPuncture_of_not_mem_support G p hcSupport] at hcEven
      exact hcEven
  have hmem : c ∈ evenNeighbors G z :=
    (mem_evenNeighbors (G := G) z c).mpr ⟨hzcG, hcEvenG⟩
  have hprevne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro hsame
    have hindex := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hsame
    omega
  have hprevAdj : G.Adj z (p.getVert (i - 1)) := by
    rw [show z = p.getVert i by rfl, ← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]
    exact (p.adj_getVert_succ (i := i - 1) (by omega)).symm
  have hnextAdj : G.Adj z (p.getVert (i + 1)) :=
    p.adj_getVert_succ (i := i) hiend
  have hprevEven : Even (G.degree (p.getVert (i - 1))) :=
    hsupport _ (p.getVert_mem_support (i - 1))
  have hnextEven : Even (G.degree (p.getVert (i + 1))) :=
    hsupport _ (p.getVert_mem_support (i + 1))
  have hprevMem : p.getVert (i - 1) ∈ evenNeighbors G z :=
    (mem_evenNeighbors (G := G) z _).mpr ⟨hprevAdj, hprevEven⟩
  have hnextMem : p.getVert (i + 1) ∈ evenNeighbors G z :=
    (mem_evenNeighbors (G := G) z _).mpr ⟨hnextAdj, hnextEven⟩
  have hsubset : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V) ⊆
      evenNeighbors G z := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hprevMem
    · exact hnextMem
  have hpaircard : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V).card = 2 := by
    simp [hprevne]
  have hseteq : ({p.getVert (i - 1), p.getVert (i + 1)} : Finset V) =
      evenNeighbors G z := by
    apply Finset.eq_of_subset_of_card_le hsubset
    have hcard : (evenNeighbors G z).card = 2 := by
      change (evenNeighbors G (p.getVert i)).card = 2 at htwo
      simpa [z] using htwo
    rw [hcard, hpaircard]
  rw [← hseteq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hprev | hnext
  · apply hnotedge
    rw [hprev]
    rw [Sym2.eq_swap]
    apply p.mk_mem_edges_iff_exists.mpr
    refine ⟨i - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]
  · apply hnotedge
    rw [hnext]
    apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨i, hiend, rfl⟩

/-- An induced component containing an internal E-degree-two corridor vertex
is not SET after the full puncture. -/
theorem eDegree_two_internal_walkPuncture_component_not_set
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (htwo : eDegree G (p.getVert i) = 2)
    (C : (walkPuncture G p).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hiC : p.getVert i ∈ C.supp) :
    ¬ IsSET ((walkPuncture G p).induce C.supp) := by
  obtain ⟨heven, hzero⟩ :=
    eDegree_two_internal_walkPuncture (G := G) p hp hnil hsupport i hi hiend htwo
  exact component_not_set_of_even_eDegree_zero (G := walkPuncture G p) C
    (p.getVert i) hiC heven hzero

/-- In the degree-one corridor regime, a SET component of the puncture avoids
every positive-index corridor vertex: the proper positions have E-degree two
and the terminal has E-degree one in the original graph. -/
theorem eDegree_one_corridor_set_component_avoids_positive
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2)
    (C : (walkPuncture G p).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hset : IsSET ((walkPuncture G p).induce C.supp)) :
    ∀ i : ℕ, 0 < i → i ≤ p.length → p.getVert i ∉ C.supp := by
  intro i hi hile hiC
  by_cases hilast : i = p.length
  · subst i
    have haC : a ∈ C.supp := by simpa using hiC
    obtain ⟨haodd, hazero⟩ :=
      eDegree_one_terminal_walkPuncture (G := G) p hp hnil hsupport hone
    exact (component_not_set_of_odd_eDegree_zero (G := walkPuncture G p) C
      a haC haodd hazero) hset
  · have hilt : i < p.length := Nat.lt_of_le_of_ne hile hilast
    exact (eDegree_two_internal_walkPuncture_component_not_set
      (G := G) p hp hnil hsupport i hi hilt (hinternal i hi hilt) C hiC) hset

/-- Combining the positive-index SET exclusion with the puncture-boundary
localization forces any original edge leaving such a SET component to be the
first corridor edge. -/
theorem eDegree_one_corridor_set_component_crossing_is_start_edge
    {u a s t : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2)
    (C : (walkPuncture G p).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hset : IsSET ((walkPuncture G p).induce C.supp))
    (hs : s ∈ C.supp) (ht : t ∉ C.supp) (hst : G.Adj s t) :
    s = u ∧ t = p.snd := by
  apply walkPuncture_component_crossing_is_start_edge G p C
  · exact eDegree_one_corridor_set_component_avoids_positive
      (G := G) p hp hnil hsupport hone hinternal C hset
  · exact hs
  · exact ht
  · exact hst

/-- A SET component cannot contain the bare hub-side start of a degree-one
corridor puncture.  The SET condition supplies a second, even vertex of the
component; the first-edge-only boundary localization then disconnects the
original graph after deleting the bare exceptional vertex. -/
theorem eDegree_one_corridor_set_component_start_false
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2)
    (C : (walkPuncture G p).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (huC : u ∈ C.supp)
    (hset : IsSET ((walkPuncture G p).induce C.supp)) : False := by
  let J : SimpleGraph V := walkPuncture G p
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hvw
    exact C.mem_supp_of_adj_mem_supp hv hvw
  have hueven : Even (G.degree u) := hsupport u p.start_mem_support
  have huodd : Odd (J.degree u) := by
    have hdegree := degree_walkPuncture_start_add_one G p hp hnil
    rw [Nat.even_iff] at hueven
    rw [Nat.odd_iff]
    dsimp [J]
    omega
  have huoddC : Odd ((J.induce C.supp).degree ⟨u, huC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed u huC)]
    exact huodd
  let E : Finset {v : V // v ∈ C.supp} :=
    Finset.univ.filter fun v => Even ((J.induce C.supp).degree v)
  have hEcard : E.card = 3 := by
    simpa [E] using hset.card_even
  have hEpos : 0 < E.card := by omega
  obtain ⟨t, htE⟩ := Finset.card_pos.mp hEpos
  have htEven : Even ((J.induce C.supp).degree t) :=
    (Finset.mem_filter.mp htE).2
  have htu : t.val ≠ u := by
    intro htu
    have htu' : t = ⟨u, huC⟩ := Subtype.ext htu
    rw [htu'] at htEven
    exact (Nat.not_even_iff_odd.mpr huoddC) htEven
  have hno := eDegree_one_corridor_set_component_avoids_positive
    (G := G) p hp hnil hsupport hone hinternal C hset
  have hdisc := walkPuncture_start_component_forces_not_connected G p C
    hno hp hnil t.property htu
  exact hdisc (bare_exception_noncut G h u H)

/-- Every actual component of the degree-one corridor puncture avoids the
SET alternative.  Connectedness first makes the component meet the deleted
corridor; a positive-index contact has already been excluded, while a start
contact is eliminated by the bare non-cut argument. -/
theorem eDegree_one_corridor_all_components_not_set
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2) :
    ∀ (C : (walkPuncture G p).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((walkPuncture G p).induce C.supp) := by
  intro C _ hset
  have hconn : G.Connected := H.counterexample.1.1
  obtain ⟨z, hzC, hzsupport⟩ :=
    walkPuncture_component_meets_deleted_support G p C hconn
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hzsupport
  obtain ⟨i, hzi, hile⟩ := hzsupport
  by_cases hi0 : i = 0
  · subst i
    have hzu : z = u := by simpa using hzi.symm
    have huC : u ∈ C.supp := by simpa [hzu] using hzC
    exact eDegree_one_corridor_set_component_start_false
      h u a H p hp hnil hsupport hone hinternal C huC hset
  · exact (eDegree_one_corridor_set_component_avoids_positive
      (G := G) p hp hnil hsupport hone hinternal C hset i
      (Nat.pos_of_ne_zero hi0) hile) (by simpa [hzi] using hzC)

/-- The bare prescribed vertex does not occur on a degree-one corridor from
the other exception.  The start is the other exception, the terminal has
E-degree one, and every proper internal vertex has E-degree two. -/
theorem bare_prescribed_not_mem_eDegree_one_corridor_support
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a)
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2) :
    h ∉ p.support := by
  rcases H.counterexample.1 with ⟨_, hhu, _, _, _, hbare, _⟩
  intro hh
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hh
  obtain ⟨i, hvi, hile⟩ := hh
  by_cases hi0 : i = 0
  · subst i
    apply hhu
    simpa using hvi.symm
  by_cases hilast : i = p.length
  · subst i
    rw [show h = a by simpa using hvi.symm] at hbare
    omega
  · have hi : 0 < i := Nat.pos_of_ne_zero hi0
    have hiend : i < p.length := Nat.lt_of_le_of_ne hile hilast
    have hdegree := hinternal i hi hiend
    rw [hvi, hbare] at hdegree
    omega

/-- The full degree-one corridor puncture retains the subcubic E-degree cap.
Vertices on the punctured corridor are either newly odd at an endpoint or
E-isolated in its interior; off the corridor, every surviving even neighbour
was already even in the original graph. -/
theorem bare_eDegree_one_corridor_walkPuncture_cap
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2) :
    ∀ v, Even ((walkPuncture G p).degree v) →
      eDegree (walkPuncture G p) v ≤ 3 := by
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hbare, hcap⟩
  intro v hvEven
  by_cases hvSupport : v ∈ p.support
  · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvSupport
    obtain ⟨i, hvi, hile⟩ := hvSupport
    by_cases hi0 : i = 0
    · subst i
      have hvu : v = u := by simpa using hvi.symm
      have huEven : Even (G.degree u) := hsupport u p.start_mem_support
      have huOdd : Odd ((walkPuncture G p).degree u) := by
        have hdegree := degree_walkPuncture_start_add_one G p hp hnil
        rw [Nat.even_iff] at huEven
        rw [Nat.odd_iff]
        omega
      rw [hvu] at hvEven
      exact False.elim ((Nat.not_even_iff_odd.mpr huOdd) hvEven)
    by_cases hilast : i = p.length
    · subst i
      have hva : v = a := by simpa using hvi.symm
      have haEven : Even (G.degree a) := hsupport a p.end_mem_support
      have haOdd : Odd ((walkPuncture G p).degree a) := by
        have hdegree := degree_walkPuncture_end_add_one G p hp hnil
        rw [Nat.even_iff] at haEven
        rw [Nat.odd_iff]
        omega
      rw [hva] at hvEven
      exact False.elim ((Nat.not_even_iff_odd.mpr haOdd) hvEven)
    · have hi : 0 < i := Nat.pos_of_ne_zero hi0
      have hiend : i < p.length := Nat.lt_of_le_of_ne hile hilast
      obtain ⟨_, hzero⟩ := eDegree_two_internal_walkPuncture
        (G := G) p hp hnil hsupport i hi hiend (hinternal i hi hiend)
      rw [hvi] at hzero
      omega
  · have hvEvenG : Even (G.degree v) := by
      rw [degree_walkPuncture_of_not_mem_support G p hvSupport] at hvEven
      exact hvEven
    have hsub := evenNeighbors_walkPuncture_subset_of_even_support
      G p hsupport (w := v)
    by_cases hvh : v = h
    · subst v
      have hle : eDegree (walkPuncture G p) h ≤ eDegree G h :=
        Finset.card_le_card hsub
      rw [hbare] at hle
      omega
    by_cases hvu : v = u
    · subst v
      exact False.elim (hvSupport p.start_mem_support)
    · have hle : eDegree (walkPuncture G p) v ≤ eDegree G v :=
        Finset.card_le_card hsub
      exact hle.trans (hcap v hvEvenG hvh hvu)

/-- A full corridor puncture has the floor budget once its retained E-degree
cap and its componentwise SET exclusions have both been established. -/
theorem walkPuncture_floor_of_component_nonSET
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hcap : ∀ v, Even ((walkPuncture G p).degree v) →
      eDegree (walkPuncture G p) v ≤ 3)
    (hnot : ∀ (C : (walkPuncture G p).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((walkPuncture G p).induce C.supp)) :
    HasPathBudget (walkPuncture G p) (Fintype.card V / 2) := by
  apply floor_of_components
  intro C
  classical
  apply (floor_or_set ((walkPuncture G p).induce C.supp)
    C.connected_toSimpleGraph ?_).resolve_right
  · exact hnot C
  · have hclosed : ∀ v ∈ C.supp,
        (walkPuncture G p).neighborSet v ⊆ C.supp := by
      intro v hv w hw
      exact C.mem_supp_of_adj_mem_supp hv hw
    exact even_degree_cap_induce_of_closed
      (walkPuncture G p) C.supp hclosed 3 hcap

/-- The degree-one corridor puncture satisfies the published floor budget.
This combines the literal cap transport with the completed componentwise SET
audit, without yet asserting the later endpoint-positive restoration. -/
theorem bare_eDegree_one_corridor_walkPuncture_floor
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2) :
    HasPathBudget (walkPuncture G p) (Fintype.card V / 2) := by
  apply walkPuncture_floor_of_component_nonSET
  · exact bare_eDegree_one_corridor_walkPuncture_cap
      h u a H p hp hnil hsupport hinternal
  · exact eDegree_one_corridor_all_components_not_set
      h u a H p hp hnil hsupport hone hinternal

/-- The degree-one corridor puncture has a ceiling-budget decomposition that
keeps the bare prescribed vertex exposed twice.  Its own component uses the
one-exception endpoint theorem; the remaining actual components use the
already established floor-or-SET assembly. -/
theorem bare_eDegree_one_corridor_walkPuncture_endpoint_budget
    (h u a : V) (H : BareMinimalCounterexample G h u)
    (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      eDegree G (p.getVert i) = 2) :
    ∃ D : Decomposition (walkPuncture G p),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  rcases H.counterexample.1 with ⟨_, _, hpositive, heven, _, _, _⟩
  let J : SimpleGraph V := walkPuncture G p
  let C : J.ConnectedComponent := J.connectedComponentMk h
  have hhoff := bare_prescribed_not_mem_eDegree_one_corridor_support
    h u a H p hone hinternal
  have hdegree : J.degree h = G.degree h := by
    dsimp [J]
    exact degree_walkPuncture_of_not_mem_support G p hhoff
  have hcap : ∀ v, Even (J.degree v) → eDegree J v ≤ 3 := by
    dsimp [J]
    exact bare_eDegree_one_corridor_walkPuncture_cap
      h u a H p hp hnil hsupport hinternal
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hvw
    exact C.mem_supp_of_adj_mem_supp hv hvw
  have hhpos : 0 < (J.induce C.supp).degree ⟨h, rfl⟩ := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed h rfl), hdegree]
    exact hpositive
  have hheven : Even ((J.induce C.supp).degree ⟨h, rfl⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed h rfl), hdegree]
    exact heven
  obtain ⟨D, hDsize, hDends⟩ := one_exception_endpoint
    (J.induce C.supp) ⟨h, rfl⟩ C.connected_toSimpleGraph hhpos hheven (by
      intro v hv _
      exact even_degree_cap_induce_of_closed J C.supp hclosed 3 hcap v hv)
  apply assemble_one_ceiling J h D hDsize hDends
  intro C' hne
  classical
  apply (floor_or_set (J.induce C'.supp) C'.connected_toSimpleGraph ?_).resolve_right
  · dsimp [J, C] at hne ⊢
    exact eDegree_one_corridor_all_components_not_set
      h u a H p hp hnil hsupport hone hinternal C'
  · have hclosed' : ∀ v ∈ C'.supp, J.neighborSet v ⊆ C'.supp := by
      intro v hv w hvw
      exact C'.mem_supp_of_adj_mem_supp hv hvw
    exact even_degree_cap_induce_of_closed J C'.supp hclosed' 3 hcap

/-- The degree-one terminal obstruction is component-local for the full
corridor puncture.  Inducing the terminal's connected component preserves
its odd degree and zero E-degree, so that component is not SET. -/
theorem eDegree_one_terminal_walkPuncture_component_not_set
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    (C : (walkPuncture G p).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (haC : a ∈ C.supp) :
    ¬ IsSET ((walkPuncture G p).induce C.supp) := by
  let J : SimpleGraph V := walkPuncture G p
  have hclosed : ∀ v ∈ C.supp, J.neighborSet v ⊆ C.supp := by
    intro v hv w hvw
    exact C.mem_supp_of_adj_mem_supp hv hvw
  obtain ⟨hodd, hzero⟩ :=
    eDegree_one_terminal_walkPuncture (G := G) p hp hnil hsupport hone
  have hoddC : Odd ((J.induce C.supp).degree ⟨a, haC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed a haC)]
    exact hodd
  have hzeroC : eDegree (J.induce C.supp) ⟨a, haC⟩ = 0 := by
    rw [eDegree_induce_of_closed J C.supp hclosed]
    exact hzero
  intro hset
  exact hset.not_odd_of_eDegree_zero ⟨a, haC⟩ hoddC hzeroC

/-- Once the hub component has no E-degree-three vertex, every proper
internal vertex of a simple even-subgraph corridor from the bare exceptional
hub has E-degree exactly two.  This is the geometric input for the later
degree-one terminal puncture: it is independent of which degree occurs at
the terminal itself. -/
theorem bare_even_corridor_internal_eDegree_eq_two
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    eDegree G (p.getVert i : V) = 2 := by
  have hge := shortest_even_corridor_internal_eDegree_ge_two x a p hp i hi hiend
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hbare, hcap⟩
  have hzx : (p.getVert i : V) ≠ x := by
    intro hz
    have hpath_eq : p.getVert i = p.getVert 0 := by
      apply Subtype.ext
      simpa using hz
    have hindex_eq : i = 0 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) hpath_eq
    omega
  have hzh : (p.getVert i : V) ≠ h := by
    intro hz
    subst h
    rw [hbare] at hge
    omega
  have hle : eDegree G (p.getVert i : V) ≤ 3 :=
    hcap _ (p.getVert i).property hzh hzx
  by_contra htwo
  have hthree : eDegree G (p.getVert i : V) = 3 := by omega
  exact bare_hub_component_no_degree_three h x H
    ⟨p.getVert i, (p.take i).reachable, hthree⟩

/-- On a shortest all-even corridor ending at an E-degree-one vertex, a proper
internal vertex remains E-isolated after every earlier corridor edge has been
restored.  This is the literal graph-indexed zero-degree ledger consumed by
the ordered restoration theorem; the geodesic no-chord condition prevents an
earlier restored edge from becoming a new even neighbour. -/
theorem bare_eDegree_one_shortest_corridor_internal_zero_after_prefix
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hnil : ¬ (shortestEvenCorridorLift p).Nil)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    [inst : DecidableRel
      (Decomposition.restorationChainGraph (walkPuncture G (shortestEvenCorridorLift p))
        (fun j => (shortestEvenCorridorLift p).getVert j) (i - 1)).Adj] :
    eDegree
      (Decomposition.restorationChainGraph (walkPuncture G (shortestEvenCorridorLift p))
        (fun j => (shortestEvenCorridorLift p).getVert j) (i - 1))
      ((shortestEvenCorridorLift p).getVert i) = 0 := by
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  letI : DecidableRel (walkPuncture G W).Adj := Classical.decRel _
  letI : DecidableRel
      (Decomposition.restorationChainGraph (walkPuncture G W)
        (fun j => W.getVert j) (i - 1)).Adj := inst
  have hinternal : eDegree G (W.getVert i) = 2 := by
    simpa only [W, shortestEvenCorridorLift_getVert] using
      bare_even_corridor_internal_eDegree_eq_two h x a H p hp i hi hiend
  have hzeroBase : eDegree (walkPuncture G W) (W.getVert i) = 0 := by
    obtain ⟨_, hzero⟩ := eDegree_two_internal_walkPuncture
      (G := G) W hpath hnil
      (fun z hz => by
        rw [show W = shortestEvenCorridorLift p from rfl] at hz
        exact shortestEvenCorridorLift_support_even p z hz)
      i hi (by rw [hWlen]; exact hiend) hinternal
    exact hzero
  have hbase : ∀ j, j ≤ i - 1 →
      ¬ (walkPuncture G W).Adj (W.getVert i) (W.getVert j) := by
    intro j hj
    by_cases hprev : j + 1 = i
    · subst i
      intro hadj
      have hnot := (walkPuncture_adj_iff G W).mp hadj |>.2
      apply hnot
      rw [Sym2.eq_swap]
      exact W.mk_mem_edges_iff_exists.mpr ⟨j, by rw [hWlen]; omega, rfl⟩
    · intro hadj
      have horig : G.Adj (W.getVert i) (W.getVert j) :=
        (walkPuncture_adj_iff G W).mp hadj |>.1
      apply shortest_even_corridor_not_adj_getVert x a p hdist j i (by omega) (by omega)
      change G.Adj (p.getVert j : V) (p.getVert i : V)
      simpa only [W, shortestEvenCorridorLift_getVert] using horig.symm
  have hne : ∀ j, j ≤ i - 1 → W.getVert i ≠ W.getVert j := by
    intro j hj he
    have hindex : i = j := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; exact Nat.le_of_lt hiend)
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega) he
    omega
  have hzeroPrefix := Decomposition.restorationChainGraph_eDegree_zero_of_base
    (G := walkPuncture G W) (v := fun j => W.getVert j)
    (n := i - 1) (w := W.getVert i) hzeroBase hbase hne
  change @eDegree V _
    (Decomposition.restorationChainGraph (walkPuncture G W)
      (fun j => W.getVert j) (i - 1))
    inst (W.getVert i) = 0
  have hdec : Decomposition.restorationChainGraphDecidableRel
      (fun j => W.getVert j) (i - 1) = inst := Subsingleton.elim _ _
  rw [hdec] at hzeroPrefix
  exact hzeroPrefix

/-- The E-degree-one terminal remains E-isolated until its final corridor
edge is restored.  The only possible original even neighbour is the immediate
predecessor, whose edge was deleted by the puncture and is absent from every
earlier restoration prefix. -/
theorem eDegree_one_terminal_walkPuncture_zero_after_prefix
    {u a : V} (p : G.Walk u a) [DecidableRel (walkPuncture G p).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hsupport : ∀ z, z ∈ p.support → Even (G.degree z))
    (hone : eDegree G a = 1)
    [inst : DecidableRel
      (Decomposition.restorationChainGraph (walkPuncture G p)
        (fun j => p.getVert j) (p.length - 1)).Adj] :
    eDegree
      (Decomposition.restorationChainGraph (walkPuncture G p)
        (fun j => p.getVert j) (p.length - 1)) a = 0 := by
  have hlen : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnil
  let b := p.getVert (p.length - 1)
  have hab : G.Adj a b := by
    dsimp [b]
    simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlen)] using
      (p.adj_getVert_succ (i := p.length - 1) (by omega)).symm
  have hbEven : Even (G.degree b) := by
    dsimp [b]
    exact hsupport _ (p.getVert_mem_support _)
  have hzeroBase : eDegree (walkPuncture G p) a = 0 :=
    (eDegree_one_terminal_walkPuncture (G := G) p hp hnil hsupport hone).2
  letI : DecidableRel
      (Decomposition.restorationChainGraph (walkPuncture G p)
        (fun j => p.getVert j) (p.length - 1)).Adj := inst
  have hbase : ∀ j, j ≤ p.length - 1 →
      ¬ (walkPuncture G p).Adj a (p.getVert j) := by
    intro j hj
    by_cases hprev : j + 1 = p.length
    · intro hadj
      have hnot := (walkPuncture_adj_iff G p).mp hadj |>.2
      apply hnot
      have hj' : j = p.length - 1 := by omega
      subst j
      rw [Sym2.eq_swap]
      apply p.mk_mem_edges_iff_exists.mpr
      refine ⟨p.length - 1, by omega, ?_⟩
      simp [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlen)]
    · intro hadj
      have horig : G.Adj a (p.getVert j) :=
        (walkPuncture_adj_iff G p).mp hadj |>.1
      have hjEven : Even (G.degree (p.getVert j)) :=
        hsupport _ (p.getVert_mem_support _)
      have hjMem : p.getVert j ∈ evenNeighbors G a :=
        (mem_evenNeighbors (G := G) a (p.getVert j)).mpr ⟨horig, hjEven⟩
      have hbMem : b ∈ evenNeighbors G a :=
        (mem_evenNeighbors (G := G) a b).mpr ⟨hab, hbEven⟩
      change (evenNeighbors G a).card = 1 at hone
      obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hone
      have hbd : b = d := by simpa [hd] using hbMem
      have hjd : p.getVert j = d := by simpa [hd] using hjMem
      have hbj : b = p.getVert j := hbd.trans hjd.symm
      have hjindex : j = p.length - 1 := hp.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simpa only [b] using hbj.symm)
      exact hprev (by omega)
  have hne : ∀ j, j ≤ p.length - 1 → a ≠ p.getVert j := by
    intro j hj he
    have hjindex : j = p.length := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
      (by simpa only [p.getVert_length] using he.symm)
    omega
  have hzeroPrefix := Decomposition.restorationChainGraph_eDegree_zero_of_base
    (G := walkPuncture G p) (v := fun j => p.getVert j)
    (n := p.length - 1) (w := a) hzeroBase hbase hne
  change @eDegree V _
    (Decomposition.restorationChainGraph (walkPuncture G p)
      (fun j => p.getVert j) (p.length - 1)) inst a = 0
  have hdec : Decomposition.restorationChainGraphDecidableRel
      (fun j => p.getVert j) (p.length - 1) = inst := Subsingleton.elim _ _
  rw [hdec] at hzeroPrefix
  exact hzeroPrefix

/-- A nontrivial shortest all-even corridor to an E-degree-one terminal can
be restored at the ceiling budget while retaining the bare prescribed-endpoint
reserve.  The start is odd after puncturing and supplies the chain donor; the
prescribed vertex lies outside the corridor and is protected by the common
endpoint ledger. -/
theorem bare_eDegree_one_shortest_corridor_restore_all
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hone : eDegree G (a : V) = 1)
    (hnil : ¬ (shortestEvenCorridorLift p).Nil) :
    ∃ E : Decomposition G,
      E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount h ∧ 0 < E.endpointCount (a : V) := by
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  have hsupport : ∀ z, z ∈ W.support → Even (G.degree z) := by
    intro z hz
    rw [show W = shortestEvenCorridorLift p from rfl] at hz
    exact shortestEvenCorridorLift_support_even p z hz
  have hinternal : ∀ i : ℕ, 0 < i → i < W.length →
      eDegree G (W.getVert i) = 2 := by
    intro i hi hiend
    rw [hWlen] at hiend
    simpa only [W, shortestEvenCorridorLift_getVert] using
      bare_even_corridor_internal_eDegree_eq_two h x a H p hp i hi hiend
  letI : DecidableRel (walkPuncture G W).Adj := Classical.decRel _
  obtain ⟨D, hDsize, hDh⟩ :=
    bare_eDegree_one_corridor_walkPuncture_endpoint_budget
      h (x : V) (a : V) H W hpath hnil hsupport hone hinternal
  have hstartEven : Even (G.degree (x : V)) := x.property
  have hstartOdd : Odd ((walkPuncture G W).degree (x : V)) := by
    have hdegree := degree_walkPuncture_start_add_one G W hpath hnil
    rw [Nat.even_iff] at hstartEven
    rw [Nat.odd_iff]
    omega
  have hDstart : 0 < D.endpointCount (W.getVert 0) := by
    simpa only [W, shortestEvenCorridorLift_getVert, p.getVert_zero] using
      D.endpointCount_pos_of_odd_degree (x : V) hstartOdd
  letI : ∀ n, DecidableRel
      (Decomposition.restorationChainGraph (walkPuncture G W)
        (fun j => W.getVert j) n).Adj :=
    Decomposition.restorationChainGraphDecidableRel (fun j => W.getVert j)
  obtain ⟨E, hEsize, hEend, hEledger⟩ :=
    Decomposition.restore_chain_of_zero_centres_with_endpoint_ledger D
      (fun j => W.getVert j) W.length hDstart
      (by
        intro i hi hile he
        have hiend : i ≤ W.length := hile
        have hpred : i - 1 ≤ W.length := by omega
        have hindex : i = i - 1 := hpath.getVert_injOn
          (by simp only [Set.mem_ofPred_eq]; exact hiend)
          (by simp only [Set.mem_ofPred_eq]; exact hpred) he
        omega)
      (by
        intro i hi hile
        apply Decomposition.restorationChainGraph_not_adj_of_base
          (fun j => W.getVert j) (i - 1) (W.getVert i) (W.getVert (i - 1))
        · intro hadj
          have hnot := (walkPuncture_adj_iff G W).mp hadj |>.2
          apply hnot
          rw [Sym2.eq_swap]
          apply W.mk_mem_edges_iff_exists.mpr
          refine ⟨i - 1, by omega, ?_⟩
          simp [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]
        · intro j hj he
          have hindex : i = j := hpath.getVert_injOn
            (by simp only [Set.mem_ofPred_eq]; exact hile)
            (by simp only [Set.mem_ofPred_eq]; exact Nat.le_trans hj (by omega)) he
          omega)
      (by
        intro i hi hile
        by_cases hterminal : i = W.length
        · subst i
          simpa only [W.getVert_length] using
            eDegree_one_terminal_walkPuncture_zero_after_prefix
              (G := G) W hpath hnil hsupport hone
        · have hiend : i < W.length := Nat.lt_of_le_of_ne hile hterminal
          simpa only [W] using
            bare_eDegree_one_shortest_corridor_internal_zero_after_prefix
              h x a H p hp hdist hnil i hi (by simpa only [hWlen] using hiend))
  have hhoff : h ∉ W.support :=
    bare_prescribed_not_mem_eDegree_one_corridor_support
      h (x : V) (a : V) H W hone hinternal
  have hEh : E.endpointCount h = D.endpointCount h :=
    hEledger h (by
      intro i hi he
      apply hhoff
      exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr ⟨i, he.symm, hi⟩)
  have hgraph :
      Decomposition.restorationChainGraph (walkPuncture G W)
        (fun j => W.getVert j) W.length = G :=
    Decomposition.restorationChainGraph_walkPuncture_eq W
  have hresult : ∃ E : Decomposition
      (Decomposition.restorationChainGraph (walkPuncture G W)
        (fun j => W.getVert j) W.length),
      E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount h ∧ 0 < E.endpointCount (a : V) := by
    refine ⟨E, hEsize.le.trans hDsize, ?_, ?_⟩
    · rw [hEh]
      exact hDh
    · simpa only [W.getVert_length] using hEend
  let Q : SimpleGraph V → Prop := fun J =>
    ∃ E : Decomposition J,
      E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount h ∧ 0 < E.endpointCount (a : V)
  have hQ : Q (Decomposition.restorationChainGraph (walkPuncture G W)
      (fun j => W.getVert j) W.length) := by
    exact hresult
  exact (congrArg Q hgraph).mp hQ

/-- Consequently, a bare relative minimum counterexample cannot contain a
nontrivial shortest even corridor from its exception to an E-degree-one
terminal.  The remaining hub-degree-one reduction is solely the structural
selection of such a terminal and corridor. -/
theorem bare_counterexample_false_of_eDegree_one_shortest_corridor
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hone : eDegree G (a : V) = 1)
    (hnil : ¬ (shortestEvenCorridorLift p).Nil) : False := by
  obtain ⟨E, hsize, hh, _⟩ :=
    bare_eDegree_one_shortest_corridor_restore_all h x a H p hp hdist hone hnil
  exact H.counterexample.2 ⟨E, hsize, hh⟩

/-- No E-degree-one vertex can occur in the even-subgraph component of the
bare exceptional hub.  A shortest path to such a vertex is nontrivial because
the exceptional hub has E-degree greater than three, and the completed
corridor contradiction then applies directly. -/
theorem bare_hub_component_no_degree_one
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hexists : ∃ a : evenVertices G, (evenSubgraph G).Reachable x a ∧
      eDegree G (a : V) = 1) : False := by
  obtain ⟨a, hareach, hone⟩ := hexists
  obtain ⟨p, hp, hdist⟩ := hareach.exists_path_of_dist
  have hxgt : 3 < eDegree G (x : V) :=
    BareCounterexample.exception_gt_three H.counterexample
  have hax : (a : V) ≠ x := by
    intro he
    have hxeq : eDegree G (x : V) = 1 := by simpa [he] using hone
    omega
  have hlen : 0 < p.length := by
    by_contra hnot
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos hnot
    have heq : (a : V) = x := by
      calc
        (a : V) = (p.getVert p.length : V) := by simp
        _ = (p.getVert 0 : V) := by simp [hzero]
        _ = x := by simp
    exact hax heq
  have hnil : ¬ (shortestEvenCorridorLift p).Nil := by
    apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
    simpa only [shortestEvenCorridorLift_length] using hlen
  exact bare_counterexample_false_of_eDegree_one_shortest_corridor
    h x a H p hp hdist hone hnil

/-- Pointwise form of the hub-component degree-one exclusion, convenient for
normal-form consumers that already carry a selected terminal. -/
theorem bare_hub_no_degree_one
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hareach : (evenSubgraph G).Reachable x a)
    (hone : eDegree G (a : V) = 1) : False :=
  bare_hub_component_no_degree_one h x H ⟨a, hareach, hone⟩

end Gallai.TwoException
