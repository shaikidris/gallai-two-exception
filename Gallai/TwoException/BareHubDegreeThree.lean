/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareMinimality
public import Gallai.TwoException.StarSurplus
public import Gallai.TwoException.BareHangingSET
public import Gallai.TwoException.BareCuts
public import Gallai.Structure.LengthOneCorridorAuxiliary
public import Gallai.Structure.CorridorAuxiliary
public import Gallai.Structure.PendantReturn
public import Gallai.Structure.EdgeDeletion
public import Gallai.Inputs.CorridorAddibility
public import Gallai.TwoException.ShortestEvenCorridor

@[expose] public section

/-! # The final-leaf bound in the degree-three hub reduction

The first corridor deletion in the bare-case proof leaves one or two pending
spokes at a nonexceptional even vertex.  The endpoint-sensitive final step
needs the strict Fan bound of at most two passing neighbours at that leaf.
This module records the exact reduction of that bound to the bare-instance
E-degree cap; the corridor construction itself remains a separate task.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a bare minimal counterexample, a pending spoke at a nonexceptional
even leaf has at most two passing neighbours whenever the puncture preserves
all degree parities away from its centre.  The hypotheses deliberately name
the missing spoke and its original even endpoints: they are exactly what is
needed to remove the centre from the original even-neighbour set. -/
theorem bare_pending_leaf_passing_le_two
    (h x c w : V) (H : BareMinimalCounterexample G h x)
    (J : SimpleGraph V) [DecidableRel J.Adj] (D : Decomposition J)
    (hsub : J ≤ G)
    (hparity : ∀ v, v ≠ c → J.degree v % 2 = G.degree v % 2)
    (hmissing : ¬ J.Adj w c)
    (hwc : G.Adj w c) (hwEven : Even (G.degree w))
    (hcEven : Even (G.degree c))
    (hwh : w ≠ h) (hwx : w ≠ x) :
    passingNeighborCount D w ≤ 2 := by
  rcases H.1.1 with ⟨_, _, _, _, _, _, hcap⟩
  have hwcap : eDegree G w ≤ 3 := hcap w hwEven hwh hwx
  have hcw : c ∈ evenNeighbors G w :=
    (mem_evenNeighbors (G := G) w c).mpr ⟨hwc, hcEven⟩
  simpa only [passingNeighborCount] using
    passing_neighbor_count_le_two_of_star_parity D c w hsub hparity hmissing hcw hwcap

/-- The literal one-edge puncture also changes the pending leaf's parity.
This variant is the correct consumer for that singleton branch: loop-freeness
excludes the leaf itself from its passing-neighbour set, so parity is needed
only away from the centre and pending leaf. -/
theorem bare_pending_leaf_passing_le_two_except_leaf
    (h x c w : V) (H : BareMinimalCounterexample G h x)
    (J : SimpleGraph V) [DecidableRel J.Adj] (D : Decomposition J)
    (hsub : J ≤ G)
    (hparity : ∀ v, v ≠ c → v ≠ w → J.degree v % 2 = G.degree v % 2)
    (hmissing : ¬ J.Adj w c)
    (hwc : G.Adj w c) (hwEven : Even (G.degree w))
    (hcEven : Even (G.degree c))
    (hwh : w ≠ h) (hwx : w ≠ x) :
    passingNeighborCount D w ≤ 2 := by
  rcases H.1.1 with ⟨_, _, _, _, _, _, hcap⟩
  have hwcap : eDegree G w ≤ 3 := hcap w hwEven hwh hwx
  have hcw : c ∈ evenNeighbors G w :=
    (mem_evenNeighbors (G := G) w c).mpr ⟨hwc, hcEven⟩
  simpa only [passingNeighborCount] using
    passing_neighbor_count_le_two_of_star_parity_except_leaf D c w hsub hparity
      hmissing hcw hwcap

/-- Every retained neighbour of the punctured centre is odd in the literal
length-one auxiliary.  The three original even neighbours are precisely the
deleted spokes; the bare prescribed vertex cannot be a retained neighbour
because its original E-degree is zero.  This supplies the positivity premise
of the prescribed half-star theorem without placing any degree cap on `x`. -/
theorem bare_lengthOneCorridorAuxiliary_center_neighbor_odd
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (ha : Even (G.degree a)) (hha : h ≠ a)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    ∀ v, (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl a) v →
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree v) := by
  rcases H.counterexample.1 with ⟨_, _, _, hh, _, hbare, _⟩
  intro v hav
  cases v with
  | inr z =>
    cases z
    have heq : (.inl a : V ⊕ Unit) = .inl h :=
      (pendantExtension_adj_new (threeSpokePuncture G a x q r) h (.inl a)).mp hav.symm
    exact False.elim (hha (Sum.inl.inj heq).symm)
  | inl w =>
    have hP : (threeSpokePuncture G a x q r).Adj a w :=
      (pendantExtension_adj_old (threeSpokePuncture G a x q r) h a w).mp hav
    have hG : G.Adj a w := threeSpokePuncture_le G a x q r hP
    have hwa : w ≠ a := hP.ne.symm
    have hwx : w ≠ x := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_ax G a x q r hP
    have hwq : w ≠ q := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_aq G a x q r hP
    have hwr : w ≠ r := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_ar G a x q r hP
    have hwh : w ≠ h := by
      intro e
      subst w
      have hmem : a ∈ evenNeighbors G h :=
        (mem_evenNeighbors (G := G) h a).mpr ⟨hG.symm, ha⟩
      change (evenNeighbors G h).card = 0 at hbare
      have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
      omega
    have hoddG : Odd (G.degree w) := by
      apply Nat.not_even_iff_odd.mp
      intro heven
      rcases hcover w hG heven with hw | hw | hw
      · exact hwx hw
      · exact hwq hw
      · exact hwr hw
    rw [pendantExtension_degree_old_ne (threeSpokePuncture G a x q r) h w hwh,
      threeSpokePuncture_degree_away G a x q r w hwa hwx hwq hwr]
    exact hoddG

/-- The retained-neighbour oddness argument for a literal terminal auxiliary
uses only the bare E-degree of the pendant attachment, not the identity of
the other exceptional vertex.  This form is therefore available after a
nontrivial corridor has been restored up to its final edge. -/
theorem lengthOneCorridorAuxiliary_center_neighbor_odd_of_bare
    (h a b q r : V) (hbare : eDegree G h = 0)
    (ha : Even (G.degree a)) (hha : h ≠ a)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = b ∨ w = q ∨ w = r) :
    ∀ v, (lengthOneCorridorAuxiliary G h a b q r).Adj (.inl a) v →
      Odd ((lengthOneCorridorAuxiliary G h a b q r).degree v) := by
  intro v hav
  cases v with
  | inr z =>
    cases z
    have heq : (.inl a : V ⊕ Unit) = .inl h :=
      (pendantExtension_adj_new (threeSpokePuncture G a b q r) h (.inl a)).mp hav.symm
    exact False.elim (hha (Sum.inl.inj heq).symm)
  | inl w =>
    have hP : (threeSpokePuncture G a b q r).Adj a w :=
      (pendantExtension_adj_old (threeSpokePuncture G a b q r) h a w).mp hav
    have hG : G.Adj a w := threeSpokePuncture_le G a b q r hP
    have hwa : w ≠ a := hP.ne.symm
    have hwb : w ≠ b := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_ax G a b q r hP
    have hwq : w ≠ q := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_aq G a b q r hP
    have hwr : w ≠ r := by
      intro e
      subst w
      exact threeSpokePuncture_not_adj_ar G a b q r hP
    have hwh : w ≠ h := by
      intro e
      subst w
      have hmem : a ∈ evenNeighbors G h :=
        (mem_evenNeighbors (G := G) h a).mpr ⟨hG.symm, ha⟩
      change (evenNeighbors G h).card = 0 at hbare
      have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
      omega
    have hoddG : Odd (G.degree w) := by
      apply Nat.not_even_iff_odd.mp
      intro heven
      rcases hcover w hG heven with hw | hw | hw
      · exact hwb hw
      · exact hwq hw
      · exact hwr hw
    rw [pendantExtension_degree_old_ne (threeSpokePuncture G a b q r) h w hwh,
      threeSpokePuncture_degree_away G a b q r w hwa hwb hwq hwr]
    exact hoddG

/-- A separated `q`-side SET component of the literal length-one pendant
auxiliary contradicts bare minimality once it contains a second old vertex.
The auxiliary SET is first transported to the original induced graph; the
checked `q-a` boundary then supplies the literal hanging-SET consumer. -/
theorem bare_lengthOneCorridorAuxiliary_separated_q_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ lengthOneCorridorAuxiliary_oldSet G h a x q r C)]
    (hq : (.inl q : V ⊕ Unit) ∈ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hh : (.inl h : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hqa : G.Adj q a)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) : False := by
  obtain ⟨t, ht, htq⟩ :=
    lengthOneCorridorAuxiliary_set_component_exists_second_old G h a x q r C hq hleaf hset
  have hsetG : IsSET (G.induce (lengthOneCorridorAuxiliary_oldSet G h a x q r C)) :=
    lengthOneCorridorAuxiliary_old_component_isSET G h a x q r C hleaf ha hset
  apply bare_hanging_set_literal_false h x H
    (lengthOneCorridorAuxiliary_oldSet G h a x q r C) q a t
  · exact hq
  · exact ha
  · exact ht
  · exact htq
  · exact hh
  · exact hx
  · exact hqa
  · intro u v hu hv huv
    exact lengthOneCorridorAuxiliary_component_crossing_is_qa G h a x q r u v C
      ha hx hr hu hv huv
  · exact hsetG

/-- The symmetric `r`-side auxiliary SET branch is eliminated by the same
literal hanging-SET consumer as the `q`-side branch. -/
theorem bare_lengthOneCorridorAuxiliary_separated_r_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ lengthOneCorridorAuxiliary_oldSet G h a x q r C)]
    (hr : (.inl r : V ⊕ Unit) ∈ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hra : G.Adj r a)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) : False := by
  have hh : (.inl h : V ⊕ Unit) ∉ C.supp :=
    lengthOneCorridorAuxiliary_attachment_not_mem_of_leaf_not_mem G h a x q r C hleaf
  obtain ⟨t, ht, htr⟩ :=
    lengthOneCorridorAuxiliary_set_component_exists_second_old_of_mem G h a x q r r C hr hleaf hset
  have hsetG : IsSET (G.induce (lengthOneCorridorAuxiliary_oldSet G h a x q r C)) :=
    lengthOneCorridorAuxiliary_old_component_isSET G h a x q r C hleaf ha hset
  apply bare_hanging_set_literal_false h x H
    (lengthOneCorridorAuxiliary_oldSet G h a x q r C) r a t
  · exact hr
  · exact ha
  · exact ht
  · exact htr
  · exact hh
  · exact hx
  · exact hra
  · intro u v hu hv huv
    exact lengthOneCorridorAuxiliary_component_crossing_is_ra G h a x q r u v C
      ha hx hq hu hv huv
  · exact hsetG

/-- The remaining `x`-side SET alternative is incompatible with bare
minimality: the structural corridor lemma makes the exceptional vertex `x` a
cut vertex, whereas the bare cut analysis proves that `x` is non-cut. -/
theorem bare_lengthOneCorridorAuxiliary_x_side_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hx : (.inl x : V ⊕ Unit) ∈ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) : False := by
  have hhx : h ≠ x := H.counterexample.1.2.1
  exact lengthOneCorridorAuxiliary_x_side_set_forces_not_connected
    G h a x q r C hhx hx ha hq hr hleaf hset
    (bare_exception_noncut G h x H)

/-- The complete SET audit for the literal length-one corridor auxiliary.
The pendant and centre components have intrinsic degree obstructions. Every
remaining SET component is exactly one-sided at `x`, `q`, or `r`; the three
checked side consumers then contradict bare minimality. This theorem stops at
the component audit: the floor assembly and the subsequent path restoration
remain separate consumers. -/
theorem bare_lengthOneCorridorAuxiliary_all_components_not_set
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    ∀ (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp) := by
  classical
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hh, hx, _, hcap⟩
  intro C _ hset
  by_cases hleaf : (.inr () : V ⊕ Unit) ∈ C.supp
  · exact lengthOneCorridorAuxiliary_pendant_component_not_set G h a x q r C hleaf hset
  by_cases haC : (.inl a : V ⊕ Unit) ∈ C.supp
  · exact lengthOneCorridorAuxiliary_center_component_not_set G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcover C haC hset
  rcases lengthOneCorridorAuxiliary_set_component_exactly_one_deleted_leaf
      G h a x q r C hconn hleaf haC hax haq har hxq hxr hqr ha hx hq hr
      hha hhx hhq hhr hh hcap hset with
      ⟨hxC, hqC, hrC⟩ | ⟨hqC, hxC, hrC⟩ | ⟨hrC, hxC, hqC⟩
  · exact bare_lengthOneCorridorAuxiliary_x_side_set_false h x a q r H C
      hxC haC hqC hrC hleaf hset
  · have hhC : (.inl h : V ⊕ Unit) ∉ C.supp :=
      lengthOneCorridorAuxiliary_attachment_not_mem_of_leaf_not_mem G h a x q r C hleaf
    exact bare_lengthOneCorridorAuxiliary_separated_q_set_false h x a q r H C
      hqC haC hxC hrC hhC hleaf haq.symm hset
  · exact bare_lengthOneCorridorAuxiliary_separated_r_set_false h x a q r H C
      hrC haC hxC hqC hleaf har.symm hset

/-- The literal length-one corridor auxiliary has the published floor budget
once the bare data are unpacked.  This composes only the auxiliary cap and
its all-component SET audit; restoring the punctured spokes and trimming the
pendant edge are separate operations. -/
theorem bare_lengthOneCorridorAuxiliary_floor
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    HasPathBudget (lengthOneCorridorAuxiliary G h a x q r)
      (Fintype.card (V ⊕ Unit) / 2) := by
  classical
  rcases H.counterexample.1 with ⟨hconn, hhx, _, hh, hx, hbare, hcap⟩
  apply lengthOneCorridorAuxiliary_floor_of_component_nonSET G h a x q r
  · exact lengthOneCorridorAuxiliary_cap_of_bare_data G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hbare hcap
  · exact bare_lengthOneCorridorAuxiliary_all_components_not_set h x a q r H
      hax haq har hxq hxr hqr ha hq hr hha hhq hhr hcover

/-- Extract the literal auxiliary's floor witness together with the endpoint
positivity needed at every auxiliary-odd return recipient.  This is the
endpoint interface consumed by the successive prefix and half-star moves;
it deliberately does not yet perform those moves. -/
theorem bare_lengthOneCorridorAuxiliary_floor_with_odd_endpoints
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    ∃ D : Decomposition (lengthOneCorridorAuxiliary G h a x q r),
      D.size ≤ Fintype.card (V ⊕ Unit) / 2 ∧
      ∀ v, Odd ((lengthOneCorridorAuxiliary G h a x q r).degree v) →
        0 < D.endpointCount v := by
  obtain ⟨D, hD⟩ := bare_lengthOneCorridorAuxiliary_floor h x a q r H
    hax haq har hxq hxr hqr ha hq hr hha hhq hhr hcover
  refine ⟨D, hD, ?_⟩
  intro v hv
  exact D.endpointCount_pos_of_odd_degree v hv

/-- The full-star branch of the literal degree-three corridor restoration is
already a complete reduction: its restored auxiliary is the pendant extension
of the original graph, and the pendant-return operation gives an old-graph
decomposition without increasing the path count. -/
theorem bare_lengthOneCorridorAuxiliary_full_star_return
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (D : Decomposition
      (lengthOneCorridorAuxiliary G h a x q r ⊔
        (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)))) :
    ∃ E : Decomposition G, E.size ≤ D.size := by
  let K := lengthOneCorridorAuxiliary G h a x q r ⊔
    (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit))
  have hK : K = pendantExtension G h :=
    lengthOneCorridorAuxiliary_restore_all_eq_pendantExtension G h a x q r
      hax haq har hxq hxr hqr
  let D' : Decomposition (pendantExtension G h) := hK ▸ D
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have hcast : D'.size = D.size := by
    exact castSize hK D
  obtain ⟨E, hsize, _⟩ := D'.return_pendant G h
  exact ⟨E, hsize.trans_eq hcast⟩

/-- The full-star return preserves the bare endpoint reserve except for the
literal pendant-carrier obstruction.  This is the endpoint-sensitive form of
the full-star branch: any remaining failure records the exact one-endpoint
carrier in the restored auxiliary, rather than being hidden by a path-count
only return. -/
theorem bare_lengthOneCorridorAuxiliary_full_star_return_dichotomy
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (hh : Even (G.degree h))
    (D : Decomposition
      (lengthOneCorridorAuxiliary G h a x q r ⊔
        (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)))) :
    ∃ E : Decomposition G, E.size ≤ D.size ∧
      (2 ≤ E.endpointCount h ∨
        E.endpointCount h = 0 ∧ D.endpointCount (.inl h) = 1) := by
  let K := lengthOneCorridorAuxiliary G h a x q r ⊔
    (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit))
  have hK : K = pendantExtension G h :=
    lengthOneCorridorAuxiliary_restore_all_eq_pendantExtension G h a x q r
      hax haq har hxq hxr hqr
  let D' : Decomposition (pendantExtension G h) := hK ▸ D
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) (v : V ⊕ Unit) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hcast : D'.size = D.size := castSize hK D
  obtain ⟨E, hsize, hgood | ⟨hzero, hone, _, _⟩⟩ :=
    D'.return_pendant_even_endpoint_dichotomy G h hh
  · exact ⟨E, hsize.trans_eq hcast, Or.inl hgood⟩
  · refine ⟨E, hsize.trans_eq hcast, Or.inr ⟨hzero, ?_⟩⟩
    · change D'.endpointCount (.inl h) = 1 at hone
      rw [show D'.endpointCount (.inl h) = D.endpointCount (.inl h) by
        exact castEnds hK D (.inl h)] at hone
      exact hone

/-- The full-star branch is endpoint-complete at the bare hub.  The generic
pendant return either retains the reserve or spends its singleton-carrier
saving to split at the positive even hub. -/
theorem bare_lengthOneCorridorAuxiliary_full_star_return_exposes
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (hpositive : 0 < G.degree h) (heven : Even (G.degree h))
    (D : Decomposition
      (lengthOneCorridorAuxiliary G h a x q r ⊔
        (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)))) :
    ∃ E : Decomposition G, E.size ≤ D.size ∧ 2 ≤ E.endpointCount h := by
  let K := lengthOneCorridorAuxiliary G h a x q r ⊔
    (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit))
  have hK : K = pendantExtension G h :=
    lengthOneCorridorAuxiliary_restore_all_eq_pendantExtension G h a x q r
      hax haq har hxq hxr hqr
  let D' : Decomposition (pendantExtension G h) := hK ▸ D
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have hcast : D'.size = D.size := castSize hK D
  obtain ⟨E, hEsize, hEends, _⟩ :=
    D'.return_pendant_even_exposes G h hpositive heven
  exact ⟨E, hEsize.trans_eq hcast, hEends⟩

/-- In either singleton-pending branch, return the pendant first and then
restore the one missing old spoke. -/
theorem bare_return_and_restore_pending_spoke
    (h x a r : V) (H : BareMinimalCounterexample G h x)
    (har : G.Adj a r)
    (ha : Even (G.degree a)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hrh : r ≠ h) (hrx : r ≠ x)
    (E : Decomposition (pendantExtension (G.deleteEdges {s(a, r)}) h))
    (hEa : 3 ≤ E.endpointCount (.inl a)) :
    ∃ F : Decomposition G, F.size ≤ E.size := by
  let J : SimpleGraph V := G.deleteEdges {s(a, r)}
  have hsub : J ≤ G := by
    intro u v huv
    exact (SimpleGraph.deleteEdges_adj.mp huv).1
  have hparity : ∀ v, v ≠ a → v ≠ r → J.degree v % 2 = G.degree v % 2 := by
    intro v hva hvr
    exact congrArg (fun n => n % 2) (degree_delete_edge_of_ne G a r v hva hvr)
  have hmissing : ¬ J.Adj r a := by
    intro hra
    exact (SimpleGraph.deleteEdges_adj.mp hra).2 (by simp [Sym2.eq_swap])
  obtain ⟨D, hDsize, _, _, hother⟩ := E.return_pendant J h
  have hDa : 3 ≤ D.endpointCount a := by
    rw [hother a hha.symm]
    exact hEa
  have hpass : passingNeighborCount D r ≤ 2 :=
    bare_pending_leaf_passing_le_two_except_leaf h x a r H J D hsub hparity hmissing
      har.symm hr ha hrh hrx
  have hstrict : #{v ∈ J.neighborFinset r | D.endpointCount v = 0} <
      D.endpointCount a := by
    change passingNeighborCount D r < D.endpointCount a
    omega
  obtain ⟨F, hFsize, _⟩ := D.single_edge_addibility r a har.ne.symm hmissing hstrict
  have hgraph : J ⊔ SimpleGraph.edge r a = G := by
    simpa [J, SimpleGraph.edge_comm] using delete_edge_sup_edge G a r har
  let F' : Decomposition G := hgraph ▸ F
  have castSizeOld {L M : SimpleGraph V} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have hFcast : F'.size = F.size := castSizeOld hgraph F
  exact ⟨F', hFcast.le.trans (hFsize.le.trans hDsize)⟩

/-- The singleton-pending branch also preserves the prescribed bare reserve.
The pendant-return theorem first creates two endpoints at `h` within its own
budget; the final Fan addition has centre and donor distinct from `h`, so its
endpoint equation leaves that reserve unchanged. -/
theorem bare_return_and_restore_pending_spoke_exposes
    (h x a r : V) (H : BareMinimalCounterexample G h x)
    (har : G.Adj a r)
    (ha : Even (G.degree a)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hrh : r ≠ h) (hrx : r ≠ x)
    (E : Decomposition (pendantExtension (G.deleteEdges {s(a, r)}) h))
    (hEa : 3 ≤ E.endpointCount (.inl a)) :
    ∃ F : Decomposition G, F.size ≤ E.size ∧ 2 ≤ F.endpointCount h := by
  let J : SimpleGraph V := G.deleteEdges {s(a, r)}
  have hsub : J ≤ G := by
    intro u v huv
    exact (SimpleGraph.deleteEdges_adj.mp huv).1
  have hparity : ∀ v, v ≠ a → v ≠ r → J.degree v % 2 = G.degree v % 2 := by
    intro v hva hvr
    exact congrArg (fun n => n % 2) (degree_delete_edge_of_ne G a r v hva hvr)
  have hmissing : ¬ J.Adj r a := by
    intro hra
    exact (SimpleGraph.deleteEdges_adj.mp hra).2 (by simp [Sym2.eq_swap])
  rcases H.counterexample.1 with ⟨_, _, hpositive, heven, _, _, _⟩
  have hdegreeh : J.degree h = G.degree h :=
    degree_delete_edge_of_ne G a r h hha hrh.symm
  have hpositiveJ : 0 < J.degree h := by
    rw [hdegreeh]
    exact hpositive
  have hevenJ : Even (J.degree h) := by
    rw [hdegreeh]
    exact heven
  obtain ⟨D, hDsize, hDh, hother⟩ :=
    E.return_pendant_even_exposes J h hpositiveJ hevenJ
  have hDa : 3 ≤ D.endpointCount a := by
    rw [hother a hha.symm]
    exact hEa
  have hpass : passingNeighborCount D r ≤ 2 :=
    bare_pending_leaf_passing_le_two_except_leaf h x a r H J D hsub hparity hmissing
      har.symm hr ha hrh hrx
  have hstrict : #{v ∈ J.neighborFinset r | D.endpointCount v = 0} <
      D.endpointCount a := by
    change passingNeighborCount D r < D.endpointCount a
    omega
  obtain ⟨F, hFsize, hFends⟩ := D.single_edge_addibility r a har.ne.symm hmissing hstrict
  have hFh : F.endpointCount h = D.endpointCount h := by
    simpa [hha.symm, hrh] using hFends h
  have hgraph : J ⊔ SimpleGraph.edge r a = G := by
    simpa [J, SimpleGraph.edge_comm] using delete_edge_sup_edge G a r har
  let F' : Decomposition G := hgraph ▸ F
  have castSizeOld {L M : SimpleGraph V} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEndsOld {L M : SimpleGraph V} (e : L = M)
      (P : Decomposition L) (v : V) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hFcast : F'.size = F.size := castSizeOld hgraph F
  refine ⟨F', hFcast.le.trans (hFsize.le.trans hDsize), ?_⟩
  rw [show F'.endpointCount h = F.endpointCount h by exact castEndsOld hgraph F h,
    hFh]
  exact hDh

/-- The pendant return followed by one pending-spoke restoration needs only a
uniform passing-neighbour bound on the graph after the pendant is removed.
The bare minimal-counterexample hypothesis is deliberately absent here: a
long corridor can supply the same bound at its terminal without identifying
its preterminal vertex as the original exceptional hub. -/
theorem return_and_restore_pending_spoke_exposes_of_pass_bound
    (h a r : V) (har : G.Adj a r)
    (hha : h ≠ a) (hrh : r ≠ h)
    (E : Decomposition (pendantExtension (G.deleteEdges {s(a, r)}) h))
    (hEa : 3 ≤ E.endpointCount (.inl a))
    (hpositiveJ : 0 < (G.deleteEdges {s(a, r)}).degree h)
    (hevenJ : Even ((G.deleteEdges {s(a, r)}).degree h))
    (hpass : ∀ D : Decomposition (G.deleteEdges {s(a, r)}),
      passingNeighborCount D r ≤ 2) :
    ∃ F : Decomposition G, F.size ≤ E.size ∧ 2 ≤ F.endpointCount h := by
  let J : SimpleGraph V := G.deleteEdges {s(a, r)}
  have hmissing : ¬ J.Adj r a := by
    intro hra
    exact (SimpleGraph.deleteEdges_adj.mp hra).2 (by simp [Sym2.eq_swap])
  obtain ⟨D, hDsize, hDh, hother⟩ :=
    E.return_pendant_even_exposes J h hpositiveJ hevenJ
  have hDa : 3 ≤ D.endpointCount a := by
    rw [hother a hha.symm]
    exact hEa
  have hstrict : #{v ∈ J.neighborFinset r | D.endpointCount v = 0} <
      D.endpointCount a := by
    change passingNeighborCount D r < D.endpointCount a
    exact (hpass D).trans_lt (by omega)
  obtain ⟨F, hFsize, hFends⟩ := D.single_edge_addibility r a har.ne.symm hmissing hstrict
  have hFh : F.endpointCount h = D.endpointCount h := by
    simpa [hha.symm, hrh] using hFends h
  have hgraph : J ⊔ SimpleGraph.edge r a = G := by
    simpa [J, SimpleGraph.edge_comm] using delete_edge_sup_edge G a r har
  let F' : Decomposition G := hgraph ▸ F
  have castSizeOld {L M : SimpleGraph V} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEndsOld {L M : SimpleGraph V} (e : L = M)
      (P : Decomposition L) (v : V) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hFcast : F'.size = F.size := castSizeOld hgraph F
  refine ⟨F', hFcast.le.trans (hFsize.le.trans hDsize), ?_⟩
  rw [show F'.endpointCount h = F.endpointCount h by exact castEndsOld hgraph F h,
    hFh]
  exact hDh

/-- Terminal selected-star return with the original exceptional vertex kept
separate from the terminal's preterminal leaf.  This is the long-corridor
version of the literal three-spoke consumer: the local star leaf `b` need not
be the exceptional vertex `x` governing the bare passing-neighbour bound. -/
theorem bare_selected_three_spoke_terminal_return
    (h x a b q r : V) (H : BareMinimalCounterexample G h x)
    (hab : G.Adj a b) (haq : G.Adj a q) (har : G.Adj a r)
    (hbq : b ≠ q) (hbr : b ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hqx : q ≠ x) (hrx : r ≠ x)
    (D : Decomposition (lengthOneCorridorAuxiliary G h a b q r))
    (B : Finset (V ⊕ Unit))
    (hsub : B ⊆ lengthOneCorridorLeaves b q r)
    (hbB : (.inl b : V ⊕ Unit) ∈ B) (hBcard : 2 ≤ #B)
    (E : Decomposition
      (lengthOneCorridorAuxiliary G h a b q r ⊔
        B.sup (SimpleGraph.edge (.inl a : V ⊕ Unit))))
    (hsize : E.size = D.size)
    (hcentre : E.endpointCount (.inl a) = D.endpointCount (.inl a) + #B)
    (hDa : 1 ≤ D.endpointCount (.inl a)) :
    ∃ F : Decomposition G, F.size ≤ D.size ∧ 2 ≤ F.endpointCount h := by
  classical
  rcases H.counterexample.1 with ⟨_, _, hpositive, heven, _, _, _⟩
  have hEa : 3 ≤ E.endpointCount (.inl a) :=
    Decomposition.prescribed_three_star_center_endpoints_ge_three D E (.inl a) B
      hDa hBcard hcentre
  rcases literal_three_star_selected_cases_lifted B b q r hbq hbr hqr hsub hbB hBcard with
      hfull | hpair | hpair
  · subst B
    obtain ⟨F, hF, hFends⟩ := bare_lengthOneCorridorAuxiliary_full_star_return_exposes
      h a b q r hab haq har hbq hbr hqr hpositive heven E
    exact ⟨F, hF.trans_eq hsize, hFends⟩
  · subst B
    have hgraph :
        lengthOneCorridorAuxiliary G h a b q r ⊔
            ({(.inl b : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)).sup
              (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
          pendantExtension (G.deleteEdges {s(a, r)}) h :=
      lengthOneCorridorAuxiliary_restore_ax_aq_eq_pendantDelete_ar G h a b q r
        hab haq hbq hbr hqr
    let E' : Decomposition (pendantExtension (G.deleteEdges {s(a, r)}) h) := hgraph ▸ E
    have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) : (e ▸ P).size = P.size := by
      subst M
      rfl
    have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) (v : V ⊕ Unit) :
        (e ▸ P).endpointCount v = P.endpointCount v := by
      subst M
      rfl
    have hEsize : E'.size = E.size := castSize hgraph E
    have hEcenter : 3 ≤ E'.endpointCount (.inl a) := by
      rw [castEnds hgraph E (.inl a)]
      exact hEa
    obtain ⟨F, hF, hFends⟩ := bare_return_and_restore_pending_spoke_exposes h x a r H har ha hr
      hha hhr.symm hrx E' hEcenter
    exact ⟨F, hF.trans (hEsize.le.trans_eq hsize), hFends⟩
  · subst B
    have hgraph :
        lengthOneCorridorAuxiliary G h a b q r ⊔
            ({(.inl b : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)).sup
              (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
          pendantExtension (G.deleteEdges {s(a, q)}) h :=
      lengthOneCorridorAuxiliary_restore_ax_ar_eq_pendantDelete_aq G h a b q r
        hab har hbq hbr hqr
    let E' : Decomposition (pendantExtension (G.deleteEdges {s(a, q)}) h) := hgraph ▸ E
    have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) : (e ▸ P).size = P.size := by
      subst M
      rfl
    have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) (v : V ⊕ Unit) :
        (e ▸ P).endpointCount v = P.endpointCount v := by
      subst M
      rfl
    have hEsize : E'.size = E.size := castSize hgraph E
    have hEcenter : 3 ≤ E'.endpointCount (.inl a) := by
      rw [castEnds hgraph E (.inl a)]
      exact hEa
    obtain ⟨F, hF, hFends⟩ := bare_return_and_restore_pending_spoke_exposes h x a q H haq ha hq
      hha hhq.symm hqx E' hEcenter
    exact ⟨F, hF.trans (hEsize.le.trans_eq hsize), hFends⟩

/-- The prescribed half-star interface closes a terminal three-spoke auxiliary
once its endpoint-positive floor witness is available.  The hypotheses are
stated on the exact auxiliary graph, so a restored corridor prefix can supply
them through its common endpoint ledger without reusing a length-one parity
argument. -/
theorem bare_terminal_three_spoke_addibility_return
    (h x a b q r : V) (H : BareMinimalCounterexample G h x)
    (hab : G.Adj a b) (haq : G.Adj a q) (har : G.Adj a r)
    (hbq : b ≠ q) (hbr : b ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hqx : q ≠ x) (hrx : r ≠ x)
    (D : Decomposition (lengthOneCorridorAuxiliary G h a b q r))
    (hDa : 1 ≤ D.endpointCount (.inl a))
    (hpositive : ∀ v,
      (lengthOneCorridorAuxiliary G h a b q r).Adj (.inl a) v ∨
        v ∈ lengthOneCorridorLeaves b q r → 0 < D.endpointCount v)
    (hmissing : ∀ z ∈ lengthOneCorridorLeaves b q r,
      ¬ (lengthOneCorridorAuxiliary G h a b q r).Adj (.inl a) z) :
    ∃ F : Decomposition G, F.size ≤ D.size ∧ 2 ≤ F.endpointCount h := by
  have haLeaf : (.inl a : V ⊕ Unit) ∉ lengthOneCorridorLeaves b q r := by
    simp [lengthOneCorridorLeaves, hab.ne, haq.ne, har.ne]
  have hcard : #(lengthOneCorridorLeaves b q r) = 3 := by
    simp [lengthOneCorridorLeaves, hbq, hbr, hqr]
  obtain ⟨B, hsub, hbB, hBcard, E, hEsize, hEcentre, _⟩ :=
    D.prescribed_three_star_addibility (.inl a) (lengthOneCorridorLeaves b q r)
      haLeaf hcard hmissing hpositive (.inl b) (by simp [lengthOneCorridorLeaves])
  exact bare_selected_three_spoke_terminal_return h x a b q r H hab haq har
    hbq hbr hqr ha hq hr hha hhq hhr hqx hrx D B hsub hbB hBcard E hEsize hEcentre hDa

/-- A shared endpoint ledger is sufficient to consume the terminal
three-spoke operation.  Retained neighbours of the centre are positive by
odd degree, while the three deleted leaves are supplied explicitly. -/
theorem bare_terminal_three_spoke_return_of_ledger
    (h x a b q r : V) (H : BareMinimalCounterexample G h x)
    (hab : G.Adj a b) (haq : G.Adj a q) (har : G.Adj a r)
    (hbq : b ≠ q) (hbr : b ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hqx : q ≠ x) (hrx : r ≠ x)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = b ∨ w = q ∨ w = r)
    (D : Decomposition (lengthOneCorridorAuxiliary G h a b q r))
    (hDb : 0 < D.endpointCount (.inl b))
    (hDa : 0 < D.endpointCount (.inl a))
    (hDq : 0 < D.endpointCount (.inl q))
    (hDr : 0 < D.endpointCount (.inl r)) :
    ∃ F : Decomposition G, F.size ≤ D.size ∧ 2 ≤ F.endpointCount h := by
  rcases H.counterexample.1 with ⟨_, _, _, _, _, hbare, _⟩
  have hmissing : ∀ z ∈ lengthOneCorridorLeaves b q r,
      ¬ (lengthOneCorridorAuxiliary G h a b q r).Adj (.inl a) z := by
    intro z hz haz
    have hz' : z = (.inl b : V ⊕ Unit) ∨ z = .inl q ∨ z = .inl r := by
      simpa [lengthOneCorridorLeaves] using hz
    rcases hz' with hzb | hzq | hzr
    · subst z
      exact threeSpokePuncture_not_adj_ax G a b q r
        ((pendantExtension_adj_old (threeSpokePuncture G a b q r) h a b).mp haz)
    · subst z
      exact threeSpokePuncture_not_adj_aq G a b q r
        ((pendantExtension_adj_old (threeSpokePuncture G a b q r) h a q).mp haz)
    · subst z
      exact threeSpokePuncture_not_adj_ar G a b q r
        ((pendantExtension_adj_old (threeSpokePuncture G a b q r) h a r).mp haz)
  have hpositive : ∀ v,
      (lengthOneCorridorAuxiliary G h a b q r).Adj (.inl a) v ∨
        v ∈ lengthOneCorridorLeaves b q r → 0 < D.endpointCount v := by
    intro v hv
    rcases hv with hav | hv
    · exact D.endpointCount_pos_of_odd_degree v
        (lengthOneCorridorAuxiliary_center_neighbor_odd_of_bare h a b q r
          hbare ha hha hcover v hav)
    · have hv' : v = (.inl b : V ⊕ Unit) ∨ v = .inl q ∨ v = .inl r := by
        simpa [lengthOneCorridorLeaves] using hv
      rcases hv' with hvb | hvq | hvr
      · subst v
        exact hDb
      · subst v
        exact hDq
      · subst v
        exact hDr
  exact bare_terminal_three_spoke_addibility_return h x a b q r H
    hab haq har hbq hbr hqr ha hq hr hha hhq hhr hqx hrx D
    (Nat.succ_le_iff.mpr hDa) hpositive hmissing

/-- A selected literal three-spoke restoration can be completed within its
input path budget.  The selected family is either the entire star, which
returns the pendant directly, or one of the two prescribed pairs, which
returns the pendant and restores the unique pending old spoke using the
strict centre surplus.  This is the finite case consumer between the
half-star interface and the bare final-edge lemma; it does not yet construct
the selected family from an auxiliary floor witness. -/
theorem bare_selected_three_spoke_return
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (D : Decomposition (lengthOneCorridorAuxiliary G h a x q r))
    (B : Finset (V ⊕ Unit))
    (hsub : B ⊆ lengthOneCorridorLeaves x q r)
    (hxB : (.inl x : V ⊕ Unit) ∈ B) (hBcard : 2 ≤ #B)
    (E : Decomposition
      (lengthOneCorridorAuxiliary G h a x q r ⊔
        B.sup (SimpleGraph.edge (.inl a : V ⊕ Unit))))
    (hsize : E.size = D.size)
    (hcentre : E.endpointCount (.inl a) = D.endpointCount (.inl a) + #B)
    (hDa : 1 ≤ D.endpointCount (.inl a)) :
    ∃ F : Decomposition G, F.size ≤ D.size ∧ 2 ≤ F.endpointCount h := by
  classical
  rcases H.counterexample.1 with ⟨_, _, hpositive, heven, _, _, _⟩
  have hEa : 3 ≤ E.endpointCount (.inl a) :=
    Decomposition.prescribed_three_star_center_endpoints_ge_three D E (.inl a) B
      hDa hBcard hcentre
  rcases literal_three_star_selected_cases_lifted B x q r hxq hxr hqr hsub hxB hBcard with
      hfull | hpair | hpair
  · subst B
    obtain ⟨F, hF, hFends⟩ := bare_lengthOneCorridorAuxiliary_full_star_return_exposes
      h a x q r hax haq har hxq hxr hqr hpositive heven E
    exact ⟨F, hF.trans_eq hsize, hFends⟩
  · subst B
    have hgraph :
        lengthOneCorridorAuxiliary G h a x q r ⊔
            ({(.inl x : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)).sup
              (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
          pendantExtension (G.deleteEdges {s(a, r)}) h :=
      lengthOneCorridorAuxiliary_restore_ax_aq_eq_pendantDelete_ar G h a x q r
        hax haq hxq hxr hqr
    let E' : Decomposition (pendantExtension (G.deleteEdges {s(a, r)}) h) := hgraph ▸ E
    have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) : (e ▸ P).size = P.size := by
      subst M
      rfl
    have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) (v : V ⊕ Unit) :
        (e ▸ P).endpointCount v = P.endpointCount v := by
      subst M
      rfl
    have hEsize : E'.size = E.size := castSize hgraph E
    have hEcenter : 3 ≤ E'.endpointCount (.inl a) := by
      rw [castEnds hgraph E (.inl a)]
      exact hEa
    obtain ⟨F, hF, hFends⟩ := bare_return_and_restore_pending_spoke_exposes h x a r H har ha hr
      hha hhr.symm (by exact hxr.symm) E' hEcenter
    exact ⟨F, hF.trans (hEsize.le.trans_eq hsize), hFends⟩
  · subst B
    have hgraph :
        lengthOneCorridorAuxiliary G h a x q r ⊔
            ({(.inl x : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)).sup
              (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
          pendantExtension (G.deleteEdges {s(a, q)}) h :=
      lengthOneCorridorAuxiliary_restore_ax_ar_eq_pendantDelete_aq G h a x q r
        hax har hxq hxr hqr
    let E' : Decomposition (pendantExtension (G.deleteEdges {s(a, q)}) h) := hgraph ▸ E
    have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) : (e ▸ P).size = P.size := by
      subst M
      rfl
    have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
        (P : Decomposition L) (v : V ⊕ Unit) :
        (e ▸ P).endpointCount v = P.endpointCount v := by
      subst M
      rfl
    have hEsize : E'.size = E.size := castSize hgraph E
    have hEcenter : 3 ≤ E'.endpointCount (.inl a) := by
      rw [castEnds hgraph E (.inl a)]
      exact hEa
    obtain ⟨F, hF, hFends⟩ := bare_return_and_restore_pending_spoke_exposes h x a q H haq ha hq
      hha hhq.symm (by exact hxq.symm) E' hEcenter
    exact ⟨F, hF.trans (hEsize.le.trans_eq hsize), hFends⟩

/-- The literal length-one corridor branch is reducible once the bare data
and its three exact even neighbours are supplied.  A floor witness provides
odd-degree endpoint positivity; the three absent spokes and the retained
centre-neighbour oddness discharge Fan's prescribed half-star interface, and
the selected-star consumer completes the original graph. -/
theorem bare_lengthOneCorridorAuxiliary_restore
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    ∃ F : Decomposition G, F.size ≤ Fintype.card (V ⊕ Unit) / 2 ∧
      2 ≤ F.endpointCount h := by
  obtain ⟨D, hDsize, hDodd⟩ :=
    bare_lengthOneCorridorAuxiliary_floor_with_odd_endpoints h x a q r H
      hax haq har hxq hxr hqr ha hq hr hha hhq hhr hcover
  rcases H.counterexample.1 with ⟨_, hhx, _, hh, hx, _, _⟩
  obtain ⟨oa, ox, oq, or, _, _⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r hax haq har hxq hxr hqr
      ha hx hq hr hha hhx hhq hhr hh
  have haLeaf : (.inl a : V ⊕ Unit) ∉ lengthOneCorridorLeaves x q r := by
    simp [lengthOneCorridorLeaves, hax.ne, haq.ne, har.ne]
  have hcard : #(lengthOneCorridorLeaves x q r) = 3 := by
    simp [lengthOneCorridorLeaves, hxq, hxr, hqr]
  have hmissing : ∀ b ∈ lengthOneCorridorLeaves x q r,
      ¬ (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl a) b := by
    intro b hb hab
    have hb' : b = (.inl x : V ⊕ Unit) ∨ b = .inl q ∨ b = .inl r := by
      simpa [lengthOneCorridorLeaves] using hb
    rcases hb' with hbx | hbq | hbr
    · subst b
      exact threeSpokePuncture_not_adj_ax G a x q r
        ((pendantExtension_adj_old (threeSpokePuncture G a x q r) h a x).mp hab)
    · subst b
      exact threeSpokePuncture_not_adj_aq G a x q r
        ((pendantExtension_adj_old (threeSpokePuncture G a x q r) h a q).mp hab)
    · subst b
      exact threeSpokePuncture_not_adj_ar G a x q r
        ((pendantExtension_adj_old (threeSpokePuncture G a x q r) h a r).mp hab)
  have hpositive : ∀ v,
      (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl a) v ∨
        v ∈ lengthOneCorridorLeaves x q r → 0 < D.endpointCount v := by
    intro v hv
    rcases hv with hav | hv
    · exact hDodd v
        (bare_lengthOneCorridorAuxiliary_center_neighbor_odd h x a q r H ha hha hcover v hav)
    · have hv' : v = (.inl x : V ⊕ Unit) ∨ v = .inl q ∨ v = .inl r := by
        simpa [lengthOneCorridorLeaves] using hv
      rcases hv' with hvx | hvq | hvr
      · subst v
        exact hDodd (.inl x) ox
      · subst v
        exact hDodd (.inl q) oq
      · subst v
        exact hDodd (.inl r) or
  obtain ⟨B, hsub, hxB, hBcard, E, hEsize, hEcentre, _⟩ :=
    D.prescribed_three_star_addibility (.inl a) (lengthOneCorridorLeaves x q r)
      haLeaf hcard hmissing hpositive (.inl x) (by simp [lengthOneCorridorLeaves])
  obtain ⟨F, hFsize, hFends⟩ := bare_selected_three_spoke_return h x a q r H hax haq har
    hxq hxr hqr ha hq hr hha hhq hhr D B hsub hxB hBcard E hEsize hEcentre
    (by exact Nat.succ_le_iff.mpr (hDodd (.inl a) oa))
  exact ⟨F, hFsize.trans hDsize, hFends⟩

/-- A literal length-one corridor ending at an E-degree-three private vertex
cannot occur in a bare relative minimum counterexample.  This is the completed
local contradiction; the remaining K-HUB3 work is to extract such a literal
corridor from an arbitrary private degree-three vertex. -/
theorem bare_hub_no_degree_three_of_literal_length_one_corridor
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhq : h ≠ q) (hhr : h ≠ r)
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    False := by
  obtain ⟨F, hFsize, hFends⟩ := bare_lengthOneCorridorAuxiliary_restore h x a q r H
    hax haq har hxq hxr hqr ha hq hr hha hhq hhr hcover
  apply H.counterexample.2
  refine ⟨F, ?_, hFends⟩
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_zero] using hFsize

/-- The completed literal corridor contradiction applies to every
E-degree-three vertex adjacent to the exceptional hub.  The two remaining
even neighbours are extracted from the three-element even-neighbour finset,
so this is a genuine distance-one exclusion rather than a result for a
pre-labelled triple. -/
theorem bare_hub_no_degree_three_of_adjacent
    (h x a : V) (H : BareMinimalCounterexample G h x)
    (hax : G.Adj a x) (ha : Even (G.degree a))
    (hadeg : eDegree G a = 3) : False := by
  classical
  rcases H.counterexample.1 with ⟨_, hhx, _, _, hx, hbare, _⟩
  let N : Finset V := evenNeighbors G a
  have hxN : x ∈ N := by
    exact (mem_evenNeighbors (G := G) a x).mpr ⟨hax, hx⟩
  have hNcard : #N = 3 := by
    simpa only [N, eDegree] using hadeg
  have herasecard : #(N.erase x) = 2 := by
    rw [Finset.card_erase_of_mem hxN]
    omega
  obtain ⟨q, r, hqr, hNerase⟩ := Finset.card_eq_two.mp herasecard
  have hqerase : q ∈ N.erase x := by
    rw [hNerase]
    simp
  have hrerase : r ∈ N.erase x := by
    rw [hNerase]
    simp
  have hqN : q ∈ N := (Finset.mem_erase.mp hqerase).2
  have hrN : r ∈ N := (Finset.mem_erase.mp hrerase).2
  have hxq : x ≠ q := (Finset.mem_erase.mp hqerase).1.symm
  have hxr : x ≠ r := (Finset.mem_erase.mp hrerase).1.symm
  have ⟨haq, hq⟩ := (mem_evenNeighbors (G := G) a q).mp hqN
  have ⟨har, hr⟩ := (mem_evenNeighbors (G := G) a r).mp hrN
  have hax' : a ≠ x := hax.ne
  have hha : h ≠ a := by
    intro hha
    subst a
    rw [hbare] at hadeg
    omega
  have hhq : h ≠ q := by
    intro hhq
    subst q
    have hmem : a ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h a).mpr ⟨haq.symm, ha⟩
    change (evenNeighbors G h).card = 0 at hbare
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  have hhr : h ≠ r := by
    intro hhr
    subst r
    have hmem : a ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h a).mpr ⟨har.symm, ha⟩
    change (evenNeighbors G h).card = 0 at hbare
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  apply bare_hub_no_degree_three_of_literal_length_one_corridor h x a q r H
    hax haq har hxq hxr hqr ha hq hr hha hhq hhr
  intro w haw hweven
  have hwN : w ∈ N := (mem_evenNeighbors (G := G) a w).mpr ⟨haw, hweven⟩
  by_cases hwx : w = x
  · exact Or.inl hwx
  have hwerase : w ∈ N.erase x := Finset.mem_erase.mpr ⟨hwx, hwN⟩
  rw [hNerase] at hwerase
  have hwqr : w = q ∨ w = r := by simpa using hwerase
  exact hwqr.elim (fun hwq => Or.inr (Or.inl hwq)) (fun hwr => Or.inr (Or.inr hwr))

/-- The prescribed bare vertex has no occurrence on a shortest even corridor
to an E-degree-three terminal: at an internal occurrence it would have an
even corridor neighbour, and at the terminal its E-degree would be three. -/
theorem bare_prescribed_not_mem_shortest_even_corridor_support
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a)
    (hadeg : eDegree G (a : V) = 3) :
    h ∉ (shortestEvenCorridorLift p).support := by
  rcases H.counterexample.1 with ⟨_, hhx, _, _, _, hbare, _⟩
  intro hmem
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hi, hile⟩ := hmem
  rw [shortestEvenCorridorLift_getVert] at hi
  by_cases hilast : i = p.length
  · subst i
    rw [p.getVert_length] at hi
    have hhadeg : eDegree G h = 3 := by
      simpa [hi] using hadeg
    omega
  have hile' : i ≤ p.length := by simpa using hile
  have hilt : i < p.length := Nat.lt_of_le_of_ne hile' hilast
  have hadj : G.Adj h (p.getVert (i + 1) : V) := by
    rw [← hi]
    exact p.adj_getVert_succ (i := i) hilt
  have hneigh : (p.getVert (i + 1) : V) ∈ evenNeighbors G h :=
    (mem_evenNeighbors (G := G) h (p.getVert (i + 1) : V)).mpr
      ⟨hadj, (p.getVert (i + 1)).property⟩
  change (evenNeighbors G h).card = 0 at hbare
  have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨_, hneigh⟩
  omega

/-- At the E-degree-three terminal of a nontrivial shortest corridor, deleting
the corridor predecessor leaves two distinct even neighbours.  Both are
outside the ambient corridor support, so they are available as the terminal
leaves in the corridor auxiliary. -/
theorem bare_shortest_even_corridor_terminal_extra_leaves
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) (hlen : 1 < p.length) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r := by
  classical
  rcases H.counterexample.1 with ⟨_, _, _, _, hx, hbare, _⟩
  let b : evenVertices G := p.getVert (p.length - 1)
  have hba : (evenSubgraph G).Adj b a := by
    have hindex : p.length - 1 + 1 = p.length := Nat.sub_add_cancel (by omega)
    change (evenSubgraph G).Adj (p.getVert (p.length - 1)) a
    have hstep := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [hindex, p.getVert_length] at hstep
    exact hstep
  let N : Finset V := evenNeighbors G (a : V)
  have hbN : (b : V) ∈ N := by
    exact (mem_evenNeighbors (G := G) (a : V) (b : V)).mpr ⟨hba.symm, b.property⟩
  have hNcard : #N = 3 := by
    simpa only [N, eDegree] using hadeg
  have herasecard : #(N.erase (b : V)) = 2 := by
    rw [Finset.card_erase_of_mem hbN]
    omega
  obtain ⟨q, r, hqr, hNerase⟩ := Finset.card_eq_two.mp herasecard
  have hqerase : q ∈ N.erase (b : V) := by
    rw [hNerase]
    simp
  have hrerase : r ∈ N.erase (b : V) := by
    rw [hNerase]
    simp
  have hqN : q ∈ N := (Finset.mem_erase.mp hqerase).2
  have hrN : r ∈ N := (Finset.mem_erase.mp hrerase).2
  have hqb : (b : V) ≠ q := (Finset.mem_erase.mp hqerase).1.symm
  have hrb : (b : V) ≠ r := (Finset.mem_erase.mp hrerase).1.symm
  have ⟨haq, hqeven⟩ := (mem_evenNeighbors (G := G) (a : V) q).mp hqN
  have ⟨har, hreven⟩ := (mem_evenNeighbors (G := G) (a : V) r).mp hrN
  let q' : evenVertices G := ⟨q, hqeven⟩
  let r' : evenVertices G := ⟨r, hreven⟩
  have hqa : (evenSubgraph G).Adj q' a := by
    exact haq.symm
  have hra : (evenSubgraph G).Adj r' a := by
    exact har.symm
  have hqpred : p.getVert (p.length - 1) ≠ q' := by
    intro e
    apply hqb
    simpa [b, q'] using congrArg Subtype.val e
  have hrpred : p.getVert (p.length - 1) ≠ r' := by
    intro e
    apply hrb
    simpa [b, r'] using congrArg Subtype.val e
  have hqoff := shortest_even_corridor_terminal_neighbor_not_mem_support
    x a q' p hdist hqa hlen hqpred
  have hroff := shortest_even_corridor_terminal_neighbor_not_mem_support
    x a r' p hdist hra hlen hrpred
  have hhq : (h : V) ≠ q' := by
    intro e
    have hmem : (a : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h (a : V)).mpr
        ⟨by simpa [e, q'] using haq.symm, a.property⟩
    change (evenNeighbors G h).card = 0 at hbare
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  have hhr : (h : V) ≠ r' := by
    intro e
    have hmem : (a : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h (a : V)).mpr
        ⟨by simpa [e, r'] using har.symm, a.property⟩
    change (evenNeighbors G h).card = 0 at hbare
    have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨a, hmem⟩
    omega
  refine ⟨q', r', hqa, hra, ?_, hqoff, hroff, hhq, hhr⟩
  intro e
  apply hqr
  simpa [q', r'] using congrArg Subtype.val e

/-- A shortest even corridor from the exceptional hub to a degree-three
vertex has genuine positive internal length in a bare minimal
counterexample.  Length zero would make the exceptional hub E-degree three,
and length one is the already eliminated adjacent case. -/
theorem bare_shortest_even_corridor_length_ge_two
    (h : V) (x a : evenVertices G)
    (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    2 ≤ p.length := by
  by_contra hlength
  have hle : p.length ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos p.length with hzero | hpos
  · have hdistzero : (evenSubgraph G).dist x a = 0 := by
      rw [← hdist, hzero]
    have hax : a = x := ((p.reachable.dist_eq_zero_iff).mp hdistzero).symm
    subst a
    have hgt := H.counterexample.exception_gt_three
    omega
  · have hone : p.length = 1 := by omega
    have hdistone : (evenSubgraph G).dist x a = 1 := by
      rw [← hdist, hone]
    have hxa : (evenSubgraph G).Adj x a :=
      SimpleGraph.dist_eq_one_iff_adj.mp hdistone
    exact bare_hub_no_degree_three_of_adjacent h (x : V) (a : V) H hxa.symm
      a.property hadeg

/-- The shortest-corridor terminal witnesses instantiate the literal
corridor-auxiliary parity profile: both terminal leaves and the protected
bare vertex are odd after the puncture and pendant extension. -/
theorem bare_shortest_even_corridor_auxiliary_terminal_odd_profile
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) (hlen : 1 < p.length) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl q)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl r)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) := by
  rcases H.counterexample.1 with ⟨_, _, _, hheven, _, _, _⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr⟩ :=
    bare_shortest_even_corridor_terminal_extra_leaves h x a H p hdist hadeg hlen
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have haq : G.Adj (a : V) (q : V) := hqa.symm
  have har : G.Adj (a : V) (r : V) := hra.symm
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  obtain ⟨hqodd, hrodd, hhodd⟩ := corridorAuxiliary_terminal_odd_profile G
    (shortestEvenCorridorLift p) hqoff hroff hhoff
    hqr' hqh hrh
    haq har q.property r.property hheven
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hqodd, hrodd, hhodd⟩

/-- The complete affected-old-vertex parity profile for a shortest nontrivial
corridor.  In addition to the two terminal leaves and pendant attachment,
the initial exceptional hub is odd because precisely its first corridor edge
is deleted. -/
theorem bare_shortest_even_corridor_auxiliary_full_odd_profile
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) := by
  rcases H.counterexample.1 with ⟨_, hhx, _, _, _, _, _⟩
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hlen : 1 < p.length := by omega
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hqodd, hrodd, hhodd⟩ :=
    bare_shortest_even_corridor_auxiliary_terminal_odd_profile h x a H p hdist hadeg hlen
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hxaSubtype : x ≠ a := by
    intro hxa
    have hzero : p.length = 0 :=
      ((hp.nil_iff_eq).mpr hxa).length_eq_zero
    omega
  have hxa : (x : V) ≠ a := fun e => hxaSubtype (Subtype.ext e)
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxh : (x : V) ≠ h := hhx.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hxodd := odd_degree_corridorAuxiliary_start G (shortestEvenCorridorLift p)
    hpath hnil hxa hxq hxr hxh x.property
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hxodd, hqodd, hrodd, hhodd⟩

/-- The degree-three terminal of a nontrivial shortest even corridor is also
odd in the pendant auxiliary: its corridor edge and two extra terminal spokes
are precisely the three deleted incident edges. -/
theorem bare_shortest_even_corridor_auxiliary_terminal_center_odd
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) := by
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hlen : 1 < p.length := by omega
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr⟩ :=
    bare_shortest_even_corridor_terminal_extra_leaves h x a H p hdist hadeg hlen
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hah : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have haq : G.Adj (a : V) (q : V) := hqa.symm
  have har : G.Adj (a : V) (r : V) := hra.symm
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have haodd := odd_degree_corridorAuxiliary_terminal_center G
    (shortestEvenCorridorLift p) hpath hnil hqoff hroff hqr' haq har a.property hah
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, haodd⟩

/-- The shortest-corridor auxiliary has a single coherent five-vertex odd
profile: start hub, both terminal leaves, pendant attachment, and the
degree-three terminal. -/
theorem bare_shortest_even_corridor_auxiliary_complete_odd_profile
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hxodd, hqodd, hrodd, hhodd⟩ :=
    bare_shortest_even_corridor_auxiliary_full_odd_profile h x a H p hp hdist hadeg
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hah : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have haq : G.Adj (a : V) (q : V) := hqa.symm
  have har : G.Adj (a : V) (r : V) := hra.symm
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have haodd := odd_degree_corridorAuxiliary_terminal_center G
    (shortestEvenCorridorLift p) hpath hnil hqoff hroff hqr' haq har a.property hah
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hxodd, hqodd, hrodd, hhodd, haodd⟩

/-- In the nontrivial shortest-corridor branch, the two terminal leaves
selected from an E-degree-three terminal also make every proper internal
corridor vertex isolated in the auxiliary even graph.  The closest-witness
hypothesis is kept explicit: it is the source of the exact original
E-degree-two calculation at the internal position. -/
theorem bare_shortest_even_corridor_auxiliary_internal_eDegree_zero
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      eDegree (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
        (.inl ((shortestEvenCorridorLift p).getVert i)) = 0 := by
  rcases H.counterexample.1 with ⟨_, _, _, hheven, _, _, _⟩
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hlen : 1 < p.length := by omega
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr⟩ :=
    bare_shortest_even_corridor_terminal_extra_leaves h x a H p hdist hadeg hlen
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hdegree := shortest_even_corridor_internal_eDegree_eq_two_of_bare
    h x a H p hp hdist hclosest i hi hiend
  have hdegree' : eDegree G ((shortestEvenCorridorLift p).getVert i) = 2 := by
    simpa only [shortestEvenCorridorLift_getVert] using hdegree
  have hiend' : i < (shortestEvenCorridorLift p).length := by
    simpa only [shortestEvenCorridorLift_length] using hiend
  have hzh : (shortestEvenCorridorLift p).getVert i ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨i, rfl, Nat.le_of_lt hiend'⟩
  have haq : G.Adj (a : V) (q : V) := hqa.symm
  have har : G.Adj (a : V) (r : V) := hra.symm
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hzero := corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
    (shortestEvenCorridorLift p) hpath i hi hiend'
    (fun w hw => shortestEvenCorridorLift_support_even p w hw)
    hqoff hroff hhoff hqr' hqh hrh haq har q.property r.property hheven hzh hdegree'
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hzero⟩

/-- The preceding literal internal-isolation fact excludes SET on every
auxiliary component that contains the chosen proper internal corridor
vertex.  This is the first componentwise clause of the nontrivial-corridor
floor audit; components avoiding all such vertices remain a separate
boundary-classification obligation. -/
theorem bare_shortest_even_corridor_auxiliary_internal_component_not_set
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      ∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl ((shortestEvenCorridorLift p).getVert i) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hzero⟩ :=
    bare_shortest_even_corridor_auxiliary_internal_eDegree_zero
      h x a H p hp hdist hclosest hadeg i hi hiend
  have hiend' : i < (shortestEvenCorridorLift p).length := by
    simpa only [shortestEvenCorridorLift_length] using hiend
  have himem : (shortestEvenCorridorLift p).getVert i ∈
      (shortestEvenCorridorLift p).support :=
    (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨i, rfl, Nat.le_of_lt hiend'⟩
  have heven : Even (G.degree ((shortestEvenCorridorLift p).getVert i)) :=
    shortestEvenCorridorLift_support_even p _ himem
  have hza : (shortestEvenCorridorLift p).getVert i ≠ (a : V) := by
    intro e
    have hindex : i = p.length := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
      (by
        apply Subtype.ext
        simpa only [shortestEvenCorridorLift_getVert, p.getVert_length] using e)
    omega
  have hzq : (shortestEvenCorridorLift p).getVert i ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact himem
  have hzr : (shortestEvenCorridorLift p).getVert i ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact himem
  have hzh : (shortestEvenCorridorLift p).getVert i ≠ h := by
    have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
    intro e
    apply hhoff
    rw [← e]
    exact himem
  have hpath := shortestEvenCorridorLift_isPath p hp
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hevenAux := even_degree_corridorAuxiliary_internal G
    (shortestEvenCorridorLift p) hpath i hi hiend' hza hzq hzr hzh heven
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_⟩
  intro C _ hiC
  exact corridorAuxiliary_internal_component_not_set_of_even_eDegree_zero G
    (shortestEvenCorridorLift p) i C hiC hevenAux hzero

/-- In the shortest nontrivial corridor branch, the two terminal leaves can
be selected so that no SET component contains both.  The initial hub is
auxiliary-odd after the corridor deletion, so it cannot be the unbounded
original-E-degree common SET witness in the capacity argument. -/
theorem bare_shortest_even_corridor_terminal_pair_set_separated
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      ∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp) := by
  rcases H.counterexample.1 with ⟨_, hhx, _, hheven, _, _, hcap⟩
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hlen : 1 < p.length := by omega
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hqodd, hrodd, hhodd⟩ :=
    bare_shortest_even_corridor_auxiliary_terminal_odd_profile h x a H p hdist hadeg hlen
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hxaSubtype : x ≠ a := by
    intro hxa
    have hzero : p.length = 0 :=
      ((hp.nil_iff_eq).mpr hxa).length_eq_zero
    omega
  have hxa : (x : V) ≠ a := fun e => hxaSubtype (Subtype.ext e)
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxh : (x : V) ≠ h := hhx.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hxodd := odd_degree_corridorAuxiliary_start G (shortestEvenCorridorLift p)
    hpath hnil hxa hxq hxr hxh x.property
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_⟩
  intro C _ hqC hrC hset
  exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
    (shortestEvenCorridorLift p) C
    (fun z hz => shortestEvenCorridorLift_support_even p z hz)
    hqodd hrodd hhodd hxodd hqodd hrodd q.property r.property
    (fun e => hhq e.symm) (fun e => hhr e.symm)
    (fun e => hqr (Subtype.ext e)) hcap hqC hrC hset

/-- In the same shortest-corridor branch, no SET component contains both the
initial hub and either selected terminal leaf.  This is the remaining
start/terminal pairwise capacity exclusion; it is stated with the selected
leaf existentially, as required by the shortest-corridor construction. -/
theorem bare_shortest_even_corridor_start_terminal_set_separated
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) := by
  rcases H.counterexample.1 with ⟨_, hhx, _, _, _, _, hcap⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, hxodd, hqodd, hrodd, hhodd⟩ :=
    bare_shortest_even_corridor_auxiliary_full_odd_profile h x a H p hp hdist hadeg
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_, ?_⟩
  · intro C _ hxC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hqodd x.property q.property
      hhx.symm (fun e => hhq e.symm) hxq hcap hxC hqC hset
  · intro C _ hxC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hrodd x.property r.property
      hhx.symm (fun e => hhr e.symm) hxr hcap hxC hrC hset

/-- The degree-three terminal cannot share a SET component with either of its
two selected terminal leaves.  This supplies the two pairwise exclusions that
the nontrivial corridor component audit was previously missing. -/
theorem bare_shortest_even_corridor_center_terminal_set_separated
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) := by
  rcases H.counterexample.1 with ⟨_, _, _, _, _, _, hcap⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd⟩ :=
    bare_shortest_even_corridor_auxiliary_complete_odd_profile h x a H p hp hdist hadeg
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hah : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have haq : (a : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have har : (a : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_, ?_⟩
  · intro C _ haC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hqodd a.property q.property
      hah (fun e => hhq e.symm) haq hcap haC hqC hset
  · intro C _ haC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hrodd a.property r.property
      hah (fun e => hhr e.symm) har hcap haC hrC hset

/-- A single choice of terminal leaves excludes every pair among the start,
terminal, and two terminal leaves from one auxiliary SET component. -/
theorem bare_shortest_even_corridor_all_deleted_contacts_set_separated
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) := by
  rcases H.counterexample.1 with ⟨_, hhx, _, _, _, _, hcap⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd⟩ :=
    bare_shortest_even_corridor_auxiliary_complete_odd_profile h x a H p hp hdist hadeg
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hxa : (x : V) ≠ a := by
    intro e
    have hxaSubtype : x = a := Subtype.ext e
    have hzero : p.length = 0 := ((hp.nil_iff_eq).mpr hxaSubtype).length_eq_zero
    omega
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hah : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have haq : (a : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have har : (a : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C _ hxC haC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd haodd x.property a.property
      hhx.symm hah hxa hcap hxC haC hset
  · intro C _ hxC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hqodd x.property q.property
      hhx.symm (fun e => hhq e.symm) hxq hcap hxC hqC hset
  · intro C _ hxC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hrodd x.property r.property
      hhx.symm (fun e => hhr e.symm) hxr hcap hxC hrC hset
  · intro C _ hqC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hqodd hrodd q.property r.property
      (fun e => hhq e.symm) (fun e => hhr e.symm) hqr' hcap hqC hrC hset
  · intro C _ haC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hqodd a.property q.property
      hah (fun e => hhq e.symm) haq hcap haC hqC hset
  · intro C _ haC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hrodd a.property r.property
      hah (fun e => hhr e.symm) har hcap haC hrC hset

/-- The shared terminal-leaf witnesses can also be used for every proper
internal corridor position: under the closest-terminal hypothesis, its
auxiliary component is not SET.  Unlike the earlier pointwise result, this
keeps one witness pair fixed for all internal indices. -/
theorem bare_shortest_even_corridor_shared_internal_components_not_set
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp → (.inl (a : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp → (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (x : V) : V ⊕ Unit) ∈ C.supp → (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (q : V) : V ⊕ Unit) ∈ C.supp → (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp → (.inl (q : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      (∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          (.inl (a : V) : V ⊕ Unit) ∈ C.supp → (.inl (r : V) : V ⊕ Unit) ∈ C.supp →
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp)) ∧
      ∀ i : ℕ, 0 < i → i < p.length →
        ∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
          ∀ [DecidablePred (· ∈ C.supp)],
            (.inl ((shortestEvenCorridorLift p).getVert i) : V ⊕ Unit) ∈ C.supp →
            ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp) := by
  rcases H.counterexample.1 with ⟨_, hhx, _, hheven, _, _, hcap⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd⟩ :=
    bare_shortest_even_corridor_auxiliary_complete_odd_profile h x a H p hp hdist hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hxaSubtype : x ≠ a := by
    intro hxa
    have hzero : p.length = 0 := ((hp.nil_iff_eq).mpr hxa).length_eq_zero
    have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
    omega
  have hxa : (x : V) ≠ a := fun e => hxaSubtype (Subtype.ext e)
  have hxh : (x : V) ≠ h := hhx.symm
  have hah : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have haq : (a : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have har : (a : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).end_mem_support
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C _ hxC haC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd haodd x.property a.property
      hhx.symm hah hxa hcap hxC haC hset
  · intro C _ hxC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hqodd x.property q.property
      hhx.symm (fun e => hhq e.symm) hxq hcap hxC hqC hset
  · intro C _ hxC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hxodd hrodd x.property r.property
      hhx.symm (fun e => hhr e.symm) hxr hcap hxC hrC hset
  · intro C _ hqC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd hqodd hrodd q.property r.property
      (fun e => hhq e.symm) (fun e => hhr e.symm) hqr' hcap hqC hrC hset
  · intro C _ haC hqC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hqodd a.property q.property
      hah (fun e => hhq e.symm) haq hcap haC hqC hset
  · intro C _ haC hrC hset
    exact corridorAuxiliary_set_component_not_contains_odd_pair_of_cap G
      (shortestEvenCorridorLift p) C
      (fun z hz => shortestEvenCorridorLift_support_even p z hz)
      hqodd hrodd hhodd hxodd haodd hrodd a.property r.property
      hah (fun e => hhr e.symm) har hcap haC hrC hset
  · intro i hi hiend C _ hiC
    have hiend' : i < (shortestEvenCorridorLift p).length := by
      simpa only [shortestEvenCorridorLift_length] using hiend
    have himem : (shortestEvenCorridorLift p).getVert i ∈
        (shortestEvenCorridorLift p).support :=
      (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
        ⟨i, rfl, Nat.le_of_lt hiend'⟩
    have heven : Even (G.degree ((shortestEvenCorridorLift p).getVert i)) :=
      shortestEvenCorridorLift_support_even p _ himem
    have hdegree := shortest_even_corridor_internal_eDegree_eq_two_of_bare
      h x a H p hp hdist hclosest i hi hiend
    have hdegree' : eDegree G ((shortestEvenCorridorLift p).getVert i) = 2 := by
      simpa only [shortestEvenCorridorLift_getVert] using hdegree
    have hzh : (shortestEvenCorridorLift p).getVert i ≠ h := by
      intro e
      apply hhoff
      rw [← e]
      exact himem
    have hza : (shortestEvenCorridorLift p).getVert i ≠ (a : V) := by
      intro e
      have hindex : i = p.length := hp.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
        (by
          apply Subtype.ext
          simpa only [shortestEvenCorridorLift_getVert, p.getVert_length] using e)
      omega
    have hzq : (shortestEvenCorridorLift p).getVert i ≠ q := by
      intro e
      apply hqoff
      rw [← e]
      exact himem
    have hzr : (shortestEvenCorridorLift p).getVert i ≠ r := by
      intro e
      apply hroff
      rw [← e]
      exact himem
    have hevenAux := even_degree_corridorAuxiliary_internal G
      (shortestEvenCorridorLift p) hpath i hi hiend' hza hzq hzr hzh heven
    have hzero := corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
      (shortestEvenCorridorLift p) hpath i hi hiend'
      (fun w hw => shortestEvenCorridorLift_support_even p w hw)
      hqoff hroff hhoff hqr' hqh hrh hqa.symm hra.symm q.property r.property hheven hzh hdegree'
    exact corridorAuxiliary_internal_component_not_set_of_even_eDegree_zero G
      (shortestEvenCorridorLift p) i C hiC hevenAux hzero

/-- In the nontrivial shortest-corridor auxiliary, every SET component has
exactly one contact among the two corridor endpoints and the two deleted
terminal leaves.  The pendant component and all proper internal corridor
contacts have already been excluded; the remaining pairwise exclusions make
the contact unique. -/
theorem bare_shortest_even_corridor_set_component_one_contact
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) ∧
      ∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp) →
          ((.inl (x : V) : V ⊕ Unit) ∈ C.supp ∨
            (.inl (a : V) : V ⊕ Unit) ∈ C.supp ∨
            (.inl (q : V) : V ⊕ Unit) ∈ C.supp ∨
            (.inl (r : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (x : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (a : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (x : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (q : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (x : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (r : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (q : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (r : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (a : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (q : V) : V ⊕ Unit) ∈ C.supp) ∧
          ¬ ((.inl (a : V) : V ⊕ Unit) ∈ C.supp ∧ (.inl (r : V) : V ⊕ Unit) ∈ C.supp) ∧
          ∀ i : ℕ, 0 < i → i < p.length →
            (.inl ((shortestEvenCorridorLift p).getVert i) : V ⊕ Unit) ∉ C.supp := by
  rcases H.counterexample.1 with ⟨hconn, _, _, _, _, _, _⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, hxa, hxq, hxr, hqr', haq, har, hinter⟩ :=
    bare_shortest_even_corridor_shared_internal_components_not_set
      h x a H p hp hdist hclosest hadeg
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, ?_⟩
  intro C _ hset
  have hentry := corridorAuxiliary_set_component_meets_deleted_support G
    (shortestEvenCorridorLift p) C hconn hset
  obtain ⟨z, hzC, hz⟩ := hentry
  have hcontact :
      (.inl (x : V) : V ⊕ Unit) ∈ C.supp ∨
      (.inl (a : V) : V ⊕ Unit) ∈ C.supp ∨
      (.inl (q : V) : V ⊕ Unit) ∈ C.supp ∨
      (.inl (r : V) : V ⊕ Unit) ∈ C.supp := by
    rcases hz with hz | hz | hz
    · rcases shortestEvenCorridorLift_support_cases p hz with hzx | hza | ⟨i, hi, hiend, hzi⟩
      · left
        simpa [hzx] using hzC
      · right; left
        simpa [hza] using hzC
      · have hiC : (.inl ((shortestEvenCorridorLift p).getVert i) : V ⊕ Unit) ∈ C.supp := by
          simpa [hzi] using hzC
        exact False.elim (hinter i hi hiend C hiC hset)
    · right; right; left
      simpa [hz] using hzC
    · right; right; right
      simpa [hz] using hzC
  refine ⟨hcontact, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hxC
    exact hxa C hxC.1 hxC.2 hset
  · intro hxC
    exact hxq C hxC.1 hxC.2 hset
  · intro hxC
    exact hxr C hxC.1 hxC.2 hset
  · intro hqC
    exact hqr' C hqC.1 hqC.2 hset
  · intro haC
    exact haq C haC.1 haC.2 hset
  · intro haC
    exact har C haC.1 haC.2 hset
  · intro i hi hiend hiC
    exact hinter i hi hiend C hiC hset

/-- A terminal-`q` SET component of a corridor auxiliary is a literal hanging
SET in the original graph once it avoids the other deleted contacts.  The
auxiliary-to-old-core transport, intrinsic second-old-vertex fact, and exact
`q-a` boundary reduce it to the existing bare hanging-SET contradiction. -/
theorem bare_corridorAuxiliary_separated_q_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ corridorAuxiliary_oldSet G p C)]
    (hq : (.inl q : V ⊕ Unit) ∈ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (hqa : G.Adj q a)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) : False := by
  have hh : (.inl h : V ⊕ Unit) ∉ C.supp :=
    corridorAuxiliary_attachment_not_mem_of_leaf_not_mem G p C hleaf
  obtain ⟨t, ht, htq⟩ :=
    corridorAuxiliary_set_component_exists_second_old_of_mem G p C hq hleaf hset
  have hsupport : ∀ z : V, (.inl z : V ⊕ Unit) ∈ C.supp → z ∉ p.support :=
    corridorAuxiliary_component_avoids_support_of_endpoint_internal_avoids G p C hx ha hinternal
  have hsetG : IsSET (G.induce (corridorAuxiliary_oldSet G p C)) :=
    corridorAuxiliary_old_component_isSET_of_avoids_support G p C hleaf hsupport hset
  apply bare_hanging_set_literal_false h x H (corridorAuxiliary_oldSet G p C) q a t
  · exact hq
  · exact ha
  · exact ht
  · exact htq
  · exact hh
  · exact hx
  · exact hqa
  · intro u v hu hv huv
    exact corridorAuxiliary_component_crossing_is_terminal_q_of_one_contact G p C
      hq hx ha hr hinternal hu hv huv
  · exact hsetG

/-- The terminal-`r` version of the preceding literal hanging-SET reduction. -/
theorem bare_corridorAuxiliary_separated_r_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ corridorAuxiliary_oldSet G p C)]
    (hr : (.inl r : V ⊕ Unit) ∈ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (hra : G.Adj r a)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) : False := by
  have hh : (.inl h : V ⊕ Unit) ∉ C.supp :=
    corridorAuxiliary_attachment_not_mem_of_leaf_not_mem G p C hleaf
  obtain ⟨t, ht, htr⟩ :=
    corridorAuxiliary_set_component_exists_second_old_of_mem G p C hr hleaf hset
  have hsupport : ∀ z : V, (.inl z : V ⊕ Unit) ∈ C.supp → z ∉ p.support :=
    corridorAuxiliary_component_avoids_support_of_endpoint_internal_avoids G p C hx ha hinternal
  have hsetG : IsSET (G.induce (corridorAuxiliary_oldSet G p C)) :=
    corridorAuxiliary_old_component_isSET_of_avoids_support G p C hleaf hsupport hset
  apply bare_hanging_set_literal_false h x H (corridorAuxiliary_oldSet G p C) r a t
  · exact hr
  · exact ha
  · exact ht
  · exact htr
  · exact hh
  · exact hx
  · exact hra
  · intro u v hu hv huv
    exact corridorAuxiliary_component_crossing_is_terminal_r_of_one_contact G p C
      hr hx ha hq hinternal hu hv huv
  · exact hsetG

/-- A start-`x` SET component of a nontrivial corridor auxiliary would make
the exceptional vertex `x` a cut vertex, contradicting bare minimality. -/
theorem bare_corridorAuxiliary_x_side_set_false
    (h x a q r : V) (H : BareMinimalCounterexample G h x)
    (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hx : (.inl x : V ⊕ Unit) ∈ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) : False := by
  have hhx : h ≠ x := H.counterexample.1.2.1
  exact corridorAuxiliary_x_side_set_forces_not_connected G p C
    hhx hx ha hq hr hleaf hinternal hset
    (bare_exception_noncut G h x H)

/-- A terminal-centre SET component is impossible whenever the exact corridor
operation makes that centre odd with auxiliary E-degree zero. -/
theorem bare_corridorAuxiliary_terminal_center_set_false
    (h x a q r : V) (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (ha : (.inl a : V ⊕ Unit) ∈ C.supp)
    (haodd : Odd ((corridorAuxiliary G p q r h).degree (.inl a)))
    (hazero : eDegree (corridorAuxiliary G p q r h) (.inl a) = 0)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) : False := by
  exact component_not_set_of_odd_eDegree_zero C (.inl a) ha haodd hazero hset

/-- The one-contact classification has no surviving SET branch: `x` would be
a cut vertex, `a` has auxiliary E-degree zero, and `q`/`r` are literal hanging
SET components in the original graph.  This is the complete componentwise SET
audit for the selected nontrivial shortest-corridor auxiliary. -/
theorem bare_shortest_even_corridor_auxiliary_all_components_not_set
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) ∧
      ∀ (C : (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).ConnectedComponent),
        ∀ [DecidablePred (· ∈ C.supp)],
          ¬ IsSET ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).induce C.supp) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, hclass⟩ :=
    bare_shortest_even_corridor_set_component_one_contact
      h x a H p hp hdist hclosest hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil := by
    exact SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hzh : (a : V) ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨(shortestEvenCorridorLift p).length, by simp, Nat.le_refl _⟩
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have haq : G.Adj (a : V) q := hqa.symm
  have har : G.Adj (a : V) r := hra.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj := Classical.decRel _
  have hazero := corridorAuxiliary_terminal_eDegree_eq_zero_of_profile G
    (shortestEvenCorridorLift p) hpath hnil
    (fun z hz => shortestEvenCorridorLift_support_even p z hz)
    hqoff hroff hqr' hzh haq har q.property r.property hqodd hrodd hhodd hadeg
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, ?_⟩
  intro C _ hset
  by_contra hnot
  letI : DecidablePred (· ∈ corridorAuxiliary_oldSet G (shortestEvenCorridorLift p) C) :=
    Classical.decPred _
  have hleaf : (.inr () : V ⊕ Unit) ∉ C.supp := by
    intro hleaf
    exact corridorAuxiliary_pendant_component_not_set G (shortestEvenCorridorLift p) C hleaf hset
  obtain ⟨hcontact, hxaC, hxqC, hxrC, hqrC, haqC, harC, hinter⟩ := hclass C hset
  have hinterLift : ∀ i : ℕ, 0 < i → i < (shortestEvenCorridorLift p).length →
      (.inl ((shortestEvenCorridorLift p).getVert i) : V ⊕ Unit) ∉ C.supp := by
    intro i hi hiend
    exact hinter i hi (by simpa only [shortestEvenCorridorLift_length] using hiend)
  rcases hcontact with hxC | haC | hqC | hrC
  · exact bare_corridorAuxiliary_x_side_set_false h (x : V) (a : V) (q : V) (r : V) H
      (shortestEvenCorridorLift p) C hxC
      (fun haC => hxaC ⟨hxC, haC⟩)
      (fun hqC => hxqC ⟨hxC, hqC⟩)
      (fun hrC => hxrC ⟨hxC, hrC⟩)
      hleaf hinterLift hset
  · exact bare_corridorAuxiliary_terminal_center_set_false h (x : V) (a : V) (q : V) (r : V)
      (shortestEvenCorridorLift p) C haC haodd hazero hset
  · exact bare_corridorAuxiliary_separated_q_set_false h (x : V) (a : V) (q : V) (r : V) H
      (shortestEvenCorridorLift p) C hqC
      (fun hxC => hxqC ⟨hxC, hqC⟩)
      (fun haC => haqC ⟨haC, hqC⟩)
      (fun hrC => hqrC ⟨hqC, hrC⟩)
      hleaf hinterLift hqa hset
  · exact bare_corridorAuxiliary_separated_r_set_false h (x : V) (a : V) (q : V) (r : V) H
      (shortestEvenCorridorLift p) C hrC
      (fun hxC => hxrC ⟨hxC, hrC⟩)
      (fun haC => harC ⟨haC, hrC⟩)
      (fun hqC => hqrC ⟨hqC, hrC⟩)
      hleaf hinterLift hra hset

/-- The selected nontrivial shortest-corridor auxiliary satisfies the full
subcubic E-degree cap.  The proof factors through the same-type corridor
puncture: all puncture-even vertices retain original parity, the prescribed
bare vertex remains puncture-even, and the other exception becomes odd. -/
theorem bare_shortest_even_corridor_auxiliary_cap_of_selected
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hadeg : eDegree G (a : V) = 3)
    (q r : evenVertices G) (hqr : q ≠ r)
    (hqoff : (q : V) ∉ (shortestEvenCorridorLift p).support)
    (hroff : (r : V) ∉ (shortestEvenCorridorLift p).support)
    (hhq : (h : V) ≠ q) (hhr : (h : V) ≠ r) :
    ∀ v, Even ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree v) →
      eDegree (corridorAuxiliary G (shortestEvenCorridorLift p) q r h) v ≤ 3 := by
  rcases H.counterexample.1 with ⟨_, hhx, _, hheven, hxeven, hbare, hcap⟩
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hnontrivial : 0 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hnil : ¬ (shortestEvenCorridorLift p).Nil :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mpr hnontrivial
  have hxaSubtype : x ≠ a := by
    intro hxa
    have hzero : p.length = 0 :=
      ((hp.nil_iff_eq).mpr hxa).length_eq_zero
    omega
  have hxa : (x : V) ≠ a := fun e => hxaSubtype (Subtype.ext e)
  have hxq : (x : V) ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hxr : (x : V) ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact (shortestEvenCorridorLift p).start_mem_support
  have hqh : h ≠ (q : V) := hhq
  have hrh : h ≠ (r : V) := hhr
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hpunctureEven := corridorPuncture_even_implies_original_even_of_path G
    (shortestEvenCorridorLift p)
    (fun z hz => shortestEvenCorridorLift_support_even p z hz)
    hqoff hroff q.property r.property
  have hhP := even_degree_corridorPuncture_attach_of_not_mem_support G
    (shortestEvenCorridorLift p) hhoff hqh hrh hheven
  have hxoddP := odd_degree_corridorPuncture_start G (shortestEvenCorridorLift p)
    hpath hnil hxa hxq hxr hxeven
  exact corridorAuxiliary_cap_of_puncture_even_preservation G
    (shortestEvenCorridorLift p) hpunctureEven hhP hxoddP hbare hcap

/-- The selected nontrivial shortest-corridor auxiliary has the floor budget.
The cap and the all-component non-SET audit are deliberately assembled for
the same selected terminal leaves, so no existential witness is changed
between the two published-theorem inputs. -/
theorem bare_shortest_even_corridor_auxiliary_floor
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (x : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (q : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (r : V))) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl h)) ∧
      Odd ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h).degree (.inl (a : V))) ∧
      HasPathBudget (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
        (Fintype.card (V ⊕ Unit) / 2) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, hnot⟩ :=
    bare_shortest_even_corridor_auxiliary_all_components_not_set
      h x a H p hp hdist hclosest hadeg
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, ?_⟩
  apply corridorAuxiliary_floor_of_component_nonSET G (shortestEvenCorridorLift p)
  · exact bare_shortest_even_corridor_auxiliary_cap_of_selected
      h x a H p hp hdist hadeg q r hqr hqoff hroff hhq hhr
  · exact hnot

/-- Extract a floor-budget decomposition of the selected nontrivial corridor
auxiliary together with the endpoint supply forced at every displayed
auxiliary-odd vertex.  This is the exact input for the subsequent restoration
schedule; no endpoint is claimed beyond parity's one-unit guarantee. -/
theorem bare_shortest_even_corridor_auxiliary_floor_with_odd_endpoints
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      ∃ D : Decomposition (corridorAuxiliary G (shortestEvenCorridorLift p) q r h),
        D.size ≤ Fintype.card (V ⊕ Unit) / 2 ∧
        0 < D.endpointCount (.inl (x : V)) ∧
        0 < D.endpointCount (.inl (q : V)) ∧
        0 < D.endpointCount (.inl (r : V)) ∧
        0 < D.endpointCount (.inl h) ∧
        0 < D.endpointCount (.inl (a : V)) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr,
    hxodd, hqodd, hrodd, hhodd, haodd, hfloor⟩ :=
    bare_shortest_even_corridor_auxiliary_floor h x a H p hp hdist hclosest hadeg
  obtain ⟨D, hsize⟩ := hfloor
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hsize,
    D.endpointCount_pos_of_odd_degree _ hxodd,
    D.endpointCount_pos_of_odd_degree _ hqodd,
    D.endpointCount_pos_of_odd_degree _ hrodd,
    D.endpointCount_pos_of_odd_degree _ hhodd,
    D.endpointCount_pos_of_odd_degree _ haodd⟩

/-- Once the terminal leaves have been selected for the floor witness, every
proper internal corridor position has E-degree zero in that same auxiliary.
Keeping the leaves fixed is what permits restoration of more than one
successive corridor edge. -/
theorem bare_shortest_even_corridor_auxiliary_internal_zero_of_selected
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3)
    (q r : evenVertices G)
    (hqa : (evenSubgraph G).Adj q a) (hra : (evenSubgraph G).Adj r a) (hqr : q ≠ r)
    (hqoff : (q : V) ∉ (shortestEvenCorridorLift p).support)
    (hroff : (r : V) ∉ (shortestEvenCorridorLift p).support)
    (hhq : (h : V) ≠ q) (hhr : (h : V) ≠ r)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length) :
    eDegree (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
      (.inl ((shortestEvenCorridorLift p).getVert i)) = 0 := by
  rcases H.counterexample.1 with ⟨_, _, _, hheven, _, _, _⟩
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hdegree := shortest_even_corridor_internal_eDegree_eq_two_of_bare
    h x a H p hp hdist hclosest i hi hiend
  have hdegree' : eDegree G ((shortestEvenCorridorLift p).getVert i) = 2 := by
    simpa only [shortestEvenCorridorLift_getVert] using hdegree
  have hiend' : i < (shortestEvenCorridorLift p).length := by
    simpa only [shortestEvenCorridorLift_length] using hiend
  have hzh : (shortestEvenCorridorLift p).getVert i ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨i, rfl, Nat.le_of_lt hiend'⟩
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  have haq : G.Adj (a : V) (q : V) := hqa.symm
  have har : G.Adj (a : V) (r : V) := hra.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  exact corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
    (shortestEvenCorridorLift p) hpath i hi hiend'
    (fun w hw => shortestEvenCorridorLift_support_even p w hw)
    hqoff hroff hhoff hqr' hqh hrh haq har q.property r.property hheven hzh hdegree'

/- The initial E-degree-zero fact for a proper corridor vertex persists after
all earlier corridor edges have been restored.  The auxiliary removes the
immediate predecessor edge; every more distant earlier position is separated
by the geodesic no-chord condition.  This provides the exact graph-indexed
ledger required by `restore_chain_of_zero_centres`. -/
set_option maxHeartbeats 5000000 in
theorem bare_shortest_even_corridor_auxiliary_internal_zero_after_prefix
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3)
    (q r : evenVertices G)
    (hqa : (evenSubgraph G).Adj q a) (hra : (evenSubgraph G).Adj r a) (hqr : q ≠ r)
    (hqoff : (q : V) ∉ (shortestEvenCorridorLift p).support)
    (hroff : (r : V) ∉ (shortestEvenCorridorLift p).support)
    (hhq : (h : V) ≠ q) (hhr : (h : V) ≠ r)
    (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    [inst : DecidableRel
      (Decomposition.restorationChainGraph
        (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
        (fun j => (.inl ((shortestEvenCorridorLift p).getVert j) : V ⊕ Unit)) (i - 1)).Adj] :
    eDegree
      (Decomposition.restorationChainGraph
        (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
        (fun j => (.inl ((shortestEvenCorridorLift p).getVert j) : V ⊕ Unit)) (i - 1))
      (.inl ((shortestEvenCorridorLift p).getVert i)) = 0 := by
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  letI : DecidableRel (corridorAuxiliary G W q r h).Adj := Classical.decRel _
  letI : DecidableRel
      (Decomposition.restorationChainGraph (corridorAuxiliary G W q r h)
        (fun j => (.inl (W.getVert j) : V ⊕ Unit)) (i - 1)).Adj := inst
  have hzero := bare_shortest_even_corridor_auxiliary_internal_zero_of_selected
    h x a H p hp hdist hclosest hadeg q r hqa hra hqr hqoff hroff hhq hhr i hi hiend
  have hzeroBase : eDegree (corridorAuxiliary G W q r h) (.inl (W.getVert i)) = 0 := by
    simpa only [W] using hzero
  have hbase : ∀ j, j ≤ i - 1 →
      ¬ (corridorAuxiliary G W q r h).Adj (.inl (W.getVert i)) (.inl (W.getVert j)) := by
    intro j hj
    by_cases hprev : j + 1 = i
    · subst i
      have hjpos : 0 < j + 1 := by omega
      have hjend : j + 1 < W.length := by
        rw [hWlen]
        exact hiend
      exact corridorAuxiliary_not_adj_internal_previous G W (j + 1) hjpos hjend
    · have hjgap : j + 1 < i := by omega
      intro hadj
      have horig := (corridorAuxiliary_adj_old_iff G W).mp hadj |>.1
      apply shortest_even_corridor_not_adj_getVert x a p hdist j i hjgap
        (by omega)
      change G.Adj ((p.getVert j : evenVertices G) : V)
        ((p.getVert i : evenVertices G) : V)
      simpa only [W, shortestEvenCorridorLift_getVert] using horig.symm
  have hne : ∀ j, j ≤ i - 1 → (.inl (W.getVert i) : V ⊕ Unit) ≠ .inl (W.getVert j) := by
    intro j hj he
    have hindex : i = j := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; exact Nat.le_of_lt hiend)
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (Sum.inl.inj he)
    omega
  have hzeroPrefix := Decomposition.restorationChainGraph_eDegree_zero_of_base
    (G := corridorAuxiliary G W q r h)
    (v := fun j => (.inl (W.getVert j) : V ⊕ Unit))
    (n := i - 1) (w := .inl (W.getVert i)) hzeroBase hbase hne
  change @eDegree (V ⊕ Unit) _
    (Decomposition.restorationChainGraph (corridorAuxiliary G W q r h)
      (fun j => (.inl (W.getVert j) : V ⊕ Unit)) (i - 1))
    inst (.inl (W.getVert i)) = 0
  have hdec :
      Decomposition.restorationChainGraphDecidableRel
        (fun j => (.inl (W.getVert j) : V ⊕ Unit)) (i - 1) = inst :=
    Subsingleton.elim _ _
  rw [hdec] at hzeroPrefix
  exact hzeroPrefix

/- Restoring every corridor edge except the final one turns the old corridor
puncture into the literal three-spoke puncture at that final edge.  This is a
pure graph identity: path restoration and endpoint accounting are consumers
of the identity, not hypotheses hidden inside it. -/
set_option maxHeartbeats 2000000 in
theorem corridorPuncture_restore_prefix_eq_threeSpoke
    {x a q r : V} (p : G.Walk x a) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support) :
    Decomposition.restorationChainGraph (corridorPuncture G p q r)
      (fun i => p.getVert i) (p.length - 1) =
      threeSpokePuncture G a (p.getVert (p.length - 1)) q r := by
  classical
  let b := p.getVert (p.length - 1)
  have hterminal : s(a, b) ∈ p.edges := by
    rw [Sym2.eq_swap]
    apply p.mk_mem_edges_iff_exists.mpr
    refine ⟨p.length - 1, by omega, ?_⟩
    simp [b, Nat.sub_add_cancel (by omega : 1 ≤ p.length)]
  ext u v
  rw [Decomposition.restorationChainGraph_adj_iff]
  simp only [threeSpokePuncture, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff]
  constructor
  · intro huv
    rcases huv with huv | ⟨i, hi, hile, hne, he⟩
    · obtain ⟨huvG, hnotpath, hnotq, hnotr⟩ :=
        (corridorPuncture_adj_iff G p).mp huv
      refine ⟨⟨⟨huvG, ?_⟩, ?_⟩, ?_⟩
      · intro h
        exact hnotpath (h ▸ hterminal)
      · exact hnotq
      · exact hnotr
    · have hi_lt : i < p.length := by omega
      have him1_lt : i - 1 < p.length := by omega
      have hEdge : s(u, v) = s(p.getVert i, p.getVert (i - 1)) := he
      have hG : G.Adj u v := by
        rcases Sym2.eq_iff.mp hEdge with h | h
        · simpa only [h.1, h.2, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)] using
            (p.adj_getVert_succ (i := i - 1) (by omega)).symm
        · simpa only [h.1, h.2, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)] using
            p.adj_getVert_succ (i := i - 1) (by omega)
      refine ⟨⟨⟨hG, ?_⟩, ?_⟩, ?_⟩
      · intro hterm
        have hpair : s(p.getVert i, p.getVert (i - 1)) = s(a, b) :=
          hEdge.symm.trans hterm
        rcases Sym2.eq_iff.mp hpair with hpair | hpair
        · have htoend : p.getVert i = p.getVert p.length := by
            simpa only [p.getVert_length] using hpair.1
          have hi_eq : i = p.length := hp.getVert_injOn
            (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hi_lt)
            (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
            htoend
          omega
        · have htoend : p.getVert (i - 1) = p.getVert p.length := by
            simpa only [p.getVert_length] using hpair.2
          have him1_eq : i - 1 = p.length := hp.getVert_injOn
            (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt him1_lt)
            (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
            htoend
          omega
      · intro hq
        apply hqoff
        rcases Sym2.eq_iff.mp (hEdge.symm.trans hq) with hq' | hq'
        · exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
            ⟨i - 1, hq'.2, Nat.le_of_lt him1_lt⟩
        · exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
            ⟨i, hq'.1, Nat.le_of_lt hi_lt⟩
      · intro hr
        apply hroff
        rcases Sym2.eq_iff.mp (hEdge.symm.trans hr) with hr' | hr'
        · exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
            ⟨i - 1, hr'.2, Nat.le_of_lt him1_lt⟩
        · exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
            ⟨i, hr'.1, Nat.le_of_lt hi_lt⟩
  · rintro ⟨⟨⟨huvG, hnotterm⟩, hnotq⟩, hnotr⟩
    by_cases hpath : s(u, v) ∈ p.edges
    · obtain ⟨j, hj, hej⟩ := p.mk_mem_edges_iff_exists.mp hpath
      have hj_ne : j ≠ p.length - 1 := by
        intro hjeq
        apply hnotterm
        subst j
        rw [← hej, Sym2.eq_swap]
        simp [b, Nat.sub_add_cancel (by omega : 1 ≤ p.length)]
      refine Or.inr ⟨j + 1, by omega, by omega, ?_, ?_⟩
      · intro hsame
        have hjplus : j + 1 = j := hp.getVert_injOn
          (by simp only [Set.mem_ofPred_eq]; omega)
          (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hj)
          hsame
        omega
      · rw [Nat.add_sub_cancel]
        calc
          s(u, v) = s(p.getVert j, p.getVert (j + 1)) := hej.symm
          _ = s(p.getVert (j + 1), p.getVert j) := Sym2.eq_swap
    · exact Or.inl ((corridorPuncture_adj_iff G p).mpr
        ⟨huvG, hpath, hnotq, hnotr⟩)

/- The same identity survives the fresh pendant extension used by the
endpoint-preserving corridor auxiliary.  It is the type-correct connection
between the multi-edge corridor repair and the literal length-one interface. -/
set_option maxHeartbeats 2000000 in
theorem corridorAuxiliary_restore_prefix_eq_lengthOne
    {x a q r h : V} (p : G.Walk x a) (hp : p.IsPath)
    (hlen : 2 ≤ p.length)
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support) :
    Decomposition.restorationChainGraph (corridorAuxiliary G p q r h)
      (fun i => (.inl (p.getVert i) : V ⊕ Unit)) (p.length - 1) =
      lengthOneCorridorAuxiliary G h a (p.getVert (p.length - 1)) q r := by
  rw [show corridorAuxiliary G p q r h =
      pendantExtension (corridorPuncture G p q r) h from rfl,
    Decomposition.restorationChainGraph_pendantExtension,
    corridorPuncture_restore_prefix_eq_threeSpoke p hp hlen hqoff hroff]

/- Every corridor edge except the final terminal edge of a nontrivial
shortest corridor restores in order at the floor budget.  The only remaining
edge at the degree-three terminal is then restored together with its two
selected terminal leaves by a three-spoke operation. -/
set_option maxHeartbeats 2000000 in
theorem bare_shortest_even_corridor_auxiliary_restore_internal_prefix
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      ∃ E : Decomposition
        (Decomposition.restorationChainGraph
          (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
          (fun j => (.inl ((shortestEvenCorridorLift p).getVert j) : V ⊕ Unit))
          (p.length - 1)),
        E.size ≤ Fintype.card (V ⊕ Unit) / 2 ∧
        0 < E.endpointCount (.inl ((shortestEvenCorridorLift p).getVert
          (p.length - 1))) ∧
        0 < E.endpointCount (.inl (a : V)) ∧
        0 < E.endpointCount (.inl (q : V)) ∧
        0 < E.endpointCount (.inl (r : V)) ∧
        0 < E.endpointCount (.inl h) := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, hDq, hDr, hDh, hDa⟩ :=
    bare_shortest_even_corridor_auxiliary_floor_with_odd_endpoints
      h x a H p hp hdist hclosest hadeg
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  letI : DecidableRel (corridorAuxiliary G W q r h).Adj := Classical.decRel _
  letI : ∀ n, DecidableRel
      (Decomposition.restorationChainGraph (corridorAuxiliary G W q r h)
        (fun j => (.inl (W.getVert j) : V ⊕ Unit)) n).Adj :=
    Decomposition.restorationChainGraphDecidableRel
      (fun j => (.inl (W.getVert j) : V ⊕ Unit))
  have hstart : 0 < D.endpointCount (.inl (W.getVert 0)) := by
    simpa only [W, shortestEvenCorridorLift_getVert, p.getVert_zero] using hDx
  obtain ⟨E, hEsize, hEend, hEledger⟩ :=
    Decomposition.restore_chain_of_zero_centres_with_endpoint_ledger D
    (fun j => (.inl (W.getVert j) : V ⊕ Unit)) (p.length - 1) hstart
    (by
      intro i hi hile he
      have hiend : i < W.length := by
        rw [hWlen]
        omega
      have hpred : i - 1 < W.length := by
        rw [hWlen]
        omega
      have hindex : i = i - 1 := hpath.getVert_injOn
        (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hiend)
        (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hpred)
        (Sum.inl.inj he)
      omega)
    (by
      intro i hi hile
      apply Decomposition.restorationChainGraph_not_adj_of_base
        (fun j => (.inl (W.getVert j) : V ⊕ Unit)) (i - 1)
        (.inl (W.getVert i)) (.inl (W.getVert (i - 1)))
      · exact corridorAuxiliary_not_adj_internal_previous G W i hi (by
          rw [hWlen]
          omega)
      · intro j hj he
        have hiend : i < W.length := by
          rw [hWlen]
          omega
        have hjend : j < W.length := by
          rw [hWlen]
          omega
        have hindex : i = j := hpath.getVert_injOn
          (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hiend)
          (by simp only [Set.mem_ofPred_eq]; exact Nat.le_of_lt hjend)
          (Sum.inl.inj he)
        omega)
    (by
      intro i hi hile
      apply bare_shortest_even_corridor_auxiliary_internal_zero_after_prefix
        h x a H p hp hdist hclosest hadeg q r hqa hra hqr hqoff hroff hhq hhr i hi
      omega)
  have hqprotected : ∀ j, j ≤ p.length - 1 →
      (.inl (q : V) : V ⊕ Unit) ≠ .inl (W.getVert j) := by
    intro j hj heq
    apply hqoff
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨j, (Sum.inl.inj heq).symm, by
        rw [hWlen]
        omega⟩
  have hrprotected : ∀ j, j ≤ p.length - 1 →
      (.inl (r : V) : V ⊕ Unit) ≠ .inl (W.getVert j) := by
    intro j hj heq
    apply hroff
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨j, (Sum.inl.inj heq).symm, by
        rw [hWlen]
        omega⟩
  have hhprotected : ∀ j, j ≤ p.length - 1 →
      (.inl h : V ⊕ Unit) ≠ .inl (W.getVert j) := by
    intro j hj heq
    apply bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨j, (Sum.inl.inj heq).symm, by
        rw [hWlen]
        omega⟩
  have haprotected : ∀ j, j ≤ p.length - 1 →
      (.inl (a : V) : V ⊕ Unit) ≠ .inl (W.getVert j) := by
    intro j hj heq
    have hja : W.getVert j = (a : V) := (Sum.inl.inj heq).symm
    have hterminal : W.getVert W.length = (a : V) := by
      rw [show W = shortestEvenCorridorLift p from rfl,
        shortestEvenCorridorLift_length,
        shortestEvenCorridorLift_getVert,
        p.getVert_length]
    have hjend : W.getVert j = W.getVert W.length := hja.trans hterminal.symm
    have hjlen : j = W.length := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.le_refl _)
      hjend
    rw [hWlen] at hjlen
    omega
  refine ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, ?_, ?_⟩
  · simpa only [W] using E
  · refine ⟨hEsize.le.trans hDsize, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [W] using hEend
    · rw [hEledger (.inl (a : V)) haprotected]
      exact hDa
    · rw [hEledger (.inl (q : V)) hqprotected]
      exact hDq
    · rw [hEledger (.inl (r : V)) hrprotected]
      exact hDr
    · rw [hEledger (.inl h) hhprotected]
      exact hDh

/- A nontrivial shortest corridor to an E-degree-three terminal is reducible.
The corridor prefix supplies one endpoint-consistent terminal auxiliary; the
three original even neighbours of its centre are then exhausted by cardinality
and the terminal shared-ledger consumer restores the remaining star. -/
set_option maxHeartbeats 5000000 in
theorem bare_hub_no_degree_three_of_nontrivial_corridor
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) : False := by
  classical
  rcases H.counterexample.1 with ⟨_, hhx, _, hh, hx, hbare, _⟩
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, E, hEsize,
    hEb, hEa, hEq, hEr, _⟩ :=
    bare_shortest_even_corridor_auxiliary_restore_internal_prefix
      h x a H p hp hdist hclosest hadeg
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  let b := W.getVert (p.length - 1)
  have hbmem : b ∈ W.support := by
    apply (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
    refine ⟨p.length - 1, rfl, ?_⟩
    rw [hWlen]
    omega
  have hba : G.Adj (a : V) b := by
    have hstep := W.adj_getVert_succ (i := p.length - 1) (by
      rw [hWlen]
      omega)
    have hlast : W.getVert (p.length - 1 + 1) = (a : V) := by
      rw [Nat.sub_add_cancel (by omega), show W = shortestEvenCorridorLift p from rfl,
        shortestEvenCorridorLift_getVert, p.getVert_length]
    rw [hlast] at hstep
    exact hstep.symm
  have hqG : G.Adj (a : V) (q : V) := hqa.symm
  have hrG : G.Adj (a : V) (r : V) := hra.symm
  have hbq : b ≠ (q : V) := by
    intro e
    apply hqoff
    rw [← e]
    exact hbmem
  have hbr : b ≠ (r : V) := by
    intro e
    apply hroff
    rw [← e]
    exact hbmem
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqx : (q : V) ≠ x := by
    intro e
    apply hqoff
    simpa only [e] using W.start_mem_support
  have hrx : (r : V) ≠ x := by
    intro e
    apply hroff
    simpa only [e] using W.start_mem_support
  have hha : h ≠ (a : V) := by
    intro e
    have hhadeg : eDegree G h = 3 := by simpa [e] using hadeg
    rw [hbare] at hhadeg
    omega
  have hcover : ∀ w, G.Adj (a : V) w → Even (G.degree w) →
      w = b ∨ w = q ∨ w = r := by
    let N : Finset V := evenNeighbors G (a : V)
    have hbN : b ∈ N :=
      (mem_evenNeighbors (G := G) (a : V) b).mpr ⟨hba, by
        apply shortestEvenCorridorLift_support_even p b hbmem⟩
    have hqN : (q : V) ∈ N :=
      (mem_evenNeighbors (G := G) (a : V) (q : V)).mpr ⟨hqG, q.property⟩
    have hrN : (r : V) ∈ N :=
      (mem_evenNeighbors (G := G) (a : V) (r : V)).mpr ⟨hrG, r.property⟩
    have hpair : ({b, (q : V), (r : V)} : Finset V) ⊆ N := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwb | hwq | hwr
      · simpa [hwb] using hbN
      · simpa [hwq] using hqN
      · simpa [hwr] using hrN
    have hN : ({b, (q : V), (r : V)} : Finset V) = N := by
      apply Finset.eq_of_subset_of_card_le hpair
      rw [show N.card = 3 by simpa [N, eDegree] using hadeg]
      simp [hbq, hbr, hqr']
    intro w haw hweven
    have hwN : w ∈ N := (mem_evenNeighbors (G := G) (a : V) w).mpr ⟨haw, hweven⟩
    rw [← hN] at hwN
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hwN
  have hgraph :
      Decomposition.restorationChainGraph (corridorAuxiliary G W q r h)
        (fun i => (.inl (W.getVert i) : V ⊕ Unit)) (p.length - 1) =
        lengthOneCorridorAuxiliary G h (a : V) b q r := by
    have hg := corridorAuxiliary_restore_prefix_eq_lengthOne
      (G := G) (h := h) W hpath (by rw [hWlen]; exact hlen2) hqoff hroff
    rw [hWlen] at hg
    exact hg
  let E0 : Decomposition
      (Decomposition.restorationChainGraph (corridorAuxiliary G W q r h)
        (fun i => (.inl (W.getVert i) : V ⊕ Unit)) (p.length - 1)) := by
    simpa only [W] using E
  let D : Decomposition (lengthOneCorridorAuxiliary G h (a : V) b q r) := hgraph ▸ E0
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) (v : V ⊕ Unit) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hDsize : D.size ≤ Fintype.card (V ⊕ Unit) / 2 := by
    change (hgraph ▸ E0).size ≤ _
    rw [castSize hgraph E0]
    simpa [E0, W] using hEsize
  have hDb : 0 < D.endpointCount (.inl b) := by
    change 0 < (hgraph ▸ E0).endpointCount (.inl b)
    rw [castEnds hgraph E0 (.inl b)]
    simpa [E0, b, W] using hEb
  have hDa : 0 < D.endpointCount (.inl (a : V)) := by
    change 0 < (hgraph ▸ E0).endpointCount (.inl (a : V))
    rw [castEnds hgraph E0 (.inl (a : V))]
    simpa [E0, W] using hEa
  have hDq : 0 < D.endpointCount (.inl (q : V)) := by
    change 0 < (hgraph ▸ E0).endpointCount (.inl (q : V))
    rw [castEnds hgraph E0 (.inl (q : V))]
    simpa [E0, W] using hEq
  have hDr : 0 < D.endpointCount (.inl (r : V)) := by
    change 0 < (hgraph ▸ E0).endpointCount (.inl (r : V))
    rw [castEnds hgraph E0 (.inl (r : V))]
    simpa [E0, W] using hEr
  obtain ⟨F, hFsize, hFends⟩ := bare_terminal_three_spoke_return_of_ledger
    h (x : V) (a : V) b (q : V) (r : V) H hba hqG hrG hbq hbr hqr'
    a.property q.property r.property hha hhq hhr hqx hrx hcover D hDb hDa hDq hDr
  apply H.counterexample.2
  refine ⟨F, ?_, hFends⟩
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_zero] using
    hFsize.trans hDsize

/-- A degree-three even vertex in the even-subgraph component of the bare
exceptional hub yields a closest terminal, and the completed corridor
contradiction excludes that terminal.  The minimization is deliberately
restricted to the reachable component: vertices in another component have
metric distance zero in the extended-distance convention and are irrelevant
to this corridor argument. -/
theorem bare_hub_component_no_degree_three
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (hexists : ∃ a : evenVertices G, (evenSubgraph G).Reachable x a ∧
      eDegree G (a : V) = 3) : False := by
  classical
  let S : Set (evenVertices G) := {z | (evenSubgraph G).Reachable x z ∧
    eDegree G (z : V) = 3}
  obtain ⟨a₀, ha₀reach, ha₀degree⟩ := hexists
  have hS : S.Nonempty := ⟨a₀, ha₀reach, ha₀degree⟩
  let a : evenVertices G := Function.argminOn
    (fun z : evenVertices G => (evenSubgraph G).dist x z) S hS
  have haS : a ∈ S := Function.argminOn_mem _ _ _
  have hareach : (evenSubgraph G).Reachable x a := haS.1
  have hadegree : eDegree G (a : V) = 3 := haS.2
  obtain ⟨p, hp, hdist⟩ := hareach.exists_path_of_dist
  have hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z := by
    intro z hz hdegree
    exact Function.argminOn_le _ S ⟨hz, hdegree⟩
  exact bare_hub_no_degree_three_of_nontrivial_corridor h x a H p hp hdist hclosest hadegree

/-- The selected nontrivial-corridor floor witness can retain its own terminal
leaves while also recording the second internal centre's E-degree-zero fact.
Keeping this shared selection explicit is essential for a later sequential
restoration: independently chosen existential leaves cannot be composed. -/
theorem bare_shortest_even_corridor_auxiliary_floor_with_second_internal_zero
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) (hlen3 : 2 < p.length) :
    ∃ q r : evenVertices G,
      (evenSubgraph G).Adj q a ∧ (evenSubgraph G).Adj r a ∧ q ≠ r ∧
      (q : V) ∉ (shortestEvenCorridorLift p).support ∧
      (r : V) ∉ (shortestEvenCorridorLift p).support ∧
      (h : V) ≠ q ∧ (h : V) ≠ r ∧
      ∃ D : Decomposition (corridorAuxiliary G (shortestEvenCorridorLift p) q r h),
        D.size ≤ Fintype.card (V ⊕ Unit) / 2 ∧
        0 < D.endpointCount (.inl (x : V)) ∧
        0 < D.endpointCount (.inl (q : V)) ∧
        0 < D.endpointCount (.inl (r : V)) ∧
        0 < D.endpointCount (.inl h) ∧
        0 < D.endpointCount (.inl (a : V)) ∧
        eDegree (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
          (.inl ((shortestEvenCorridorLift p).getVert 1)) = 0 ∧
        eDegree (corridorAuxiliary G (shortestEvenCorridorLift p) q r h)
          (.inl ((shortestEvenCorridorLift p).getVert 2)) = 0 := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, hDq, hDr, hDh, hDa⟩ :=
    bare_shortest_even_corridor_auxiliary_floor_with_odd_endpoints
      h x a H p hp hdist hclosest hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hi1 : 0 < (1 : ℕ) := by omega
  have hi2 : 0 < (2 : ℕ) := by omega
  have hi1end : 1 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hi2end : 2 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    exact hlen3
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hdegree1 := shortest_even_corridor_internal_eDegree_eq_two_of_bare
    h x a H p hp hdist hclosest 1 hi1
    (by simpa only [shortestEvenCorridorLift_length] using hi1end)
  have hdegree1' : eDegree G ((shortestEvenCorridorLift p).getVert 1) = 2 := by
    simpa only [shortestEvenCorridorLift_getVert] using hdegree1
  have hdegree := shortest_even_corridor_internal_eDegree_eq_two_of_bare
    h x a H p hp hdist hclosest 2 hi2
    (by simpa only [shortestEvenCorridorLift_length] using hi2end)
  have hdegree' : eDegree G ((shortestEvenCorridorLift p).getVert 2) = 2 := by
    simpa only [shortestEvenCorridorLift_getVert] using hdegree
  have hzh : (shortestEvenCorridorLift p).getVert 2 ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨2, rfl, Nat.le_of_lt hi2end⟩
  have hzh1 : (shortestEvenCorridorLift p).getVert 1 ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨1, rfl, Nat.le_of_lt hi1end⟩
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  have haq : G.Adj (a : V) q := hqa.symm
  have har : G.Adj (a : V) r := hra.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hzero1 := corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
    (shortestEvenCorridorLift p) hpath 1 hi1 hi1end
    (fun w hw => shortestEvenCorridorLift_support_even p w hw)
    hqoff hroff hhoff hqr' hqh hrh haq har q.property r.property
    (H.counterexample.1).2.2.2.1 hzh1 hdegree1'
  have hzero := corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
    (shortestEvenCorridorLift p) hpath 2 hi2 hi2end
    (fun w hw => shortestEvenCorridorLift_support_even p w hw)
    hqoff hroff hhoff hqr' hqh hrh haq har q.property r.property
    (H.counterexample.1).2.2.2.1 hzh hdegree'
  exact ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, hDq, hDr, hDh, hDa, hzero1, hzero⟩

/-- The first missing edge of a nontrivial shortest even corridor restores at
unchanged path count.  The floor witness supplies an endpoint at the start;
the first internal corridor vertex has auxiliary E-degree zero, so every one
of its current neighbours is already endpoint-positive.  This is the first
actual restoration step, not a conditional strict-addibility interface. -/
theorem bare_shortest_even_corridor_auxiliary_restore_first_edge
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) :
    ∃ q r : evenVertices G,
      ∃ E : Decomposition
        ((corridorAuxiliary G (shortestEvenCorridorLift p) q r h) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 1))
            (.inl ((shortestEvenCorridorLift p).getVert 0))),
        E.size ≤ Fintype.card (V ⊕ Unit) / 2 := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, _, _, _, _⟩ :=
    bare_shortest_even_corridor_auxiliary_floor_with_odd_endpoints
      h x a H p hp hdist hclosest hadeg
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hlen2 := bare_shortest_even_corridor_length_ge_two h x a H p hdist hadeg
  have hi : 0 < (1 : ℕ) := by omega
  have hiend : 1 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    exact hlen2
  have hhoff := bare_prescribed_not_mem_shortest_even_corridor_support h x a H p hadeg
  have hdegree := shortest_even_corridor_internal_eDegree_eq_two_of_bare
    h x a H p hp hdist hclosest 1 hi (by simpa only [shortestEvenCorridorLift_length] using hiend)
  have hdegree' : eDegree G ((shortestEvenCorridorLift p).getVert 1) = 2 := by
    simpa only [shortestEvenCorridorLift_getVert] using hdegree
  have hzh : (shortestEvenCorridorLift p).getVert 1 ≠ h := by
    intro e
    apply hhoff
    rw [← e]
    exact (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨1, rfl, Nat.le_of_lt hiend⟩
  have hqr' : (q : V) ≠ r := fun e => hqr (Subtype.ext e)
  have hqh : (q : V) ≠ h := fun e => hhq e.symm
  have hrh : (r : V) ≠ h := fun e => hhr e.symm
  have haq : G.Adj (a : V) q := hqa.symm
  have har : G.Adj (a : V) r := hra.symm
  letI : DecidableRel (walkPuncture G (shortestEvenCorridorLift p)).Adj := Classical.decRel _
  letI : DecidableRel (corridorPuncture G (shortestEvenCorridorLift p) q r).Adj :=
    Classical.decRel _
  have hzero := corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data G
    (shortestEvenCorridorLift p) hpath 1 hi hiend
    (fun w hw => shortestEvenCorridorLift_support_even p w hw)
    hqoff hroff hhoff hqr' hqh hrh haq har q.property r.property
    (H.counterexample.1).2.2.2.1 hzh hdegree'
  have hDstart : 0 < D.endpointCount (.inl ((shortestEvenCorridorLift p).getVert 0)) := by
    simpa only [shortestEvenCorridorLift_getVert, p.getVert_zero] using hDx
  obtain ⟨E, hEsize, _⟩ := D.restore_corridor_internal_previous
    (shortestEvenCorridorLift p) hpath 1 hi hiend hzero hDstart
  exact ⟨q, r, E, hEsize.le.trans hDsize⟩

/-- After the first corridor edge is restored, the old start vertex is the
only newly even endpoint that could enter the next centre's even
neighbourhood.  A shortest corridor has no such start-to-later chord, and
this is the auxiliary-typed form used by the second restoration step. -/
theorem bare_shortest_even_corridor_auxiliary_start_not_adj_later
    (h : V) (x a : evenVertices G) (p : (evenSubgraph G).Walk x a)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (q r : evenVertices G) (j : ℕ) (hj : 1 < j) (hjle : j ≤ p.length) :
    ¬ (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).Adj
      (.inl ((shortestEvenCorridorLift p).getVert 0))
      (.inl ((shortestEvenCorridorLift p).getVert j)) := by
  intro hadj
  have horig := (corridorAuxiliary_adj_old_iff G (shortestEvenCorridorLift p)).mp hadj |>.1
  apply shortest_even_corridor_start_not_adj_getVert x a p hdist j hj hjle
  change G.Adj (x : V) ((p.getVert j : evenVertices G) : V)
  simpa only [shortestEvenCorridorLift_getVert, p.getVert_zero] using horig

/-- In the length-at-least-three shortest-corridor branch, the first two
deleted corridor edges restore at the floor budget.  The proof is the direct
consumer of the shared q/r floor witness and the abstract two-centre
restoration theorem. -/
theorem bare_shortest_even_corridor_auxiliary_restore_first_two_edges
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) (hlen3 : 2 < p.length) :
    ∃ q r : evenVertices G,
      ∃ F : Decomposition
        (((corridorAuxiliary G (shortestEvenCorridorLift p) q r h) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 1))
            (.inl ((shortestEvenCorridorLift p).getVert 0))) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 2))
            (.inl ((shortestEvenCorridorLift p).getVert 1))),
        F.size ≤ Fintype.card (V ⊕ Unit) / 2 := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, _, _, _, _, hzero1, hzero2⟩ :=
    bare_shortest_even_corridor_auxiliary_floor_with_second_internal_zero
      h x a H p hp hdist hclosest hadeg hlen3
  have hpath := shortestEvenCorridorLift_isPath p hp
  have hi1 : 0 < (1 : ℕ) := by omega
  have hi2 : 0 < (2 : ℕ) := by omega
  have hi1end : 1 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    omega
  have hi2end : 2 < (shortestEvenCorridorLift p).length := by
    rw [shortestEvenCorridorLift_length]
    exact hlen3
  have hne10 : (shortestEvenCorridorLift p).getVert 1 ≠
      (shortestEvenCorridorLift p).getVert 0 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) he
    omega
  have hne21 : (shortestEvenCorridorLift p).getVert 2 ≠
      (shortestEvenCorridorLift p).getVert 1 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) he
    omega
  have hne20 : (shortestEvenCorridorLift p).getVert 2 ≠
      (shortestEvenCorridorLift p).getVert 0 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) he
    omega
  have hDstart : 0 < D.endpointCount (.inl ((shortestEvenCorridorLift p).getVert 0)) := by
    simpa only [shortestEvenCorridorLift_getVert, p.getVert_zero] using hDx
  have hmissing1 : ¬ (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).Adj
      (.inl ((shortestEvenCorridorLift p).getVert 1))
      (.inl ((shortestEvenCorridorLift p).getVert 0)) :=
    corridorAuxiliary_not_adj_internal_previous G (shortestEvenCorridorLift p) 1 hi1 hi1end
  have hno21 : ¬ (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).Adj
      (.inl ((shortestEvenCorridorLift p).getVert 2))
      (.inl ((shortestEvenCorridorLift p).getVert 1)) :=
    corridorAuxiliary_not_adj_internal_previous G (shortestEvenCorridorLift p) 2 hi2 hi2end
  have hno20 : ¬ (corridorAuxiliary G (shortestEvenCorridorLift p) q r h).Adj
      (.inl ((shortestEvenCorridorLift p).getVert 2))
      (.inl ((shortestEvenCorridorLift p).getVert 0)) := by
    intro hadj
    apply bare_shortest_even_corridor_auxiliary_start_not_adj_later h x a p hdist q r 2
      (by omega) (by omega)
    exact hadj.symm
  obtain ⟨F, hFsize⟩ := D.two_edge_restore_of_zero_centres
    (.inl ((shortestEvenCorridorLift p).getVert 0))
    (.inl ((shortestEvenCorridorLift p).getVert 1))
    (.inl ((shortestEvenCorridorLift p).getVert 2))
    (by intro e; exact hne10 (Sum.inl.inj e))
    (by intro e; exact hne21 (Sum.inl.inj e))
    (by intro e; exact hne20 (Sum.inl.inj e))
    hmissing1 hzero1 hDstart hzero2 hno21 hno20
  exact ⟨q, r, F, hFsize.le.trans hDsize⟩

/-- In the length-at-least-four shortest-corridor branch, the first three
deleted corridor edges restore at the floor budget.  The three-edge consumer
keeps the original terminal-leaf choice fixed, and the geodesic no-chord
lemma supplies the new separation from both earlier restored positions. -/
theorem bare_shortest_even_corridor_auxiliary_restore_first_three_edges
    (h : V) (x a : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (p : (evenSubgraph G).Walk x a) (hp : p.IsPath)
    (hdist : p.length = (evenSubgraph G).dist x a)
    (hclosest : ∀ z : evenVertices G, (evenSubgraph G).Reachable x z →
      eDegree G (z : V) = 3 →
      (evenSubgraph G).dist x a ≤ (evenSubgraph G).dist x z)
    (hadeg : eDegree G (a : V) = 3) (hlen4 : 3 < p.length) :
    ∃ q r : evenVertices G,
      ∃ K : Decomposition
        ((((corridorAuxiliary G (shortestEvenCorridorLift p) q r h) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 1))
            (.inl ((shortestEvenCorridorLift p).getVert 0))) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 2))
            (.inl ((shortestEvenCorridorLift p).getVert 1))) ⊔
          SimpleGraph.edge (.inl ((shortestEvenCorridorLift p).getVert 3))
            (.inl ((shortestEvenCorridorLift p).getVert 2))),
        K.size ≤ Fintype.card (V ⊕ Unit) / 2 := by
  obtain ⟨q, r, hqa, hra, hqr, hqoff, hroff, hhq, hhr, D, hDsize,
    hDx, _, _, _, _⟩ :=
    bare_shortest_even_corridor_auxiliary_floor_with_odd_endpoints
      h x a H p hp hdist hclosest hadeg
  let W := shortestEvenCorridorLift p
  have hpath : W.IsPath := shortestEvenCorridorLift_isPath p hp
  have hWlen : W.length = p.length := by
    simp only [W, shortestEvenCorridorLift_length]
  have hi1 : 0 < (1 : ℕ) := by omega
  have hi2 : 0 < (2 : ℕ) := by omega
  have hi3 : 0 < (3 : ℕ) := by omega
  have hi1end : 1 < p.length := by omega
  have hi2end : 2 < p.length := by omega
  have hi3end : 3 < p.length := hlen4
  have hzero1 := bare_shortest_even_corridor_auxiliary_internal_zero_of_selected
    h x a H p hp hdist hclosest hadeg q r hqa hra hqr hqoff hroff hhq hhr
    1 hi1 hi1end
  have hzero2 := bare_shortest_even_corridor_auxiliary_internal_zero_of_selected
    h x a H p hp hdist hclosest hadeg q r hqa hra hqr hqoff hroff hhq hhr
    2 hi2 hi2end
  have hzero3 := bare_shortest_even_corridor_auxiliary_internal_zero_of_selected
    h x a H p hp hdist hclosest hadeg q r hqa hra hqr hqoff hroff hhq hhr
    3 hi3 hi3end
  have hne10 : W.getVert 1 ≠ W.getVert 0 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) he
    omega
  have hne21 : W.getVert 2 ≠ W.getVert 1 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega) he
    omega
  have hne20 : W.getVert 2 ≠ W.getVert 0 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) he
    omega
  have hne32 : W.getVert 3 ≠ W.getVert 2 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega) he
    omega
  have hne31 : W.getVert 3 ≠ W.getVert 1 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega) he
    omega
  have hne30 : W.getVert 3 ≠ W.getVert 0 := by
    intro he
    have hindex := hpath.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; rw [hWlen]; omega)
      (by simp only [Set.mem_ofPred_eq]; exact Nat.zero_le _) he
    omega
  have hDstart : 0 < D.endpointCount (.inl (W.getVert 0)) := by
    simpa only [W, shortestEvenCorridorLift_getVert, p.getVert_zero] using hDx
  have hmissing1 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 1)) (.inl (W.getVert 0)) :=
    corridorAuxiliary_not_adj_internal_previous G W 1 hi1 (by
      simpa only [W, shortestEvenCorridorLift_length] using hi1end)
  have hno21 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 2)) (.inl (W.getVert 1)) :=
    corridorAuxiliary_not_adj_internal_previous G W 2 hi2 (by
      simpa only [W, shortestEvenCorridorLift_length] using hi2end)
  have hno20 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 2)) (.inl (W.getVert 0)) := by
    intro hadj
    apply bare_shortest_even_corridor_auxiliary_start_not_adj_later h x a p hdist q r 2
      (by omega) (by omega)
    simpa only [W] using hadj.symm
  have hno32 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 3)) (.inl (W.getVert 2)) :=
    corridorAuxiliary_not_adj_internal_previous G W 3 hi3 (by
      simpa only [W, shortestEvenCorridorLift_length] using hi3end)
  have hno31 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 3)) (.inl (W.getVert 1)) := by
    intro hadj
    have horig := (corridorAuxiliary_adj_old_iff G W).mp hadj |>.1
    apply shortest_even_corridor_not_adj_getVert x a p hdist 1 3 (by omega) (by omega)
    change G.Adj ((p.getVert 1 : evenVertices G) : V) ((p.getVert 3 : evenVertices G) : V)
    simpa only [W, shortestEvenCorridorLift_getVert] using horig.symm
  have hno30 : ¬ (corridorAuxiliary G W q r h).Adj
      (.inl (W.getVert 3)) (.inl (W.getVert 0)) := by
    intro hadj
    apply bare_shortest_even_corridor_auxiliary_start_not_adj_later h x a p hdist q r 3
      (by omega) (by omega)
    simpa only [W] using hadj.symm
  obtain ⟨K, hKsize⟩ := D.three_edge_restore_of_zero_centres
    (.inl (W.getVert 0)) (.inl (W.getVert 1)) (.inl (W.getVert 2)) (.inl (W.getVert 3))
    (by intro e; exact hne10 (Sum.inl.inj e))
    (by intro e; exact hne21 (Sum.inl.inj e))
    (by intro e; exact hne20 (Sum.inl.inj e))
    (by intro e; exact hne32 (Sum.inl.inj e))
    (by intro e; exact hne31 (Sum.inl.inj e))
    (by intro e; exact hne30 (Sum.inl.inj e))
    (by simpa only [W] using hmissing1)
    (by simpa only [W] using hzero1) hDstart
    (by simpa only [W] using hzero2)
    (by simpa only [W] using hno21)
    (by simpa only [W] using hno20)
    (by simpa only [W] using hzero3)
    (by simpa only [W] using hno32)
    (by simpa only [W] using hno31)
    (by simpa only [W] using hno30)
  exact ⟨q, r, K, hKsize.le.trans hDsize⟩

end Gallai.TwoException
