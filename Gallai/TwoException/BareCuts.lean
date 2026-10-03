/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.OneExceptionPieces
public import Gallai.Structure.CutVertexPieces
public import Gallai.TwoException.BareMinimality
public import Gallai.Operations.AttachedMerge
public import Gallai.TwoException.SimultaneousEndpoint

@[expose] public section

/-!
# Cap transport at a bare two-exception cut

The one-exception cut API is deliberately insufficient here: B0 permits a
second large even hub.  These lemmas transport exactly the cap away from both
designated vertices to an actual induced cut side.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]

/-- A one-carrier merge at a prospective bare vertex preserves its required
two-endpoint reserve exactly when the two input endpoint supplies total at
least four.  This is the accounting interface for the exceptional-cut branch:
the merge saves the one path needed by the cut budget and consumes precisely
two endpoints at its joint. -/
theorem single_merge_preserves_joint_reserve
    (D : Decomposition A) (E : Decomposition B) (z : V)
    (hD : 0 < D.endpointCount z) (hE : 0 < E.endpointCount z)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hsupply : 4 ≤ D.endpointCount z + E.endpointCount z) :
    ∃ F : Decomposition (A ⊔ B), F.size + 1 = D.size + E.size ∧
      2 ≤ F.endpointCount z := by
  obtain ⟨F, hFsize, hFends⟩ := D.single_merge_endpoints E z hD hE hmeet
  refine ⟨F, hFsize, ?_⟩
  have hends := hFends z
  simp at hends
  omega

/-- For two decompositions meeting at a vertex of odd local degree on both
sides, the only way that one-carrier gluing can fail to preserve a two-endpoint
reserve is the exact `1 + 1` endpoint profile.  This is a parity consequence,
not an additional decomposition-selection assumption. -/
theorem odd_joint_supply_or_one_one
    (D : Decomposition A) (E : Decomposition B) (z : V)
    (hDodd : Odd (A.degree z)) (hEodd : Odd (B.degree z)) :
    (D.endpointCount z = 1 ∧ E.endpointCount z = 1) ∨
      4 ≤ D.endpointCount z + E.endpointCount z := by
  by_cases hsupply : 4 ≤ D.endpointCount z + E.endpointCount z
  · exact Or.inr hsupply
  · left
    have hDpos := D.endpointCount_pos_of_odd_degree z hDodd
    have hEpos := E.endpointCount_pos_of_odd_degree z hEodd
    have hDparity := D.endpointCount_mod_two z
    have hEparity := E.endpointCount_mod_two z
    rcases hDodd with ⟨a, ha⟩
    rcases hEodd with ⟨b, hb⟩
    constructor <;> omega

/-- A connected subcubic-even side has a ceiling-budget decomposition exposing
any specified odd vertex.  In the Gallai branch this is endpoint parity; in
the SET branch it is the published SET endpoint-reserve construction.  This
is the literal side interface used when the actual exceptional hub is odd on
both sides of a cut. -/
theorem floor_or_set_ceiling_endpoint_of_odd
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V)
    (hconn : G.Connected)
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3)
    (hzOdd : Odd (G.degree z)) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      0 < D.endpointCount z := by
  rcases floor_or_set G hconn hcap with ⟨D, hD⟩ | hset
  · exact ⟨D, by omega, D.endpointCount_pos_of_odd_degree z hzOdd⟩
  · obtain ⟨D, hD, hzD⟩ := hset.endpoint_reserve z
    exact ⟨D, hD, by omega⟩

/-- A side of a union at an even separator inherits the subcubic E-degree cap
away from *both* designated hubs. -/
theorem bare_cap_right (z h x : V)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ x →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v, Even (B.degree v) → v ≠ h → v ≠ x → eDegree B v ≤ 3 := by
  intro v hv hvh hvx
  by_cases hp : ∃ w, B.Adj v w
  · exact (eDegree_le_one_vertex_union A B z v hmeet (Or.inl hz)).trans
      (hcap v (even_positive_in_one_vertex_union A B z v hmeet (Or.inl hz) hv hp)
        hvh hvx)
  · have hn : B.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hd : B.degree v = 0 := by
      rw [← B.card_neighborFinset_eq_degree, hn, Finset.card_empty]
    have he := eDegree_le_degree (G := B) v
    omega

/-- The left-hand analogue of the one-vertex even-neighbour inclusion.  It is
proved directly rather than by rewriting `A ⊔ B` to `B ⊔ A`, because degree
and E-degree carry graph-indexed decidability instances. -/
theorem evenNeighbors_subset_left_one_vertex_union (z v : V)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z) :
    evenNeighbors A v ⊆ evenNeighbors (A ⊔ B) v := by
  intro w hw
  obtain ⟨hvw, hwEven⟩ := (mem_evenNeighbors v w).mp hw
  refine (mem_evenNeighbors v w).mpr ⟨Or.inl hvw, ?_⟩
  by_cases hwz : w = z
  · subst w
    exact hz
  · have hBiso : ∀ q, ¬ B.Adj w q := by
      intro q hwq
      exact hwz (hmeet w ⟨v, hvw.symm⟩ ⟨q, hwq⟩)
    have hzero : B.neighborFinset w = ∅ := by
      ext q
      simp [hBiso q]
    have hdeg : (A ⊔ B).degree w = A.degree w := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
        hzero]
      simp
    rw [hdeg]
    exact hwEven

/-- A left side of a one-vertex union inherits the cap away from both
designated hubs.  This is intentionally a direct proof: `sup_comm` cannot be
used as a dependent rewrite through `eDegree`. -/
theorem bare_cap_left (z h x : V)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ x →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v, Even (A.degree v) → v ≠ h → v ≠ x → eDegree A v ≤ 3 := by
  intro v hv hvh hvx
  by_cases hp : ∃ w, A.Adj v w
  · have hEven : Even ((A ⊔ B).degree v) := by
      rcases hp with ⟨w, hvw⟩
      by_cases hvz : v = z
      · subst v
        exact hz
      · have hBiso : ∀ q, ¬ B.Adj v q := by
          intro q hvq
          exact hvz (hmeet v ⟨w, hvw⟩ ⟨q, hvq⟩)
        have hzero : B.neighborFinset v = ∅ := by
          ext q
          simp [hBiso q]
        have hdeg : (A ⊔ B).degree v = A.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree,
            SimpleGraph.neighborFinset_sup, hzero]
          simp
        rw [hdeg]
        exact hv
    exact (Finset.card_le_card
      (evenNeighbors_subset_left_one_vertex_union A B z v hz hmeet)).trans
      (hcap v hEven hvh hvx)
  · have hzero : A.neighborFinset v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hw => hp ⟨w, hw⟩
    have hdeg : A.degree v = 0 := by
      rw [← A.card_neighborFinset_eq_degree, hzero, Finset.card_empty]
    have hle := eDegree_le_degree (G := A) v
    omega

/-- The actual subtype graph of a cut side retains the same two-exception
cap.  The hub labels stay ambient, preventing an accidental one-exception
specialization at the opposite side. -/
theorem bare_cap_induced_right (S : Set V) [DecidablePred (· ∈ S)]
    (z h x : V) (hs : B.support ⊆ S)
    (hz : Even ((A ⊔ B).degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z)
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ x →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v : S, Even ((B.induce S).degree v) → v.val ≠ h → v.val ≠ x →
      eDegree (B.induce S) v ≤ 3 := by
  intro v hv hvh hvx
  rw [eDegree_induce_of_support_subset B S hs v]
  apply bare_cap_right A B z h x hz hmeet hcap v.val ?_ hvh hvx
  rwa [SimpleGraph.degree_induce_of_support_subset hs v] at hv

/-- Map a decomposition of an actual induced piece back to its ambient piece.
The support condition is the exact reason this is an equality rather than a
spanning supergraph construction. -/
private theorem lift_cut_piece {H : SimpleGraph V} (S : Set V)
    (hs : H.support ⊆ S) (D : Decomposition (H.induce S)) :
    ∃ E : Decomposition H, E.size = D.size ∧
      ∀ w : S, E.endpointCount w.val = D.endpointCount w := by
  have hgraph : (H.induce S).map (Function.Embedding.subtype _) = H :=
    (H.spanningCoe_induce_eq_self S).mpr hs
  have hout : ∃ E : Decomposition ((H.induce S).map (Function.Embedding.subtype _)),
      E.size = D.size ∧ ∀ w : S, E.endpointCount w.val = D.endpointCount w :=
    ⟨D.map (Function.Embedding.subtype _), rfl,
      fun w => D.map_endpointCount (Function.Embedding.subtype _) w⟩
  rwa [hgraph] at hout

/-- The odd-local branch for an actual cut at the exceptional vertex of a
bare B0 instance. The `h` side receives the one-exception endpoint theorem;
the other side is fully subcubic because the cut vertex is odd there, so the
floor-or-SET odd-joint interface supplies its merger endpoint. -/
theorem bare_exception_cut_odd_assembly
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (H : BareCounterexample (A ⊔ B) h x)
    (hxS : x ∈ S) (hxT : x ∈ T) (hhS : h ∈ S) (hhx : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hxOddA : Odd (A.degree x)) :
    ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
  rcases H with ⟨⟨hconn, hne, hhpos, hhEven, hxEven, hbare, hcap⟩, hfail⟩
  have hhT : h ∉ T := by
    intro hhT
    have hmem : h ∈ S ∩ T := ⟨hhS, hhT⟩
    have : h = x := by simpa only [hinter, Set.mem_singleton_iff] using hmem
    exact hhx this
  have hBiso : ∀ w, ¬ B.Adj h w := fun w hw => hhT (hB ⟨w, hw⟩)
  have hhdeg : (A ⊔ B).degree h = A.degree h := by
    have hzero : B.neighborFinset h = ∅ := by
      ext w
      simp [hBiso w]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      hzero]
    simp
  have hhposA : 0 < (A.induce S).degree ⟨h, hhS⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhpos
  have hhEvenA : Even ((A.induce S).degree ⟨h, hhS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhEven
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = x := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hdis : Disjoint (A.neighborFinset x) (B.neighborFinset x) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset x w).mp ha
    have hb' := (B.mem_neighborFinset x w).mp hb
    exact ha'.ne (hmeet w ⟨x, ha'.symm⟩ ⟨x, hb'.symm⟩).symm
  have hxdeg : (A ⊔ B).degree x = A.degree x + B.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hxOddB : Odd (B.degree x) := by
    rw [Nat.even_iff, hxdeg] at hxEven
    rw [Nat.odd_iff] at hxOddA ⊢
    omega
  have hxOddAS : Odd ((A.induce S).degree ⟨x, hxS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hxOddA
  have hxOddBS : Odd ((B.induce T).degree ⟨x, hxT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hxOddB
  have hcapA0 := bare_cap_left A B x h x hxEven hmeet hcap
  have hcapB0 := bare_cap_induced_right A B T x h x hB hxEven hmeet hcap
  have hcapAS : ∀ v : S, Even ((A.induce S).degree v) →
      v ≠ ⟨h, hhS⟩ → eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA0 v.val hvA
    · intro hval
      exact hvh (Subtype.ext hval)
    · intro hval
      have heq : v = ⟨x, hxS⟩ := Subtype.ext hval
      rw [heq] at hv
      exact (Nat.not_even_iff_odd.mpr hxOddAS) hv
  have hcapBS : ∀ v : T, Even ((B.induce T).degree v) →
      eDegree (B.induce T) v ≤ 3 := by
    intro v hv
    apply hcapB0 v hv
    · intro hval
      exact hhT (hval ▸ v.property)
    · intro hval
      have heq : v = ⟨x, hxT⟩ := Subtype.ext hval
      rw [heq] at hv
      exact (Nat.not_even_iff_odd.mpr hxOddBS) hv
  obtain ⟨D0, hD0size, hhD0⟩ := one_exception_endpoint (A.induce S) ⟨h, hhS⟩
    hconnA hhposA hhEvenA hcapAS
  obtain ⟨E0, hE0size, hxE0⟩ := floor_or_set_ceiling_endpoint_of_odd
    (B.induce T) ⟨x, hxT⟩ hconnB hcapBS hxOddBS
  obtain ⟨D, hDsize, hDends⟩ := lift_cut_piece S hA D0
  obtain ⟨E, hEsize, hEends⟩ := lift_cut_piece T hB E0
  have hxD : 0 < D.endpointCount x := by
    rw [hDends ⟨x, hxS⟩]
    exact D0.endpointCount_pos_of_odd_degree ⟨x, hxS⟩ hxOddAS
  have hxE : 0 < E.endpointCount x := by
    rw [hEends ⟨x, hxT⟩]
    exact hxE0
  obtain ⟨F, hFsize, hFends⟩ := D.single_merge_endpoints E x hxD hxE hmeet
  refine ⟨F, ?_, ?_⟩
  · have hcard := card_cover_single_inter S T x hcover hinter
    have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
      (Fintype.card V) hcard
    have hAcard : D.size ≤ (Fintype.card S + 1) / 2 := by omega
    have hBcard : E.size ≤ (Fintype.card T + 1) / 2 := by omega
    omega
  · have hhD : 2 ≤ D.endpointCount h := by
      rw [hDends ⟨h, hhS⟩]
      exact hhD0
    have hhF := hFends h
    have hxh : x ≠ h := hhx.symm
    simp only [hxh, if_false, mul_zero, Nat.add_zero] at hhF
    omega

/-- In the normal form of a B0 cut at the exceptional hub, the local degree
on the side containing the bare prescribed vertex is even. The odd branch is
the preceding literal assembly and therefore contradicts bare failure. -/
theorem bare_exception_cut_h_side_even
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (H : BareCounterexample (A ⊔ B) h x)
    (hxS : x ∈ S) (hxT : x ∈ T) (hhS : h ∈ S) (hhx : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected) :
    Even (A.degree x) := by
  apply Nat.not_odd_iff_even.mp
  intro hxOdd
  obtain ⟨F, hF, hhF⟩ := bare_exception_cut_odd_assembly A B S T h x H
    hxS hxT hhS hhx hcover hinter hA hB hconnA hconnB hxOdd
  exact H.2 ⟨F, hF, hhF⟩

/-- The even-local exceptional-cut assembly after the h-side has been
discharged by relative B0 minimality.  The opposite side is now a literal
one-exception instance designated at `x`; its two-endpoint reserve absorbs an
incident h-side carrier at `x`, saving the one path required by the cut
budget while leaving the prescribed h-endpoint count unchanged. -/
theorem bare_exception_cut_even_assembly_of_bare
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (H : BareCounterexample (A ⊔ B) h x)
    (hxS : x ∈ S) (hxT : x ∈ T) (hhS : h ∈ S) (hhx : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {x})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnB : (B.induce T).Connected) (hxEvenB : Even (B.degree x))
    (hincA : ∃ q, A.Adj x q) (hincB : ∃ q, B.Adj x q)
    (hbareA : BareConclusion (A.induce S) ⟨h, hhS⟩) :
    ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
  rcases H with ⟨⟨hconn, hne, hhpos, hhEven, hxEven, hbare, hcap⟩, hfail⟩
  have hhT : h ∉ T := by
    intro hhT
    have hmem : h ∈ S ∩ T := ⟨hhS, hhT⟩
    have : h = x := by simpa only [hinter, Set.mem_singleton_iff] using hmem
    exact hhx this
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = x := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hxEvenBT : Even ((B.induce T).degree ⟨x, hxT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hxEvenB
  have hxposBT : 0 < (B.induce T).degree ⟨x, hxT⟩ := by
    obtain ⟨q, hq⟩ := hincB
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact (B.degree_pos_iff_exists_adj x).mpr ⟨q, hq⟩
  have hcapB0 := bare_cap_induced_right A B T x h x hB hxEven hmeet hcap
  have hcapBT : ∀ v : T, Even ((B.induce T).degree v) →
      v ≠ ⟨x, hxT⟩ → eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx
    apply hcapB0 v hv
    · intro hval
      exact hhT (hval ▸ v.property)
    · intro hval
      exact hvx (Subtype.ext hval)
  obtain ⟨D0, hD0size, hhD0⟩ := hbareA
  obtain ⟨E0, hE0size, hxE0⟩ := one_exception_endpoint (B.induce T) ⟨x, hxT⟩
    hconnB hxposBT hxEvenBT hcapBT
  obtain ⟨D, hDsize, hDends⟩ := lift_cut_piece S hA D0
  obtain ⟨E, hEsize, hEends⟩ := lift_cut_piece T hB E0
  have hxE : 2 ≤ E.endpointCount x := by
    rw [hEends ⟨x, hxT⟩]
    exact hxE0
  obtain ⟨F0, hF0size, hF0ends⟩ := E.glue_at_exposed_vertex D x hxE hincA
    (fun w hwB hwA => hmeet w hwA hwB)
  have hgraph : B ⊔ A = A ⊔ B := by simpa only [sup_comm]
  have hcard := card_cover_single_inter S T x hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  have hAcard : D.size ≤ (Fintype.card S + 1) / 2 := by omega
  have hBcard : E.size ≤ (Fintype.card T + 1) / 2 := by omega
  have hhD : 2 ≤ D.endpointCount h := by
    rw [hDends ⟨h, hhS⟩]
    exact hhD0
  have hhF0 := hF0ends h
  have hxh : x ≠ h := hhx.symm
  simp only [hxh, if_false, mul_zero, Nat.add_zero] at hhF0
  rw [← hgraph]
  exact ⟨F0, by omega, by omega⟩

/-- The h-side of an exceptional cut is itself a literal bare instance once
its local degree at `x` is even.  This packages all graph-indexed degree and
E-degree transport needed before relative B0 minimality may be invoked; it
does not assert the strict cardinality decrease of an actual cut. -/
theorem bare_exception_cut_left_instance
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (H : BareCounterexample (A ⊔ B) h x)
    (hxS : x ∈ S) (hhS : h ∈ S) (hhx : h ≠ x)
    (hinter : S ∩ T = {x}) (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hxEvenA : Even (A.degree x)) :
    BareInstance (A.induce S) ⟨h, hhS⟩ ⟨x, hxS⟩ := by
  rcases H with ⟨⟨hconn, hne, hhpos, hhEven, hxEven, hbare, hcap⟩, hfail⟩
  have hhT : h ∉ T := by
    intro hhT
    have hmem : h ∈ S ∩ T := ⟨hhS, hhT⟩
    have : h = x := by simpa only [hinter, Set.mem_singleton_iff] using hmem
    exact hhx this
  have hBiso : ∀ w, ¬ B.Adj h w := fun w hw => hhT (hB ⟨w, hw⟩)
  have hhdeg : (A ⊔ B).degree h = A.degree h := by
    have hzero : B.neighborFinset h = ∅ := by
      ext w
      simp [hBiso w]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      hzero]
    simp
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = x := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hhposA : 0 < (A.induce S).degree ⟨h, hhS⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhpos
  have hhEvenA : Even ((A.induce S).degree ⟨h, hhS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhEven
  have hxEvenAS : Even ((A.induce S).degree ⟨x, hxS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hxEvenA
  have hbareA : eDegree (A.induce S) ⟨h, hhS⟩ = 0 := by
    rw [eDegree_induce_of_support_subset A S hA]
    apply Nat.eq_zero_of_le_zero
    refine (Finset.card_le_card
      (evenNeighbors_subset_left_one_vertex_union A B x h hxEven hmeet)).trans ?_
    exact Nat.le_of_eq hbare
  refine ⟨hconnA, ?_, hhposA, hhEvenA, hxEvenAS, hbareA, ?_⟩
  · intro hEq
    apply hhx
    exact congrArg Subtype.val hEq
  · intro v hv hvh hvx
    rw [eDegree_induce_of_support_subset A S hA]
    apply bare_cap_left A B x h x hxEven hmeet hcap v.val ?_ ?_ ?_
    · rwa [← SimpleGraph.degree_induce_of_support_subset hA v]
    · intro hval
      apply hvh
      exact Subtype.ext hval
    · intro hval
      apply hvx
      exact Subtype.ext hval

/-- Relative B0 minimality supplies the h-side conclusion for an actual
exceptional cut once the opposite side has a vertex distinct from the cut
hub.  This is the induction consumer for the even-local branch. -/
theorem bare_exception_cut_left_conclusion_of_minimal
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x b : V) (H : BareMinimalCounterexample (A ⊔ B) h x)
    (hxS : x ∈ S) (hhS : h ∈ S) (hhx : h ≠ x)
    (hinter : S ∩ T = {x}) (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hxEvenA : Even (A.degree x))
    (hbT : b ∈ T) (hbx : b ≠ x) :
    BareConclusion (A.induce S) ⟨h, hhS⟩ := by
  have hsmall : Fintype.card S < Fintype.card V :=
    cut_piece_card_lt S T x b hinter hbT hbx
  have hinst : BareInstance (A.induce S) ⟨h, hhS⟩ ⟨x, hxS⟩ :=
    bare_exception_cut_left_instance A B S T h x H.counterexample
      hxS hhS hhx hinter hA hB hconnA hxEvenA
  exact H.of_vertex_smaller S (A.induce S) ⟨h, hhS⟩ ⟨x, hxS⟩ hsmall hinst

/-- In a relative B0 minimum counterexample, deleting the exceptional vertex
cannot disconnect the graph.  The literal h-anchored cut pieces are obtained
from reachability after deletion.  Their h-side has even local degree by the
odd-branch contradiction; relative minimality closes that side and the
checked even-local assembly closes the original graph. -/
theorem bare_exception_noncut
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h x : V) (H : BareMinimalCounterexample G h x) :
    (G.induce {v | v ≠ x}).Connected := by
  classical
  by_contra hdisc
  have hhx : h ≠ x := H.counterexample.1.2.1
  obtain ⟨b, hsep⟩ := exists_not_reachable_of_not_connected
    (G.induce {v | v ≠ x}) ⟨h, hhx⟩ hdisc
  obtain ⟨S, T, hcover, hinter, hhS, hbT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G H.counterexample.1.1 x h b hhx b.property hsep
  have hxS : x ∈ S := by
    have : x ∈ S ∩ T := by simpa [hinter]
    exact this.1
  have hxT : x ∈ T := by
    have : x ∈ S ∩ T := by simpa [hinter]
    exact this.2
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  have H' : BareMinimalCounterexample (A ⊔ B) h x :=
    bareMinimalCounterexample_congr h x hAB.symm H
  letI : DecidablePred (· ∈ (A ⊔ B).neighborSet x) :=
    fun v => SimpleGraph.neighborSet.memDecidable (A ⊔ B) x v
  have hxEvenA : Even (A.degree x) :=
    bare_exception_cut_h_side_even A B S T h x H'.counterexample
      hxS hxT hhS hhx hcover hinter hA hB hconnA hconnB
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = x := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hdis : Disjoint (A.neighborFinset x) (B.neighborFinset x) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset x w).mp ha
    have hb' := (B.mem_neighborFinset x w).mp hb
    exact ha'.ne (hmeet w ⟨x, ha'.symm⟩ ⟨x, hb'.symm⟩).symm
  have hxdeg : (A ⊔ B).degree x = A.degree x + B.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hxEvenB : Even (B.degree x) := by
    have hxEven : Even ((A ⊔ B).degree x) := H'.counterexample.1.2.2.2.2.1
    rw [hxdeg] at hxEven
    exact (Nat.even_add.mp hxEven).mp hxEvenA
  have hincA : ∃ q, A.Adj x q := by
    have hnt : Nontrivial S := ⟨⟨⟨x, hxS⟩, ⟨h, hhS⟩, by
      intro heq
      exact hhx (congrArg Subtype.val heq).symm⟩⟩
    have hp := hconnA.preconnected.degree_pos_of_nontrivial ⟨x, hxS⟩
    rw [SimpleGraph.degree_induce_of_support_subset hA] at hp
    exact (A.degree_pos_iff_exists_adj x).mp hp
  have hincB : ∃ q, B.Adj x q := by
    have hnt : Nontrivial T := ⟨⟨⟨x, hxT⟩, ⟨b, hbT⟩, by
      intro heq
      exact b.property (congrArg Subtype.val heq).symm⟩⟩
    have hp := hconnB.preconnected.degree_pos_of_nontrivial ⟨x, hxT⟩
    rw [SimpleGraph.degree_induce_of_support_subset hB] at hp
    exact (B.degree_pos_iff_exists_adj x).mp hp
  have hbareA : BareConclusion (A.induce S) ⟨h, hhS⟩ :=
    bare_exception_cut_left_conclusion_of_minimal A B S T h x b H'
      hxS hhS hhx hinter hA hB hconnA hxEvenA hbT b.property
  obtain ⟨F, hFsize, hhF⟩ := bare_exception_cut_even_assembly_of_bare A B S T h x
    H'.counterexample hxS hxT hhS hhx hcover hinter hA hB hconnB hxEvenB hincA hincB hbareA
  exact H'.counterexample.2 ⟨F, hFsize, hhF⟩

/-- The odd-local-degree branch of the B0 even-separator reduction.  The two
actual connected *induced* pieces each have only one possible exception, so
the published endpoint theorem supplies a reserve on its designated hub. Odd
local degree supplies an endpoint at the separator on both sides; gluing
saves one path and retains the prescribed `h` reserve. -/
theorem bare_odd_separator_assembly
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z h x : V) (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hhpos : 0 < (A.induce S).degree ⟨h, hhS⟩)
    (hhEven : Even ((A.induce S).degree ⟨h, hhS⟩))
    (hxpos : 0 < (B.induce T).degree ⟨x, hxT⟩)
    (hxEven : Even ((B.induce T).degree ⟨x, hxT⟩))
    (hcapA : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
      eDegree (A.induce S) v ≤ 3)
    (hcapB : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
      eDegree (B.induce T) v ≤ 3)
    (hzAo : Odd ((A.induce S).degree ⟨z, hzS⟩))
    (hzBo : Odd ((B.induce T).degree ⟨z, hzT⟩)) :
    ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hwS : w ∈ S := hA ⟨q, hAq⟩
    have hwT : w ∈ T := hB ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hwS, hwT⟩
    simpa [hinter] using hw
  have hcapAS : ∀ v : S, Even ((A.induce S).degree v) → v ≠ ⟨h, hhS⟩ →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh
    apply hcapA v hv
    intro hval
    exact hvh (Subtype.ext hval)
  have hcapBT : ∀ v : T, Even ((B.induce T).degree v) → v ≠ ⟨x, hxT⟩ →
      eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx
    apply hcapB v hv
    intro hval
    exact hvx (Subtype.ext hval)
  obtain ⟨D0, hD0size, hhD0⟩ := one_exception_endpoint (A.induce S) ⟨h, hhS⟩
    hconnA hhpos hhEven hcapAS
  obtain ⟨E0, hE0size, _⟩ := one_exception_endpoint (B.induce T) ⟨x, hxT⟩
    hconnB hxpos hxEven hcapBT
  obtain ⟨D, hDsize, hDends⟩ := lift_cut_piece S hA D0
  obtain ⟨E, hEsize, hEends⟩ := lift_cut_piece T hB E0
  have hzA : Odd (A.degree z) := by
    rw [← SimpleGraph.degree_induce_of_support_subset hA ⟨z, hzS⟩]
    exact hzAo
  have hzB : Odd (B.degree z) := by
    rw [← SimpleGraph.degree_induce_of_support_subset hB ⟨z, hzT⟩]
    exact hzBo
  obtain ⟨F, hFsize, hFends⟩ := D.single_merge_endpoints E z
    (D.endpointCount_pos_of_odd_degree z hzA)
    (E.endpointCount_pos_of_odd_degree z hzB) hmeet
  refine ⟨F, ?_, ?_⟩
  · have hcard := card_cover_single_inter S T z hcover hinter
    have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
      (Fintype.card V) hcard
    have hAcard : D.size ≤ (Fintype.card S + 1) / 2 := by omega
    have hBcard : E.size ≤ (Fintype.card T + 1) / 2 := by omega
    omega
  · have hh := hFends h
    simp only [hzh, if_false, mul_zero, Nat.add_zero] at hh
    have hhmap := hDends ⟨h, hhS⟩
    have hhbase : 2 ≤ D.endpointCount h := by
      rw [hhmap]
      exact hhD0
    omega

/-- The even-local separator branch in which the `x` side has odd order.
The odd-order simultaneous theorem supplies endpoints at `x` and the shared
separator; the `h` side needs only the one-exception endpoint theorem. -/
theorem bare_even_separator_odd_x_side_assembly
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z h x : V) (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hhpos : 0 < (A.induce S).degree ⟨h, hhS⟩)
    (hhEven : Even ((A.induce S).degree ⟨h, hhS⟩))
    (hxEven : Even ((B.induce T).degree ⟨x, hxT⟩))
    (hzEven : Even ((B.induce T).degree ⟨z, hzT⟩))
    (hcapA : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
      eDegree (A.induce S) v ≤ 3)
    (hcapB : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
      v.val ≠ z → eDegree (B.induce T) v ≤ 3)
    (hincA : ∃ q, A.Adj z q)
    (m : ℕ) (hoddT : Fintype.card T = 2 * m + 1) :
    ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hwS : w ∈ S := hA ⟨q, hAq⟩
    have hwT : w ∈ T := hB ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hwS, hwT⟩
    simpa [hinter] using hw
  have hcapAS : ∀ v : S, Even ((A.induce S).degree v) → v ≠ ⟨h, hhS⟩ →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh
    apply hcapA v hv
    intro hval
    exact hvh (Subtype.ext hval)
  have hcapBT : ∀ v : T, Even ((B.induce T).degree v) → v ≠ ⟨x, hxT⟩ →
      v ≠ ⟨z, hzT⟩ → eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx hvz
    apply hcapB v hv
    · intro hval
      exact hvx (Subtype.ext hval)
    · intro hval
      exact hvz (Subtype.ext hval)
  obtain ⟨D0, hD0size, hhD0⟩ := one_exception_endpoint (A.induce S) ⟨h, hhS⟩
    hconnA hhpos hhEven hcapAS
  obtain ⟨E0, hE0size, hxE0, hzE0⟩ := odd_order_simultaneous m hoddT hconnB
    ⟨x, hxT⟩ ⟨z, hzT⟩ (fun h => hzx (congrArg Subtype.val h).symm) hxEven hzEven hcapBT
  obtain ⟨D, hDsize, hDends⟩ := lift_cut_piece S hA D0
  obtain ⟨E, hEsize, hEends⟩ := lift_cut_piece T hB E0
  have hzE : 2 ≤ E.endpointCount z := by
    rw [hEends ⟨z, hzT⟩]
    exact hzE0
  obtain ⟨F0, hF0size, hF0ends⟩ := E.glue_at_exposed_vertex D z hzE hincA
    (fun w hwB hwA => hmeet w hwA hwB)
  have hFgraph : B ⊔ A = A ⊔ B := by simpa only [sup_comm]
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  have hAcard : D.size ≤ (Fintype.card S + 1) / 2 := by omega
  have hBcard : E.size ≤ (Fintype.card T + 1) / 2 := by omega
  have hhbase : 2 ≤ D.endpointCount h := by
    rw [hDends ⟨h, hhS⟩]
    exact hhD0
  have hhF0 := hF0ends h
  simp only [hzh, if_false, mul_zero, Nat.add_zero] at hhF0
  have hout : ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
    rw [← hFgraph]
    refine ⟨F0, ?_, ?_⟩
    · omega
    · omega
  exact hout

/-- The symmetric even-local separator branch, when the `h` side has odd
order.  Here `ODD-ALL` directly provides both the preserved `h` reserve and
the separator reserve used to absorb an arbitrary carrier from the x-side. -/
theorem bare_even_separator_odd_h_side_assembly
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (z h x : V) (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hhEven : Even ((A.induce S).degree ⟨h, hhS⟩))
    (hzEven : Even ((A.induce S).degree ⟨z, hzS⟩))
    (hxpos : 0 < (B.induce T).degree ⟨x, hxT⟩)
    (hxEven : Even ((B.induce T).degree ⟨x, hxT⟩))
    (hcapA : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
      v.val ≠ z → eDegree (A.induce S) v ≤ 3)
    (hcapB : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
      eDegree (B.induce T) v ≤ 3)
    (hincB : ∃ q, B.Adj z q)
    (m : ℕ) (hoddS : Fintype.card S = 2 * m + 1) :
    ∃ F : Decomposition (A ⊔ B), F.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ F.endpointCount h := by
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hwS : w ∈ S := hA ⟨q, hAq⟩
    have hwT : w ∈ T := hB ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hwS, hwT⟩
    simpa [hinter] using hw
  have hcapAS : ∀ v : S, Even ((A.induce S).degree v) → v ≠ ⟨h, hhS⟩ →
      v ≠ ⟨z, hzS⟩ → eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh hvz
    apply hcapA v hv
    · intro hval
      exact hvh (Subtype.ext hval)
    · intro hval
      exact hvz (Subtype.ext hval)
  have hcapBT : ∀ v : T, Even ((B.induce T).degree v) → v ≠ ⟨x, hxT⟩ →
      eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx
    apply hcapB v hv
    intro hval
    exact hvx (Subtype.ext hval)
  obtain ⟨D0, hD0size, hhD0, hzD0⟩ := odd_order_simultaneous m hoddS hconnA
    ⟨h, hhS⟩ ⟨z, hzS⟩ (fun h => hzh (congrArg Subtype.val h).symm) hhEven hzEven hcapAS
  obtain ⟨E0, hE0size, _⟩ := one_exception_endpoint (B.induce T) ⟨x, hxT⟩
    hconnB hxpos hxEven hcapBT
  obtain ⟨D, hDsize, hDends⟩ := lift_cut_piece S hA D0
  obtain ⟨E, hEsize, _⟩ := lift_cut_piece T hB E0
  have hzD : 2 ≤ D.endpointCount z := by
    rw [hDends ⟨z, hzS⟩]
    exact hzD0
  obtain ⟨F, hFsize, hFends⟩ := D.glue_at_exposed_vertex E z hzD hincB hmeet
  have hcard := card_cover_single_inter S T z hcover hinter
  have hbudget := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hcard
  have hAcard : D.size ≤ (Fintype.card S + 1) / 2 := by omega
  have hBcard : E.size ≤ (Fintype.card T + 1) / 2 := by omega
  have hhbase : 2 ≤ D.endpointCount h := by
    rw [hDends ⟨h, hhS⟩]
    exact hhD0
  have hhF := hFends h
  simp only [hzh, if_false, mul_zero, Nat.add_zero] at hhF
  exact ⟨F, by omega, by omega⟩

/-- The normalized odd-local cut consumer.  Here the ambient graph is already
the union of its two actual cut pieces, so all degree and endpoint transports
are literal.  A later, small equality-transport wrapper connects this theorem
to `cut_vertex_pieces`; keeping that transport separate prevents an equality
of graph values from silently changing the degree instances used below. -/
theorem bare_odd_separator_split_false
    (z h x : V) (H : BareCounterexample (A ⊔ B) h x)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hzEven : Even ((A ⊔ B).degree z)) (hzOddA : Odd (A.degree z)) : False := by
  rcases H with ⟨⟨hconn, hhx, hhpos, hhEven, hxEven, hbare, hcap⟩, hfail⟩
  have hhT : h ∉ T := by
    intro hT
    have : h ∈ S ∩ T := ⟨hhS, hT⟩
    have : h = z := by simpa only [hinter, Set.mem_singleton_iff] using this
    exact hzh this.symm
  have hxS : x ∉ S := by
    intro hS
    have : x ∈ S ∩ T := ⟨hS, hxT⟩
    have : x = z := by simpa only [hinter, Set.mem_singleton_iff] using this
    exact hzx this.symm
  have hBiso : ∀ w, ¬ B.Adj h w := fun w hw => hhT (hB ⟨w, hw⟩)
  have hAiso : ∀ w, ¬ A.Adj x w := fun w hw => hxS (hA ⟨w, hw⟩)
  have hhdeg : (A ⊔ B).degree h = A.degree h := by
    have hzero : B.neighborFinset h = ∅ := by
      ext w
      simp [hBiso w]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      hzero]
    simp
  have hxdeg : (A ⊔ B).degree x = B.degree x :=
    degree_union_of_left_isolated A B x hAiso
  have hhposA : 0 < (A.induce S).degree ⟨h, hhS⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhpos
  have hhEvenA : Even ((A.induce S).degree ⟨h, hhS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhEven
  have hxposB : 0 < (B.induce T).degree ⟨x, hxT⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hB, ← hxdeg]
    have hex := BareCounterexample.exception_gt_three ⟨⟨hconn, hhx, hhpos,
      hhEven, hxEven, hbare, hcap⟩, hfail⟩
    have hle := eDegree_le_degree (G := A ⊔ B) x
    omega
  have hxEvenB : Even ((B.induce T).degree ⟨x, hxT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB, ← hxdeg]
    exact hxEven
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hcapA0 := bare_cap_left A B z h x hzEven hmeet hcap
  have hcapB0 := bare_cap_induced_right A B T z h x hB hzEven hmeet hcap
  have hcapA : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA0 v.val hvA hvh
    intro hvx
    exact hxS (hvx ▸ v.property)
  have hcapB : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
      eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx
    apply hcapB0 v hv
    · intro hvh
      exact hhT (hvh ▸ v.property)
    · exact hvx
  have hzOddAS : Odd ((A.induce S).degree ⟨z, hzS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hzOddA
  have hdis : Disjoint (A.neighborFinset z) (B.neighborFinset z) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset z w).mp ha
    have hb' := (B.mem_neighborFinset z w).mp hb
    exact ha'.ne (hmeet w ⟨z, ha'.symm⟩ ⟨z, hb'.symm⟩).symm
  have hzdeg : (A ⊔ B).degree z = A.degree z + B.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  have hzOddB : Odd (B.degree z) := by
    rw [Nat.even_iff, hzdeg] at hzEven
    rw [Nat.odd_iff] at hzOddA ⊢
    omega
  have hzOddBS : Odd ((B.induce T).degree ⟨z, hzT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hzOddB
  obtain ⟨F, hF, hhF⟩ := bare_odd_separator_assembly A B S T z h x
    hzS hzT hhS hxT hzh hcover hinter hA hB hconnA hconnB hhposA hhEvenA
    hxposB hxEvenB hcapA hcapB hzOddAS hzOddBS
  exact hfail ⟨F, hF, hhF⟩

/-- Equality-transport wrapper for an actual odd-local split.  The hypotheses
are the graph-theoretic output of `cut_vertex_pieces` after the two hubs have
been placed on opposite sides.  The explicit transports preserve the chosen
decidability instances before the normalized consumer is applied. -/
theorem bare_odd_separator_actual_split_false
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z h x : V) (H : BareCounterexample G h x)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hgraph : A ⊔ B = G) (hzEven : Even (G.degree z))
    (hzOddA : Odd (A.degree z)) : False := by
  have H' := bareCounterexample_congr h x hgraph.symm H
  have hzEven' := even_degree_congr z hgraph.symm hzEven
  exact bare_odd_separator_split_false A B z h x H' S T hzS hzT hhS hxT
    hzh hzx hcover hinter hA hB hconnA hconnB hzEven' hzOddA

/-- In an actual hub-separating B0 cut, the h-side local separator degree
cannot be odd.  This is the literal structural reduction delivered by the
odd-local consumer; the even-local schedules remain the next branch. -/
theorem bare_separator_h_side_even
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z h x : V) (H : BareCounterexample G h x)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hgraph : A ⊔ B = G) (hzEven : Even (G.degree z)) :
    Even (A.degree z) := by
  apply Nat.not_odd_iff_even.mp
  intro hzOddA
  exact bare_odd_separator_actual_split_false A B G z h x H S T hzS hzT hhS hxT
    hzh hzx hcover hinter hA hB hconnA hconnB hgraph hzEven hzOddA

/-- At a one-vertex union, an even ambient separator and an even left local
degree force an even right local degree. -/
theorem even_right_of_even_one_vertex_union (z : V)
    (hz : Even ((A ⊔ B).degree z)) (hzA : Even (A.degree z))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = z) :
    Even (B.degree z) := by
  have hdis : Disjoint (A.neighborFinset z) (B.neighborFinset z) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have ha' := (A.mem_neighborFinset z w).mp ha
    have hb' := (B.mem_neighborFinset z w).mp hb
    exact ha'.ne (hmeet w ⟨z, ha'.symm⟩ ⟨z, hb'.symm⟩).symm
  have hzdeg : (A ⊔ B).degree z = A.degree z + B.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      Finset.card_union_of_disjoint hdis]
    rfl
  apply Nat.not_odd_iff_even.mp
  intro hzBo
  rcases hz with ⟨u, hu⟩
  rcases hzA with ⟨v, hv⟩
  rcases hzBo with ⟨w, hw⟩
  omega

/-- In a one-vertex union of an even-order graph, at least one side has odd
order. The explicit witnesses match the `2*m+1` inputs of the two schedules. -/
theorem one_vertex_cut_even_order_odd_side (s t n : ℕ)
    (hn : Even n) (hcard : n + 1 = s + t) :
    (∃ m, s = 2 * m + 1) ∨ ∃ m, t = 2 * m + 1 := by
  by_cases hs : Even s
  · right
    apply Nat.not_even_iff_odd.mp
    intro ht
    rcases hn with ⟨k, hk⟩
    rcases hs with ⟨a, ha⟩
    rcases ht with ⟨b, hb⟩
    omega
  · exact Or.inl (Nat.not_even_iff_odd.mp hs)

/-- The actual even-local hub-separating-cut consumer.  Once the h-side is
known even by the odd-local contradiction, the other local degree is even as
well.  Global even order selects one odd cut side, so one of the two checked
even-local assemblies contradicts the bare counterexample. -/
theorem bare_even_separator_actual_split_false
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z h x : V) (H : BareCounterexample G h x)
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hzS : z ∈ S) (hzT : z ∈ T) (hhS : h ∈ S) (hxT : x ∈ T)
    (hzh : z ≠ h) (hzx : z ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {z})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hgraph : A ⊔ B = G) (hzEven : Even (G.degree z)) : False := by
  have H' := bareCounterexample_congr h x hgraph.symm H
  have hzEven' := even_degree_congr z hgraph.symm hzEven
  rcases H' with ⟨⟨hconn, hhx, hhpos, hhEven, hxEven, hbare, hcap⟩, hfail⟩
  have hhT : h ∉ T := by
    intro hT
    have hh : h ∈ S ∩ T := ⟨hhS, hT⟩
    have : h = z := by simpa only [hinter, Set.mem_singleton_iff] using hh
    exact hzh this.symm
  have hxS : x ∉ S := by
    intro hS
    have hx : x ∈ S ∩ T := ⟨hS, hxT⟩
    have : x = z := by simpa only [hinter, Set.mem_singleton_iff] using hx
    exact hzx this.symm
  have hBiso : ∀ w, ¬ B.Adj h w := fun w hw => hhT (hB ⟨w, hw⟩)
  have hAiso : ∀ w, ¬ A.Adj x w := fun w hw => hxS (hA ⟨w, hw⟩)
  have hhdeg : (A ⊔ B).degree h = A.degree h := by
    have hzero : B.neighborFinset h = ∅ := by
      ext w
      simp [hBiso w]
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
      hzero]
    simp
  have hxdeg : (A ⊔ B).degree x = B.degree x :=
    degree_union_of_left_isolated A B x hAiso
  have hhposA : 0 < (A.induce S).degree ⟨h, hhS⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhpos
  have hhEvenA : Even ((A.induce S).degree ⟨h, hhS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA, ← hhdeg]
    exact hhEven
  have hxposB : 0 < (B.induce T).degree ⟨x, hxT⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hB, ← hxdeg]
    have hex := BareCounterexample.exception_gt_three ⟨⟨hconn, hhx, hhpos,
      hhEven, hxEven, hbare, hcap⟩, hfail⟩
    have hle := eDegree_le_degree (G := A ⊔ B) x
    omega
  have hxEvenB : Even ((B.induce T).degree ⟨x, hxT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB, ← hxdeg]
    exact hxEven
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ q, B.Adj w q) → w = z := by
    intro w hAw hBw
    rcases hAw with ⟨q, hAq⟩
    rcases hBw with ⟨r, hBr⟩
    have hw : w ∈ S ∩ T := ⟨hA ⟨q, hAq⟩, hB ⟨r, hBr⟩⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hcapA0 := bare_cap_left A B z h x hzEven' hmeet hcap
  have hcapB0 := bare_cap_induced_right A B T z h x hB hzEven' hmeet hcap
  have hcapA : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
      eDegree (A.induce S) v ≤ 3 := by
    intro v hv hvh
    rw [eDegree_induce_of_support_subset A S hA v]
    have hvA : Even (A.degree v.val) := by
      rwa [SimpleGraph.degree_induce_of_support_subset hA v] at hv
    apply hcapA0 v.val hvA hvh
    intro hvx
    exact hxS (hvx ▸ v.property)
  have hcapB : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
      eDegree (B.induce T) v ≤ 3 := by
    intro v hv hvx
    apply hcapB0 v hv
    · intro hvh
      exact hhT (hvh ▸ v.property)
    · exact hvx
  have hzEvenA : Even (A.degree z) :=
    bare_separator_h_side_even A B G z h x H S T hzS hzT hhS hxT hzh hzx
      hcover hinter hA hB hconnA hconnB hgraph hzEven
  have hzEvenB : Even (B.degree z) :=
    even_right_of_even_one_vertex_union A B z hzEven' hzEvenA hmeet
  have hzEvenAS : Even ((A.induce S).degree ⟨z, hzS⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hA]
    exact hzEvenA
  have hzEvenBS : Even ((B.induce T).degree ⟨z, hzT⟩) := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact hzEvenB
  have hincA : ∃ q, A.Adj z q := by
    have hnt : Nontrivial S := ⟨⟨⟨z, hzS⟩, ⟨h, hhS⟩,
      fun e => hzh (congrArg Subtype.val e)⟩⟩
    have hp := hconnA.preconnected.degree_pos_of_nontrivial ⟨z, hzS⟩
    rw [SimpleGraph.degree_induce_of_support_subset hA] at hp
    exact (A.degree_pos_iff_exists_adj z).mp hp
  have hincB : ∃ q, B.Adj z q := by
    have hnt : Nontrivial T := ⟨⟨⟨z, hzT⟩, ⟨x, hxT⟩,
      fun e => hzx (congrArg Subtype.val e)⟩⟩
    have hp := hconnB.preconnected.degree_pos_of_nontrivial ⟨z, hzT⟩
    rw [SimpleGraph.degree_induce_of_support_subset hB] at hp
    exact (B.degree_pos_iff_exists_adj z).mp hp
  have horder := BareCounterexample.card_even ⟨⟨hconn, hhx, hhpos, hhEven,
    hxEven, hbare, hcap⟩, hfail⟩
  have hcard := card_cover_single_inter S T z hcover hinter
  rcases one_vertex_cut_even_order_odd_side (Fintype.card S) (Fintype.card T)
    (Fintype.card V) horder hcard with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hcapA' : ∀ v : S, Even ((A.induce S).degree v) → v.val ≠ h →
        v.val ≠ z → eDegree (A.induce S) v ≤ 3 := by
      intro v hv hvh _
      exact hcapA v hv hvh
    obtain ⟨F, hF, hhF⟩ := bare_even_separator_odd_h_side_assembly A B S T z h x
      hzS hzT hhS hxT hzh hzx hcover hinter hA hB hconnA hconnB hhEvenA hzEvenAS
      hxposB hxEvenB hcapA' hcapB hincB m hm
    exact hfail ⟨F, hF, hhF⟩
  · have hcapB' : ∀ v : T, Even ((B.induce T).degree v) → v.val ≠ x →
        v.val ≠ z → eDegree (B.induce T) v ≤ 3 := by
      intro v hv hvx _
      exact hcapB v hv hvx
    obtain ⟨F, hF, hhF⟩ := bare_even_separator_odd_x_side_assembly A B S T z h x
      hzS hzT hhS hxT hzh hzx hcover hinter hA hB hconnA hconnB hhposA hhEvenA
      hxEvenB hzEvenBS hcapA hcapB' hincA m hm
    exact hfail ⟨F, hF, hhF⟩

/-- A literal deletion that separates the two designated hubs produces an
actual cut partition whose `h`-side separator degree is even.  This is the
first consumer of `cut_vertex_pieces` in the bare argument: it constructs the
pieces and supplies all support and connectedness data, rather than assuming a
normalized union.  The still-open even-local schedule is intentionally not
hidden by this structural extraction lemma. -/
theorem bare_hx_separation_has_even_h_side
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z h x : V) (H : BareCounterexample G h x)
    (hzh : z ≠ h) (hzx : z ≠ x) (hzEven : Even (G.degree z))
    (hsep : ¬ (G.induce {v | v ≠ z}).Reachable ⟨h, hzh.symm⟩ ⟨x, hzx.symm⟩) :
    ∃ S T : Set V, ∃ _ : DecidablePred (· ∈ S), ∃ _ : DecidablePred (· ∈ T),
      z ∈ S ∧ z ∈ T ∧ h ∈ S ∧ x ∈ T ∧
      S ∪ T = Set.univ ∧ S ∩ T = {z} ∧
      Even (((G.induce S).spanningCoe).degree z) := by
  classical
  obtain ⟨S, T, hcover, hinter, hhS, hxT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G H.1.1 z h x hzh.symm hzx.symm hsep
  have hzS : z ∈ S := by
    have : z ∈ S ∩ T := by simpa [hinter]
    exact this.1
  have hzT : z ∈ T := by
    have : z ∈ S ∩ T := by simpa [hinter]
    exact this.2
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  refine ⟨S, T, inferInstance, inferInstance, hzS, hzT, hhS, hxT, hcover, hinter, ?_⟩
  exact bare_separator_h_side_even A B G z h x H S T hzS hzT hhS hxT hzh hzx
    hcover hinter hA hB hconnA hconnB hAB hzEven

/-- A bare counterexample has no even separator whose deletion separates the
two designated hubs. This packages the completed odd- and even-local cut
branches as the literal contradiction consumed by later reductions. -/
theorem bare_even_separator_separating_hubs_false
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (z h x : V) (H : BareCounterexample G h x)
    (hzh : z ≠ h) (hzx : z ≠ x) (hzEven : Even (G.degree z))
    (hsep : ¬ (G.induce {v | v ≠ z}).Reachable ⟨h, hzh.symm⟩ ⟨x, hzx.symm⟩) :
    False := by
  classical
  obtain ⟨S, T, hcover, hinter, hhS, hxT, hgraph, hconnS, hconnT⟩ :=
    cut_vertex_pieces G H.1.1 z h x hzh.symm hzx.symm hsep
  have hzS : z ∈ S := by
    have : z ∈ S ∩ T := by simpa [hinter]
    exact this.1
  have hzT : z ∈ T := by
    have : z ∈ S ∩ T := by simpa [hinter]
    exact this.2
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hA : A.support ⊆ S := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hB : B.support ⊆ T := by
    intro v hv
    rw [SimpleGraph.support_spanningCoe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  have hconnA : (A.induce S).Connected := by
    simpa only [A, SimpleGraph.induce_spanningCoe] using hconnS
  have hconnB : (B.induce T).Connected := by
    simpa only [B, SimpleGraph.induce_spanningCoe] using hconnT
  have hAB : A ⊔ B = G := by
    simpa only [A, B] using hgraph
  exact bare_even_separator_actual_split_false A B G z h x H S T hzS hzT hhS hxT
    hzh hzx hcover hinter hA hB hconnA hconnB hAB hzEven

end Gallai.TwoException
