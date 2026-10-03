/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareCuts
public import Gallai.TwoException.PrescribedRetainedEdge
public import Gallai.TwoException.PendantReserve

@[expose] public section

/-! # Prescribed-endpoint cut-side induction and assembly -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Apply vertex induction to a genuine cut side containing the other
exception, or the one-exception theorem when that vertex is absent. -/
theorem prescribed_cut_side_endpoint
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (h x : V) (hhS : h ∈ S)
    (hhne : h ≠ x) (hconn : (A.induce S).Connected)
    (hhpos : 0 < (A.induce S).degree ⟨h, hhS⟩)
    (hhEven : Even ((A.induce S).degree ⟨h, hhS⟩))
    (hxEven : ∀ hxS : x ∈ S, Even ((A.induce S).degree ⟨x, hxS⟩))
    (hcap : ∀ w : S, Even ((A.induce S).degree w) →
      w.val ≠ h → w.val ≠ x → eDegree (A.induce S) w ≤ 3)
    (hsmall : Fintype.card S < Fintype.card V)
    (hind : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion (A.induce S) ⟨h, hhS⟩ := by
  classical
  by_cases hxS : x ∈ S
  · apply hind S (A.induce S) hsmall hconn ⟨h, hhS⟩ ⟨x, hxS⟩
      (fun he => hhne (congrArg Subtype.val he)) hhpos hhEven (hxEven hxS)
    intro w hw hwh hwx
    exact hcap w hw (fun he => hwh (Subtype.ext he))
      (fun he => hwx (Subtype.ext he))
  · apply one_exception_endpoint (A.induce S) ⟨h, hhS⟩ hconn hhpos hhEven
    intro w hw hwh
    exact hcap w hw (fun he => hwh (Subtype.ext he))
      (fun he => hxS (he ▸ w.property))

omit [Fintype V] in
/-- Lift an actual support-contained cut side without changing its path
count or endpoint multiplicities. -/
theorem prescribed_lift_cut_side
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (hs : A.support ⊆ S)
    (D : Decomposition (A.induce S)) :
    ∃ E : Decomposition A, E.size = D.size ∧
      ∀ w : S, E.endpointCount w.val = D.endpointCount w := by
  have hg : (A.induce S).map (Function.Embedding.subtype _) = A :=
    (A.spanningCoe_induce_eq_self S).mpr hs
  have hout : ∃ E : Decomposition ((A.induce S).map (Function.Embedding.subtype _)),
      E.size = D.size ∧ ∀ w : S, E.endpointCount w.val = D.endpointCount w :=
    ⟨D.map (Function.Embedding.subtype _), rfl,
      fun w => D.map_endpointCount (Function.Embedding.subtype _) w⟩
  rwa [hg] at hout

/-- Two twice-exposed even-local cut sides glue within the original ceiling
budget, retaining two endpoints at the prescribed separator. -/
theorem prescribed_even_cut_assembly
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hleft : BareConclusion (A.induce S) ⟨h, hhS⟩)
    (hright : BareConclusion (B.induce T) ⟨h, hhT⟩) :
    BareConclusion (A ⊔ B) h := by
  classical
  obtain ⟨D0, hd0, hhD0⟩ := hleft
  obtain ⟨E0, he0, hhE0⟩ := hright
  obtain ⟨D, hd, hDends⟩ := prescribed_lift_cut_side A S hA D0
  obtain ⟨E, he, hEends⟩ := prescribed_lift_cut_side B T hB E0
  have hhD : 2 ≤ D.endpointCount h := by rwa [hDends ⟨h, hhS⟩]
  have hhE : 2 ≤ E.endpointCount h := by rwa [hEends ⟨h, hhT⟩]
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w ha hb
    have hw : w ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  obtain ⟨F, hsize, hends⟩ := single_merge_preserves_joint_reserve A B D E h
    (by omega) (by omega) hmeet (by omega)
  have hc := card_cover_single_inter S T h hcover hinter
  have hb := ceiling_one_vertex_budget (Fintype.card S) (Fintype.card T)
    (Fintype.card V) hc
  exact ⟨F, by omega, hends⟩

omit [Fintype V] in
/-- Trimming a pendant carrier distinguishes a saved singleton path from
a longer carrier's extra endpoint at the hub. -/
theorem prescribed_trim_pendant_cases
    (G : SimpleGraph V) (D : Decomposition G) (i : Fin D.size)
    (z h : V) (hz : (D.path i).start = z)
    (hh : (D.path i).walk.snd = h) (hreserve : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition (G.deleteEdges {s(z, h)}),
      (E.size + 1 = D.size ∧ 1 ≤ E.endpointCount h) ∨
      (E.size = D.size ∧ 3 ≤ E.endpointCount h) := by
  obtain ⟨E, hsize, _, hends, _⟩ := D.exists_delete_first i
  subst z
  subst h
  refine ⟨E, ?_⟩
  by_cases hone : (D.path i).walk.length = 1
  · simp only [hone, ↓reduceIte] at hsize hends
    exact Or.inl ⟨hsize, by omega⟩
  · simp only [hone, ↓reduceIte] at hsize hends
    exact Or.inr ⟨by omega, by omega⟩

/-- The odd-local cut assembly uses either the singleton pendant's saved
path, with no join, or three endpoints on the trimmed side, with one join.
The two alternatives are kept explicit to prevent losing the hub reserve. -/
theorem prescribed_odd_cut_assembly
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (D : Decomposition A) (E : Decomposition B) (h : V)
    (a b : ℕ) (hcard : Fintype.card V + 1 = a + b)
    (hbudgetE : E.size ≤ (b + 1) / 2) (hendsE : 1 ≤ E.endpointCount h)
    (hleft : (D.size + 1 ≤ (a + 1) / 2 ∧ 1 ≤ D.endpointCount h) ∨
      (D.size ≤ (a + 1) / 2 ∧ 3 ≤ D.endpointCount h))
    (hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ r, B.Adj w r) → w = h) :
    BareConclusion (A ⊔ B) h := by
  have hb := ceiling_one_vertex_budget a b (Fintype.card V) hcard
  rcases hleft with ⟨hsizeD, hendsD⟩ | ⟨hsizeD, hendsD⟩
  · have hd : Disjoint A.edgeSet B.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e
      induction e using Sym2.inductionOn with
      | hf u v =>
        intro ha hb
        have hAuv : A.Adj u v := ha
        have hBuv : B.Adj u v := hb
        exact hAuv.ne ((hmeet u ⟨v, hAuv⟩ ⟨v, hBuv⟩).trans
          (hmeet v ⟨u, hAuv.symm⟩ ⟨u, hBuv.symm⟩).symm)
    obtain ⟨F, hs, he⟩ := D.union_disjoint_endpoints E hd
    exact ⟨F, by omega, by have ht := he h; omega⟩
  · obtain ⟨F, hs, he⟩ := single_merge_preserves_joint_reserve A B D E h
      (by omega) (by omega) hmeet (by omega)
    exact ⟨F, by omega, he⟩

/-- An actual even-local right cut side inherits the required cap and the
other exception's parity. Its strict order decrease follows from an edge
on the opposite side, rather than a supplied cardinality estimate. -/
theorem prescribed_actual_even_right_endpoint
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hhT : h ∈ T) (hhne : h ≠ x)
    (hinter : S ∩ T = {h}) (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnB : (B.induce T).Connected)
    (hhEven : Even ((A ⊔ B).degree h)) (hxEven : Even ((A ⊔ B).degree x))
    (hhEvenB : Even (B.degree h))
    (hincA : ∃ a, A.Adj h a) (hincB : ∃ b, B.Adj h b)
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3)
    (hind : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion (B.induce T) ⟨h, hhT⟩ := by
  classical
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w ha hb
    have hw : w ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hsmall : Fintype.card T < Fintype.card V := by
    obtain ⟨a, ha⟩ := hincA
    have hinter' : T ∩ S = {h} := by simpa only [Set.inter_comm] using hinter
    exact cut_piece_card_lt T S h a hinter' (hA ⟨h, ha.symm⟩) ha.ne.symm
  have hp : 0 < (B.induce T).degree ⟨h, hhT⟩ := by
    rw [SimpleGraph.degree_induce_of_support_subset hB]
    exact (B.degree_pos_iff_exists_adj h).mpr hincB
  have he : Even ((B.induce T).degree ⟨h, hhT⟩) := by
    rwa [SimpleGraph.degree_induce_of_support_subset hB]
  have hxSide (hxT : x ∈ T) : Even ((B.induce T).degree ⟨x, hxT⟩) := by
    have hxS : x ∉ S := by
      intro hs
      have hm : x ∈ S ∩ T := ⟨hs, hxT⟩
      have hxh : x = h := by simpa only [hinter, Set.mem_singleton_iff] using hm
      exact hhne hxh.symm
    have hz : A.neighborFinset x = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun ha => hxS (hA ⟨w, ha⟩)
    have hd : (A ⊔ B).degree x = B.degree x := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup, hz]
      simp
    rw [SimpleGraph.degree_induce_of_support_subset hB, ← hd]
    exact hxEven
  exact prescribed_cut_side_endpoint B T h x hhT hhne hconnB hp he hxSide
    (bare_cap_induced_right A B T h h x hB hhEven hmeet hcap) hsmall hind

/-- Both genuine even-local sides are solved from their graph hypotheses
and vertex induction, then joined. No side decomposition or local cap is
supplied as an extra certificate. -/
theorem prescribed_actual_even_cut
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hhS : h ∈ S) (hhT : h ∈ T) (hhne : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hhEven : Even ((A ⊔ B).degree h)) (hxEven : Even ((A ⊔ B).degree x))
    (hhEvenA : Even (A.degree h)) (hhEvenB : Even (B.degree h))
    (hincA : ∃ a, A.Adj h a) (hincB : ∃ b, B.Adj h b)
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3)
    (hind : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion (A ⊔ B) h := by
  have hright := prescribed_actual_even_right_endpoint A B S T h x hhT hhne
    hinter hA hB hconnB hhEven hxEven hhEvenB hincA hincB hcap hind
  have hinter' : T ∩ S = {h} := by simpa only [Set.inter_comm] using hinter
  have hhEven' : Even ((B ⊔ A).degree h) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hhEven
  have hxEven' : Even ((B ⊔ A).degree x) := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hxEven
  have hcap' : ∀ w, Even ((B ⊔ A).degree w) → w ≠ h → w ≠ x →
      eDegree (B ⊔ A) w ≤ 3 := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', sup_comm] using hcap
  have hleft := prescribed_actual_even_right_endpoint B A T S h x hhS hhne
    hinter' hB hA hconnA hhEven' hxEven' hhEvenA hincB hincA hcap' hind
  exact prescribed_even_cut_assembly A B S T h hhS hhT hcover hinter hA hB hleft hright

end Gallai.TwoException
