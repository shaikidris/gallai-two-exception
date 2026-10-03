/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.PrescribedCut
public import Gallai.Structure.PendantReturn
public import Gallai.TwoException.AdjacentHubOddInvariants

@[expose] public section

/-! # Actual fresh-pendant return for a prescribed cut vertex -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A twice-exposed attachment in a fresh-pendant decomposition returns
either with a saved path and a positive endpoint, or without added paths
and with at least three endpoints. The pendant carrier is selected from
the decomposition itself; no orientation or carrier index is supplied. -/
theorem prescribed_pendant_return
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h))
    (hh : 2 ≤ D.endpointCount (.inl h)) :
    ∃ E : Decomposition G,
      (E.size + 1 = D.size ∧ 1 ≤ E.endpointCount h) ∨
      (E.size ≤ D.size ∧ 3 ≤ E.endpointCount h) := by
  obtain ⟨i, hi, hnew⟩ := D.exists_terminal_pendant_carrier G h
  by_cases hold : (D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit)
  · obtain ⟨E, hs, he, _⟩ :=
      D.return_terminal_pendant_at_old_end_saves_one G h i hi hnew hold
    exact ⟨E, Or.inl ⟨hs, by omega⟩⟩
  · obtain ⟨E, hs, he, _⟩ := D.return_terminal_pendant G h i hi hnew
    simp only [hold, ↓reduceIte] at he
    exact ⟨E, Or.inr ⟨hs, by omega⟩⟩

/-- A genuine odd-order side with a twice-exposed fresh-leaf decomposition
returns and combines with the opposite odd-local side within the ambient
ceiling. The singleton return is not merged. -/
theorem prescribed_actual_odd_cut_from_pendant
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (horderS : Odd (Fintype.card S))
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (hd : D.size ≤ (Fintype.card (S ⊕ Unit) + 1) / 2)
    (hhD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩))
    (E0 : Decomposition (B.induce T))
    (he : E0.size ≤ (Fintype.card T + 1) / 2)
    (hhE : 1 ≤ E0.endpointCount ⟨h, hhT⟩) : BareConclusion (A ⊔ B) h := by
  classical
  obtain ⟨D0, hreturn⟩ := prescribed_pendant_return (A.induce S) ⟨h, hhS⟩ D hhD
  obtain ⟨D1, hsD, heD⟩ := prescribed_lift_cut_side A S hA D0
  obtain ⟨E1, hsE, heE⟩ := prescribed_lift_cut_side B T hB E0
  have hceiling : D.size ≤ (Fintype.card S + 1) / 2 := by
    rw [Fintype.card_sum, Fintype.card_unit] at hd
    rw [Nat.odd_iff] at horderS
    omega
  have hleft : (D1.size + 1 ≤ (Fintype.card S + 1) / 2 ∧
      1 ≤ D1.endpointCount h) ∨
      (D1.size ≤ (Fintype.card S + 1) / 2 ∧ 3 ≤ D1.endpointCount h) := by
    have ht := heD ⟨h, hhS⟩
    rcases hreturn with ⟨hs, hh⟩ | ⟨hs, hh⟩
    · exact Or.inl ⟨by omega, by simpa only [ht] using hh⟩
    · exact Or.inr ⟨by omega, by simpa only [ht] using hh⟩
  have hmeet : ∀ w, (∃ q, A.Adj w q) → (∃ r, B.Adj w r) → w = h := by
    intro w ha hb
    have hw : w ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  exact prescribed_odd_cut_assembly A B D1 E1 h (Fintype.card S) (Fintype.card T)
    (card_cover_single_inter S T h hcover hinter) (by omega)
    (by rwa [heE ⟨h, hhT⟩]) hleft hmeet

/-- A fresh pendant on an actual cut side inherits the ambient cap away
from the prescribed hub and the other exception. The hub's restored even
neighbour contribution is counted in the ambient graph. -/
theorem prescribed_pendant_side_cap
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (h x : V) (hhS : h ∈ S)
    (hA : A.support ⊆ S)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hhEven : Even ((A ⊔ B).degree h))
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3) :
    ∀ w, Even ((pendantExtension (A.induce S) ⟨h, hhS⟩).degree w) →
      w ≠ .inl ⟨h, hhS⟩ →
      (∀ hxS : x ∈ S, w ≠ .inl ⟨x, hxS⟩) →
      eDegree (pendantExtension (A.induce S) ⟨h, hhS⟩) w ≤ 3 := by
  classical
  let J := A.induce S
  let K := pendantExtension J ⟨h, hhS⟩
  have hreflect (v : S) (hne : v.val ≠ h) (hp : ∃ w, J.Adj v w)
      (he : Even (J.degree v)) : Even ((A ⊔ B).degree v.val) := by
    obtain ⟨w, ha⟩ := hp
    have hz : B.neighborFinset v.val = ∅ := by
      ext q
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hb => hne (hmeet v.val ⟨w.val, ha⟩ ⟨q, hb⟩)
    have hd : (A ⊔ B).degree v.val = A.degree v.val := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup, hz]
      simp
    rw [hd]
    rwa [SimpleGraph.degree_induce_of_support_subset hA] at he
  intro w hw hwh hwx
  cases w with
  | inr u =>
    cases u
    exact ((Nat.not_even_iff_odd.mpr (pendantExtension_odd_new J ⟨h, hhS⟩)) hw).elim
  | inl v =>
    have hvh : v.val ≠ h := by
      intro he
      exact hwh (congrArg Sum.inl (Subtype.ext he))
    have hvx : v.val ≠ x := by
      intro he
      exact hwx (he ▸ v.property) (congrArg Sum.inl (Subtype.ext he))
    have hvhne : v ≠ ⟨h, hhS⟩ := fun he => hvh (congrArg Subtype.val he)
    have hvJ : Even (J.degree v) :=
      (pendantExtension_even_old_ne J ⟨h, hhS⟩ v hvhne).mp hw
    by_cases hp : ∃ q, J.Adj v q
    · let U := J.neighborFinset v |>.filter (fun q => Even ((A ⊔ B).degree q.val))
      have hsub : evenNeighbors K (.inl v) ⊆ U.map Function.Embedding.inl := by
        intro q hq
        obtain ⟨ha, he⟩ := (mem_evenNeighbors (G := K) (.inl v) q).mp hq
        cases q with
        | inr u =>
          cases u
          exact ((Nat.not_even_iff_odd.mpr (pendantExtension_odd_new J ⟨h, hhS⟩)) he).elim
        | inl q =>
          have haq : J.Adj v q := (pendantExtension_adj_old J ⟨h, hhS⟩ v q).mp ha
          have heq : Even ((A ⊔ B).degree q.val) := by
            by_cases hqh : q.val = h
            · rwa [hqh]
            · exact hreflect q hqh ⟨v, haq.symm⟩
                ((pendantExtension_even_old_ne J ⟨h, hhS⟩ q
                  (fun he => hqh (congrArg Subtype.val he))).mp he)
          exact Finset.mem_map.mpr ⟨q, Finset.mem_filter.mpr
            ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr haq, heq⟩, rfl⟩
      have hsubOld : U.map (Function.Embedding.subtype S) ⊆ evenNeighbors (A ⊔ B) v.val := by
        intro q hq
        obtain ⟨z, hzU, hzEq⟩ := Finset.mem_map.mp hq
        subst q
        obtain ⟨ha, he⟩ := Finset.mem_filter.mp hzU
        have haz : J.Adj v z := (SimpleGraph.mem_neighborFinset J v z).mp ha
        exact (mem_evenNeighbors v.val z.val).mpr
          ⟨Or.inl haz, he⟩
      have hle : eDegree K (.inl v) ≤ eDegree (A ⊔ B) v.val := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_le_card hsubOld
        simp only [Finset.card_map] at h1 h2
        exact h1.trans h2
      exact hle.trans (hcap v.val (hreflect v hvh hp hvJ) hvh hvx)
    · have hz : J.neighborFinset v = ∅ := by
        ext q
        simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
        exact fun ha => hp ⟨q, ha⟩
      have hd : J.degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, hz]
        rfl
      have hdK : K.degree (.inl v) = 0 := by
        rw [pendantExtension_degree_old_ne J ⟨h, hhS⟩ v hvhne, hd]
      have hb := eDegree_le_degree
        (G := pendantExtension (A.induce S) ⟨h, hhS⟩) (.inl v)
      have hdK' : (pendantExtension (A.induce S) ⟨h, hhS⟩).degree (.inl v) = 0 := hdK
      rw [hdK'] at hb
      omega

/-- The odd-local side's fresh-leaf endpoint decomposition is supplied by
vertex induction, or by the one-exception theorem when x is absent. -/
theorem prescribed_pendant_side_endpoint
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hhS : h ∈ S) (hhne : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hhOddA : Odd (A.degree h))
    (hhEven : Even ((A ⊔ B).degree h)) (hxEven : Even ((A ⊔ B).degree x))
    (hotherSize : 4 ≤ Fintype.card T)
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3)
    (hind : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) :
    BareConclusion (pendantExtension (A.induce S) ⟨h, hhS⟩) (.inl ⟨h, hhS⟩) := by
  classical
  let J := A.induce S
  let K := pendantExtension J ⟨h, hhS⟩
  have hm : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w ha hb
    have hw : w ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hcK : K.Connected := pendantExtension_connected J ⟨h, hhS⟩ hconnA
  have hpK : 0 < K.degree (.inl ⟨h, hhS⟩) := by
    rw [pendantExtension_degree_attach]
    omega
  have heK : Even (K.degree (.inl ⟨h, hhS⟩)) := by
    apply (pendantExtension_even_attach_iff J ⟨h, hhS⟩).mpr
    rwa [SimpleGraph.degree_induce_of_support_subset hA]
  have hsmall : Fintype.card (S ⊕ Unit) < Fintype.card V := by
    have hc := card_cover_single_inter S T h hcover hinter
    rw [Fintype.card_sum, Fintype.card_unit]
    omega
  have hcP := prescribed_pendant_side_cap A B S h x hhS hA hm hhEven hcap
  by_cases hxS : x ∈ S
  · have hxT : x ∉ T := by
      intro ht
      have hw : x ∈ S ∩ T := ⟨hxS, ht⟩
      have he : x = h := by simpa only [hinter, Set.mem_singleton_iff] using hw
      exact hhne he.symm
    have hz : B.neighborFinset x = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun hb => hxT (hB ⟨w, hb⟩)
    have hd : (A ⊔ B).degree x = A.degree x := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup, hz]
      simp
    have heX : Even (K.degree (.inl ⟨x, hxS⟩)) := by
      rw [pendantExtension_degree_old_ne J ⟨h, hhS⟩ ⟨x, hxS⟩
        (fun he => hhne (congrArg Subtype.val he).symm),
        SimpleGraph.degree_induce_of_support_subset hA, ← hd]
      exact hxEven
    apply hind (S ⊕ Unit) K hsmall hcK (.inl ⟨h, hhS⟩) (.inl ⟨x, hxS⟩)
      (fun he => hhne (congrArg Subtype.val (Sum.inl.inj he))) hpK heK heX
    intro w hw hwh hwx
    exact hcP w hw hwh (fun _ => hwx)
  · apply one_exception_endpoint K (.inl ⟨h, hhS⟩) hcK hpK heK
    intro w hw hwh
    exact hcP w hw hwh (fun hx => (hxS hx).elim)

/-- A connected one-exception graph supplies a ceiling decomposition with
a positive endpoint at every designated odd vertex, including when the
possible even exception is isolated. -/
theorem prescribed_one_exception_odd_budget
    (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V)
    (hc : G.Connected) (hh : Odd (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ w, Even (G.degree w) → w ≠ x → eDegree G w ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      0 < D.endpointCount h := by
  by_cases hp : 0 < G.degree x
  · obtain ⟨D, hd, _⟩ := one_exception_endpoint G x hc hp hx hcap
    exact ⟨D, hd, D.endpointCount_pos_of_odd_degree h hh⟩
  · apply floor_or_set_ceiling_endpoint_of_odd G h hc ?_ hh
    intro w hw
    by_cases he : w = x
    · subst w
      have hb := eDegree_le_degree (G := G) x
      omega
    · exact hcap w hw he

/-- The opposite odd-local cut side has its ceiling budget and a positive
hub endpoint from published inputs. The actual side cap is derived from
the ambient cap; oddness removes the prescribed hub as an exception. -/
theorem prescribed_actual_odd_right_budget
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hhT : h ∈ T) (hhne : h ≠ x)
    (hinter : S ∩ T = {h}) (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnB : (B.induce T).Connected) (hhOddB : Odd (B.degree h))
    (hhEven : Even ((A ⊔ B).degree h)) (hxEven : Even ((A ⊔ B).degree x))
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3) :
    ∃ E : Decomposition (B.induce T), E.size ≤ (Fintype.card T + 1) / 2 ∧
      0 < E.endpointCount ⟨h, hhT⟩ := by
  classical
  have hm : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w ha hb
    have hw : w ∈ S ∩ T := ⟨hA ha, hB hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using hw
  have hhOdd : Odd ((B.induce T).degree ⟨h, hhT⟩) := by
    rwa [SimpleGraph.degree_induce_of_support_subset hB]
  have hcP := bare_cap_induced_right A B T h h x hB hhEven hm hcap
  have hnotH (w : T) (hw : Even ((B.induce T).degree w)) : w.val ≠ h := by
    intro he
    have heq : w = ⟨h, hhT⟩ := Subtype.ext he
    rw [heq] at hw
    exact (Nat.not_even_iff_odd.mpr hhOdd) hw
  by_cases hxT : x ∈ T
  · have hxS : x ∉ S := by
      intro hs
      have hw : x ∈ S ∩ T := ⟨hs, hxT⟩
      have he : x = h := by simpa only [hinter, Set.mem_singleton_iff] using hw
      exact hhne he.symm
    have hz : A.neighborFinset x = ∅ := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact fun ha => hxS (hA ⟨w, ha⟩)
    have hd : (A ⊔ B).degree x = B.degree x := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup, hz]
      simp
    have heX : Even ((B.induce T).degree ⟨x, hxT⟩) := by
      rw [SimpleGraph.degree_induce_of_support_subset hB, ← hd]
      exact hxEven
    apply prescribed_one_exception_odd_budget (B.induce T) ⟨h, hhT⟩ ⟨x, hxT⟩
      hconnB hhOdd heX
    intro w hw hwx
    exact hcP w hw (hnotH w hw) (fun he => hwx (Subtype.ext he))
  · apply floor_or_set_ceiling_endpoint_of_odd (B.induce T) ⟨h, hhT⟩ hconnB ?_ hhOdd
    intro w hw
    exact hcP w hw (hnotH w hw) (fun he => hxT (he ▸ w.property))

/-- The genuine odd/odd cut branch with an opposite side of order at least
four closes from graph conditions and vertex induction alone. -/
theorem prescribed_actual_odd_cut
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h x : V) (hhS : h ∈ S) (hhT : h ∈ T) (hhne : h ≠ x)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (hA : A.support ⊆ S) (hB : B.support ⊆ T)
    (hconnA : (A.induce S).Connected) (hconnB : (B.induce T).Connected)
    (hhOddA : Odd (A.degree h)) (hhOddB : Odd (B.degree h))
    (hhEven : Even ((A ⊔ B).degree h)) (hxEven : Even ((A ⊔ B).degree x))
    (horderS : Odd (Fintype.card S)) (hotherSize : 4 ≤ Fintype.card T)
    (hcap : ∀ w, Even ((A ⊔ B).degree w) → w ≠ h → w ≠ x →
      eDegree (A ⊔ B) w ≤ 3)
    (hind : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      Fintype.card W < Fintype.card V → J.Connected →
      ∀ a b : W, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ w, Even (J.degree w) → w ≠ a → w ≠ b → eDegree J w ≤ 3) →
      BareConclusion J a) : BareConclusion (A ⊔ B) h := by
  obtain ⟨D, hd, hhD⟩ := prescribed_pendant_side_endpoint A B S T h x hhS hhne
    hcover hinter hA hB hconnA hhOddA hhEven hxEven hotherSize hcap hind
  obtain ⟨E, he, hhE⟩ := prescribed_actual_odd_right_budget A B S T h x hhT hhne
    hinter hA hB hconnB hhOddB hhEven hxEven hcap
  exact prescribed_actual_odd_cut_from_pendant A B S T h hhS hhT hcover hinter
    hA hB horderS D hd hhD E he (by omega)

end Gallai.TwoException
