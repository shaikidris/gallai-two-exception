/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPacket

@[expose] public section

/-! # Half-star reserve for odd contact packets -/

namespace Gallai.TwoException

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance halfContactAdj (u : V) (B : Finset V) :
    DecidableRel (G ⊔ B.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Odd contact cardinality turns the half-star rounding into the two-unit
reserve needed for the remaining outward restorations. The reserved edge is
not added by this operation. All positivity is checked in the current graph.
-/
theorem prepare_odd_contact_half_star
    (D : Decomposition G) (u v b : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hreserved : ¬ G.Adj u v)
    (hmissing : ∀ w ∈ S, ¬ G.Adj u w)
    (hpositive : ∀ w, G.Adj u w ∨ w ∈ S → 0 < D.endpointCount w)
    (hDu : 0 < D.endpointCount u) (hodd : Odd #S) (hb : b ∈ S) :
    ∃ B : Finset V, B ⊆ S ∧ b ∈ B ∧
      ∃ E : Decomposition (G ⊔ B.sup (SimpleGraph.edge u)),
        E.size = D.size ∧ #(S \ B) + 2 ≤ E.endpointCount u ∧
        ¬ (G ⊔ B.sup (SimpleGraph.edge u)).Adj u v ∧
        E.endpointCount v = D.endpointCount v ∧
        ∀ w, E.endpointCount w + (if w ∈ B then 1 else 0) =
          D.endpointCount w + if u = w then #B else 0 := by
  classical
  obtain ⟨B, hBS, hbB, hhalf, E, hsize, hvec⟩ :=
    D.prescribed_half_star_addibility u S hu hmissing hpositive b hb
  have huB : u ∉ B := fun h => hu (hBS h)
  have hvB : v ∉ B := fun h => hv (hBS h)
  have hEu : E.endpointCount u = D.endpointCount u + #B := by
    simpa only [huB, if_false, if_true, Nat.add_zero] using hvec u
  have hcard := Finset.card_sdiff_add_card_eq_card hBS
  have hround : #S + 1 ≤ 2 * #B := by
    rw [Nat.odd_iff] at hodd
    omega
  refine ⟨B, hBS, hbB, E, hsize, by omega, ?_, ?_, hvec⟩
  · intro hadj
    rcases hadj with hG | hB
    · exact hreserved hG
    · exact hvB ((star_sup_adj_center u B huB v).mp hB)
  · simpa only [hvB, huv, if_false, Nat.add_zero] using hvec v

/-- A pending leaf keeps its old neighbours after the half-star. Outside
two designated slots, untouched positive endpoints exclude passing vertices.
In windmill applications the slots are the hub and the private mate. -/
theorem contact_half_star_passing_le_two
    (D : Decomposition G) (u w : V) (S B K : Finset V)
    (hBS : B ⊆ S) (hu : u ∉ S) (hw : w ∈ S \ B) (hK : #K ≤ 2)
    (E : Decomposition (G ⊔ B.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ B then 1 else 0) =
      D.endpointCount t + if u = t then #B else 0)
    (hpositive : ∀ t, G.Adj w t → t ∉ K →
      t ≠ u ∧ t ∉ S ∧ 0 < D.endpointCount t) :
    passingNeighborCount E w ≤ 2 := by
  classical
  have hwu : w ≠ u := fun he => hu (he ▸ (Finset.mem_sdiff.mp hw).1)
  have hwB : w ∉ B := (Finset.mem_sdiff.mp hw).2
  have hsubset : {t ∈ (G ⊔ B.sup (SimpleGraph.edge u)).neighborFinset w |
      E.endpointCount t = 0} ⊆ K := by
    intro t ht
    obtain ⟨htAdj, htZero⟩ := Finset.mem_filter.mp ht
    have hadj := ((G ⊔ B.sup (SimpleGraph.edge u)).mem_neighborFinset w t).mp htAdj
    have hG : G.Adj w t := by
      rcases hadj with hG | hB
      · exact hG
      · exact False.elim (hwB ((star_sup_adj_off_center u B w t hwu).mp hB).1)
    by_contra htK
    obtain ⟨htu, htS, htPos⟩ := hpositive t hG htK
    have htB : t ∉ B := fun hb => htS (hBS hb)
    have he := hvec t
    simp only [htB, htu.symm, ite_false, Nat.add_zero, htZero] at he
    omega
  exact (Finset.card_le_card hsubset).trans hK

/-- Before delayed hub payment, a pending private can have only its mate
as a passing neighbour. The missing centre edge excludes the sole possible
new even vertex, and the retained hub is still exposed. -/
theorem pending_private_passing_le_one
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (D : Decomposition G) (u w x p : V)
    (hsub : G ≤ R) (hmissing : ¬ G.Adj w u)
    (hprofile : ∀ t, Even (G.degree t) → Even (R.degree t) ∨ t = u)
    (hpair : ∀ t, R.Adj w t → Even (R.degree t) → t = x ∨ t = p)
    (hx : 0 < D.endpointCount x) : passingNeighborCount D w ≤ 1 := by
  classical
  have hsubset : {t ∈ G.neighborFinset w | D.endpointCount t = 0} ⊆ {p} := by
    intro t ht
    obtain ⟨htAdj,htZero⟩ := Finset.mem_filter.mp ht
    have ha : G.Adj w t := (G.mem_neighborFinset w t).mp htAdj
    have he : Even (G.degree t) := by
      rw [Nat.even_iff]
      have hm := D.endpointCount_mod_two t
      rw [htZero] at hm
      omega
    rcases hprofile t he with he | rfl
    · rcases hpair t (hsub ha) he with rfl | rfl
      · omega
      · simp
    · exact False.elim (hmissing ha)
  have hc := Finset.card_le_card hsubset
  simpa only [passingNeighborCount, Finset.card_singleton] using hc

/-- In a tight failure profile, every private leaf with the delayed-payment
one-passing-neighbour bound must already have been selected inward. -/
theorem private_leaves_selected_of_tight_profile
    (D : Decomposition G) (S A K : Finset V) (hKS : K ⊆ S)
    (hprivate : ∀ t ∈ K, passingNeighborCount D t ≤ 1)
    (htight : ∀ t ∈ S \ A, passingNeighborCount D t = 2) : K ⊆ A := by
  intro t ht
  by_contra hn
  have hb := hprivate t ht
  have he := htight t (Finset.mem_sdiff.mpr ⟨hKS ht,hn⟩)
  omega

/-- Combining private selection with ordinary packet gain gives the exact
delayed-payment failure inequality, without replacing endpoint lower bounds
by equalities. K is the private leaf set and L the ordinary leaf set. -/
theorem delayed_packet_failure_count
    (K L A : Finset V) (d N epsilon : ℕ)
    (hdisjoint : Disjoint K L) (hA : A ⊆ K ∪ L) (hK : K ⊆ A)
    (htight : d + #A = #((K ∪ L) \ A) + 1)
    (hgain : #(L \ A) + N ≤ #(L ∩ A) + epsilon) :
    d + #K + N ≤ epsilon + 1 := by
  classical
  have hrepr : A = K ∪ (L ∩ A) := by
    ext t
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · intro ht
      rcases Finset.mem_union.mp (hA ht) with hk | hl
      · exact Or.inl hk
      · exact Or.inr ⟨hl,ht⟩
    · rintro (hk | ⟨_,ht⟩)
      · exact hK hk
      · exact ht
  have hd : Disjoint K (L ∩ A) := hdisjoint.mono_right Finset.inter_subset_left
  have hc : #A = #K + #(L ∩ A) := by
    exact (congrArg Finset.card hrepr).trans (Finset.card_union_of_disjoint hd)
  have hr : (K ∪ L) \ A = L \ A := by
    ext t
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨hk | hl,hn⟩
      · exact False.elim (hn (hK hk))
      · exact ⟨hl,hn⟩
    · rintro ⟨hl,hn⟩
      exact ⟨Or.inr hl,hn⟩
  rw [hr] at htight
  omega

/-- Original E-degree two gives the pending-private bound in any prepared
subgraph, provided its original odd neighbours retain positive endpoints.
Only original even contacts can lose endpoints in the half-star. -/
theorem contact_half_star_passing_of_original_even_cap
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (D : Decomposition G) (u w : V) (S B : Finset V)
    (hsub : G ≤ R) (hBS : B ⊆ S) (hu : u ∉ S)
    (hw : w ∈ S \ B) (hmissing : ¬ G.Adj w u)
    (hS : ∀ t ∈ S, Even (R.degree t)) (hcap : eDegree R w ≤ 2)
    (hoddpositive : ∀ t, G.Adj w t → Odd (R.degree t) → 0 < D.endpointCount t)
    (E : Decomposition (G ⊔ B.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ B then 1 else 0) =
      D.endpointCount t + if u = t then #B else 0) :
    passingNeighborCount E w ≤ 2 := by
  apply contact_half_star_passing_le_two D u w S B (evenNeighbors R w)
    hBS hu hw hcap E hvec
  intro t hadj htK
  have htEven : ¬ Even (R.degree t) := by
    intro he
    exact htK ((mem_evenNeighbors (G := R) w t).mpr ⟨hsub hadj, he⟩)
  refine ⟨?_, fun ht => htEven (hS t ht), ?_⟩
  · intro he
    exact hmissing (he ▸ hadj)
  · exact hoddpositive t hadj (Nat.not_even_iff_odd.mp htEven)

/-- Complete the odd contact sequence from its half-star witness. The
remaining leaf bound is stated on the actual intermediate decomposition;
windmill preparations must derive it before invoking this consumer. -/
theorem restore_odd_contact_sequence
    (D : Decomposition G) (u v b : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hreserved : ¬ G.Adj u v)
    (hmissing : ∀ w ∈ S, ¬ G.Adj u w)
    (hseparate : ∀ w ∈ S, ¬ G.Adj v w)
    (hpositive : ∀ w, G.Adj u w ∨ w ∈ S → 0 < D.endpointCount w)
    (hvpositive : ∀ w, G.Adj v w → 0 < D.endpointCount w)
    (hDu : 0 < D.endpointCount u) (hodd : Odd #S) (hb : b ∈ S)
    (hpassing : ∀ B : Finset V, B ⊆ S → b ∈ B →
      ∀ E : Decomposition (G ⊔ B.sup (SimpleGraph.edge u)),
        (∀ w, E.endpointCount w + (if w ∈ B then 1 else 0) =
          D.endpointCount w + if u = w then #B else 0) →
        ∀ w ∈ S \ B, passingNeighborCount E w ≤ 2) :
    ∃ F : Decomposition ((G ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u),
      F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  classical
  obtain ⟨B, hBS, hbB, E, hsize, hreserve, hmiss, hvcount, hvec⟩ :=
    prepare_odd_contact_half_star D u v b S hu hv huv hreserved
      hmissing hpositive hDu hodd hb
  have huB : u ∉ B := fun h => hu (hBS h)
  have hvB : v ∉ B := fun h => hv (hBS h)
  have P : ContactPacket E u v (S \ B) := by
    refine ⟨fun h => hu (Finset.mem_sdiff.mp h).1, huv,
      fun h => hv (Finset.mem_sdiff.mp h).1, ?_, hmiss, ?_,
      hpassing B hBS hbB E hvec, hreserve, ?_⟩
    · intro w hw hadj
      obtain ⟨hwS, hwB⟩ := Finset.mem_sdiff.mp hw
      rcases hadj with hG | hB
      · exact hmissing w hwS hG
      · exact hwB ((star_sup_adj_center u B huB w).mp hB)
    · intro w hw hadj
      rcases hadj with hG | hB
      · exact hseparate w (Finset.mem_sdiff.mp hw).1 hG
      · exact hvB ((star_sup_adj_off_center u B v w huv.symm).mp hB).1
    · intro w hadj
      rcases hadj with hG | hB
      · have hwu : u ≠ w := by
          intro he
          exact hreserved (he ▸ hG.symm)
        have hwS : w ∉ S := fun hw => hseparate w hw hG
        have hwB : w ∉ B := fun hw => hwS (hBS hw)
        have he := hvec w
        simp only [hwB, hwu, ite_false, Nat.add_zero] at he
        rw [he]
        exact hvpositive w hG
      · exact False.elim (hvB ((star_sup_adj_off_center u B v w huv.symm).mp hB).1)
  obtain ⟨F, hFsize, hFvec⟩ := restore_reserved_contact_packet E u v (S \ B) P
  have hFu : 1 ≤ F.endpointCount u := by
    have he := hFvec u
    have huR : u ∉ S \ B := fun h => hu (Finset.mem_sdiff.mp h).1
    simp only [huR, huv.symm, ite_false, ite_true, Nat.add_zero] at he
    omega
  have hFv : F.endpointCount v = D.endpointCount v + 1 := by
    have he := hFvec v
    have hvR : v ∉ S \ B := fun h => hv (Finset.mem_sdiff.mp h).1
    simpa only [huv, hvR, ite_false, ite_true, Nat.add_zero, hvcount] using he
  have hpreserve : ∀ t, t ≠ u → t ≠ v → t ∉ S →
      F.endpointCount t = D.endpointCount t := by
    intro t htu htv htS
    have htB : t ∉ B := fun ht => htS (hBS ht)
    have htR : t ∉ S \ B := fun ht => htS (Finset.mem_sdiff.mp ht).1
    have he := hvec t
    have hf := hFvec t
    simp only [htB, htR, htu.symm, htv.symm, ite_false, Nat.add_zero] at he hf
    exact hf.trans he
  have hgraph : ((G ⊔ B.sup (SimpleGraph.edge u)) ⊔
      (S \ B).sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u =
      (G ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u := by
    rw [sup_assoc G, ← Finset.sup_union, Finset.union_sdiff_of_subset hBS]
  have hout : ∃ F : Decomposition (((G ⊔ B.sup (SimpleGraph.edge u)) ⊔
      (S \ B).sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u),
      F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t :=
    ⟨F, hFsize.trans hsize, hFu, hFv, hpreserve⟩
  rwa [hgraph] at hout

/-- Graph-local two-slot data suffices for the complete contact sequence.
The prescribed leaf is exempt: it is necessarily restored inward, which
allows it to be the exceptional windmill hub in E3/E4. -/
theorem restore_odd_contact_sequence_of_two_slots
    (D : Decomposition G) (u v b : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hreserved : ¬ G.Adj u v)
    (hmissing : ∀ w ∈ S, ¬ G.Adj u w)
    (hseparate : ∀ w ∈ S, ¬ G.Adj v w)
    (hpositive : ∀ w, G.Adj u w ∨ w ∈ S → 0 < D.endpointCount w)
    (hvpositive : ∀ w, G.Adj v w → 0 < D.endpointCount w)
    (hDu : 0 < D.endpointCount u) (hodd : Odd #S) (hb : b ∈ S)
    (K : V → Finset V) (hK : ∀ w ∈ S, w ≠ b → #(K w) ≤ 2)
    (hlocal : ∀ w ∈ S, w ≠ b → ∀ t, G.Adj w t → t ∉ K w →
      t ≠ u ∧ t ∉ S ∧ 0 < D.endpointCount t) :
    ∃ F : Decomposition ((G ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u),
      F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  apply restore_odd_contact_sequence D u v b S hu hv huv hreserved
    hmissing hseparate hpositive hvpositive hDu hodd hb
  intro B hBS hbB E hvec w hw
  have hwS := (Finset.mem_sdiff.mp hw).1
  have hwb : w ≠ b := by
    intro he
    exact (Finset.mem_sdiff.mp hw).2 (he ▸ hbB)
  exact contact_half_star_passing_le_two D u w S B (K w) hBS hu hw
    (hK w hwS hwb) E hvec (hlocal w hwS hwb)

/-- Original private E-degree bounds and positive original odd neighbours
suffice for the whole restoration sequence. The prescribed hub contact is
exempt from the private degree bound. -/
theorem restore_odd_contact_sequence_of_original_even_cap
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (D : Decomposition G) (u v b : V) (S : Finset V)
    (hsub : G ≤ R) (hu : u ∉ S) (hv : v ∉ S) (huv : u ≠ v)
    (hreserved : ¬ G.Adj u v)
    (hmissing : ∀ w ∈ S, ¬ G.Adj u w)
    (hseparate : ∀ w ∈ S, ¬ G.Adj v w)
    (hpositive : ∀ w, G.Adj u w ∨ w ∈ S → 0 < D.endpointCount w)
    (hvpositive : ∀ w, G.Adj v w → 0 < D.endpointCount w)
    (hDu : 0 < D.endpointCount u) (hodd : Odd #S) (hb : b ∈ S)
    (hS : ∀ w ∈ S, Even (R.degree w))
    (hcap : ∀ w ∈ S, w ≠ b → eDegree R w ≤ 2)
    (hoddpositive : ∀ w ∈ S, w ≠ b → ∀ t,
      G.Adj w t → Odd (R.degree t) → 0 < D.endpointCount t) :
    ∃ F : Decomposition ((G ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u),
      F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      ∀ t, t ≠ u → t ≠ v → t ∉ S → F.endpointCount t = D.endpointCount t := by
  apply restore_odd_contact_sequence D u v b S hu hv huv hreserved
    hmissing hseparate hpositive hvpositive hDu hodd hb
  intro B hBS hbB E hvec w hw
  have hwS := (Finset.mem_sdiff.mp hw).1
  have hwb : w ≠ b := by
    intro he
    exact (Finset.mem_sdiff.mp hw).2 (he ▸ hbB)
  exact contact_half_star_passing_of_original_even_cap R D u w S B
    hsub hBS hu hw (fun h => hmissing w hwS h.symm) hS
    (hcap w hwS hwb) (hoddpositive w hwS hwb) E hvec

/-- The half-star endpoint vector preserves the original-even profile
away from the centre. Selected leaves are originally even; all other
noncentral vertices retain their endpoint parity. -/
theorem contact_half_star_even_profile
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (D : Decomposition G) (u : V) (S A : Finset V) (hAS : A ⊆ S)
    (hS : ∀ t ∈ S, Even (R.degree t))
    (hprofile : ∀ t, Even (G.degree t) → Even (R.degree t) ∨ t = u)
    (E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0) :
    ∀ t, Even ((G ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (R.degree t) ∨ t = u := by
  intro t ht
  by_cases htu : t = u
  · exact Or.inr htu
  by_cases htA : t ∈ A
  · exact Or.inl (hS t (hAS htA))
  have hv := hvec t
  simp only [htA,Ne.symm htu,ite_false,Nat.add_zero] at hv
  have hE := E.endpointCount_mod_two t
  have hD := D.endpointCount_mod_two t
  have htG : Even (G.degree t) := by
    rw [Nat.even_iff] at ht ⊢
    omega
  exact hprofile t htG

/-- The delayed private bound is derived for the actual half-star,
including its subgraph, missing-centre and exposed-hub guards. -/
theorem delayed_half_star_private_bound
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (D : Decomposition G) (u x w p : V) (S A : Finset V)
    (hAS : A ⊆ S) (huS : u ∉ S) (hxS : x ∉ S) (hxu : x ≠ u)
    (hsub : G ≤ R) (hadj : ∀ t ∈ S, R.Adj u t)
    (hS : ∀ t ∈ S, Even (R.degree t))
    (hprofile : ∀ t, Even (G.degree t) → Even (R.degree t) ∨ t = u)
    (hmissing : ∀ t ∈ S, ¬ G.Adj u t)
    (hw : w ∈ S \ A)
    (hpair : ∀ t, R.Adj w t → Even (R.degree t) → t = x ∨ t = p)
    (hx : 0 < D.endpointCount x)
    (E : Decomposition (G ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0) :
    passingNeighborCount E w ≤ 1 := by
  classical
  have huA : u ∉ A := fun ht => huS (hAS ht)
  have hxA : x ∉ A := fun ht => hxS (hAS ht)
  have hsubE : G ⊔ A.sup (SimpleGraph.edge u) ≤ R := by
    apply sup_le hsub
    apply Finset.sup_le
    intro t ht v z hvz
    rw [SimpleGraph.edge_adj] at hvz
    rcases hvz.1 with ⟨hv,hz⟩ | ⟨hv,hz⟩
    · rw [hv,hz]
      exact hadj t (hAS ht)
    · rw [hv,hz]
      exact (hadj t (hAS ht)).symm
  have hmissingE : ¬ (G ⊔ A.sup (SimpleGraph.edge u)).Adj w u := by
    rintro (hG | hA)
    · exact hmissing w (Finset.mem_sdiff.mp hw).1 hG.symm
    · exact (Finset.mem_sdiff.mp hw).2
        ((star_sup_adj_center u A huA w).mp hA.symm)
  have hxE : 0 < E.endpointCount x := by
    have hv := hvec x
    simp only [hxA,hxu.symm,ite_false,Nat.add_zero] at hv
    omega
  exact pending_private_passing_le_one R E u w x p hsubE hmissingE
    (contact_half_star_even_profile R D u S A hAS hS hprofile E hvec) hpair hxE

end Gallai.TwoException
