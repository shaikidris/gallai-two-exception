/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE3Budget

@[expose] public section

/-! # Native joint budget for a spoke and a private mate deletion -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longE5Adj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- E5 deletes one hub spoke and a disjoint private mate edge. The odd
hub, joint boundary caps and surviving private spoke are derived from the
actual packet, while the ordinary preparation is retained for reconstruction. -/
theorem bare_long_E5_auxiliary_endpoint
    (h u v : V) (x s p q : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (hsC : s ∈ C.supp)
    (hpC : p ∈ C.supp) (hqC : q ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∉ S) (hsS : (s : V) ∉ S)
    (hpS : (p : V) ∉ S) (hqS : (q : V) ∉ S)
    (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hxs : G.Adj x s) (hqp : G.Adj q p)
    (hpx : (p : V) ≠ (x : V)) (hps : (p : V) ≠ (s : V))
    (hqx : (q : V) ≠ (x : V)) (hqs : (q : V) ≠ (s : V))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (x : V) ∨ t = (s : V) ∨ t = (q : V) ∨ t = (p : V)) :
    ∃ B : Finset V, ∃ O : List (V × V),
      (∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
        t ∉ Subtype.val '' C.supp) ∧
      O.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
        e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
        e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp) ∧
      (∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
        t ∈ B ∨ ∃ e ∈ O, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
        (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
        Z.supp = {a,b,c} ∧ (a : V) ∈ B) ∧
      Nonempty (OrdinaryRegularPacketData G h x v B O) ∧
      ∃ D : Decomposition (ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) [((q : V),(p : V)),((x : V),(s : V))]),
        D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  let N : List (V × V) := [((q : V),(p : V)),((x : V),(s : V))]
  have hNC : ∀ e ∈ N, e.1 ∈ Subtype.val '' C.supp ∧ e.2 ∈ Subtype.val '' C.supp := by
    intro e he
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact ⟨⟨q,hqC,rfl⟩,⟨p,hpC,rfl⟩⟩
    · exact ⟨⟨x,hxC,rfl⟩,⟨s,hsC,rfl⟩⟩
  obtain ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,hQ,hdu,hdh,hcenterQ,hwind,hOrd⟩ :=
    bare_long_native_ordinary_boundary_bounds h u v x H C hxC huOdd hvOdd huv
      hsep S N hSodd hS hNC
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let J := ordinaryMatePuncture (starPuncture Q u (insert v S)) N
  have hQE : Q ≤ G := (ordinaryMatePuncture_le O).trans (fun _ _ ht => ht.1)
  have hsub : J ≤ G := (ordinaryMatePuncture_le N).trans
    ((show starPuncture Q u (insert v S) ≤ Q from fun _ _ ht => ht.1).trans hQE)
  have hSE : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t) := by
    intro t ht
    obtain ⟨w,_,rfl⟩ := (hS t ht).2
    exact ⟨(hS w ht).1,w.property⟩
  have hOE : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).2.1,(hO e he).2.2.1⟩
  have hNE : ∀ e ∈ N, Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact ⟨q.property,p.property⟩
    · exact ⟨x.property,s.property⟩
  have hprofile := (long_joint_original_parity_profile u v B S O N huOdd hvOdd huv
    (fun t ht => (hB t ht).2.1) hOE hSE hSodd hNE).1
  have huS : u ∉ S := fun ht => G.irrefl (hS u ht).1
  have huI : u ∉ insert v S := by simp [huv.ne,huS]
  have hxu : (x : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ x.property)
  have hxv : (x : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ x.property)
  have hqu : (q : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ q.property)
  have hqv : (q : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ q.property)
  have hpu : (p : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ p.property)
  have hpv : (p : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ p.property)
  have hsu : (s : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ s.property)
  have hsv : (s : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ s.property)
  have hNdis : N.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by simp [N,hpx,hps,hqx,hqs]
  have hNavoid : ∀ e ∈ N, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ insert v S ∧ e.2 ∉ insert v S := by
    intro e he
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact ⟨hqu,hpu,by simp [hqv,hqS],by simp [hpv,hpS]⟩
    · exact ⟨hxu,hsu,by simp [hxv,hxS],by simp [hsv,hsS]⟩
  have hNQ : ∀ e ∈ N, Q.Adj e.1 e.2 ∧ Even (Q.degree e.1) ∧ Even (Q.degree e.2) := by
    intro e he
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · refine ⟨((hwind q ⟨q,hqC,rfl⟩).2 p).mpr hqp,?_,?_⟩
      · rw [(hwind q ⟨q,hqC,rfl⟩).1]; exact q.property
      · rw [(hwind p ⟨p,hpC,rfl⟩).1]; exact p.property
    · refine ⟨((hwind x ⟨x,hxC,rfl⟩).2 s).mpr hxs,?_,?_⟩
      · rw [(hwind x ⟨x,hxC,rfl⟩).1]; exact x.property
      · rw [(hwind s ⟨s,hsC,rfl⟩).1]; exact s.property
  have hQS : ∀ t ∈ S, Q.Adj u t ∧ Even (Q.degree t) := by
    intro t ht
    exact ⟨((hwind t (hS t ht).2).2 u).mpr (hS t ht).1.symm |>.symm,
      by rw [(hwind t (hS t ht).2).1]; exact (hSE t ht).2⟩
  have hmates := ordinary_star_mates_endpoints_odd (G := Q) u (insert v S) N hNdis hNavoid hNQ
  have hxOdd : Odd (J.degree x) :=
    long_joint_covered_hub_odd (G := Q) u v x S N hQS hNdis hNavoid hNQ
      (Or.inr ⟨((x : V),(s : V)),by simp [N],Or.inl rfl⟩)
  have hcenter : ∀ t, J.Adj v t → Even (J.degree t) → t = h :=
    long_joint_reserved_center_inherited (G := Q) h u v S N huS huv.ne
      (fun t ht hvt => hsep t (hS t ht).2 (hQE hvt))
      (fun e he => ⟨fun ha => hsep e.1 (hNC e he).1 (hQE ha),
        fun ha => hsep e.2 (hNC e he).2 (hQE ha)⟩) hcenterQ
  have huCap : eDegree J u = 0 := by
    apply long_joint_contact_center_eDegree_zero u v S N J hsub hprofile
    · intro ha
      exact starPuncture_missing Q u (insert v S) huI v (Finset.mem_insert_self _ _)
        ((ordinaryMatePuncture_le N) ha)
    · intro t ht ha
      exact starPuncture_missing Q u (insert v S) huI t (Finset.mem_insert_of_mem ht)
        ((ordinaryMatePuncture_le N) ha)
    · exact hmates
    · intro t hut he
      rcases hcontacts t hut he with ht | rfl | rfl | rfl | rfl
      · exact Or.inl ht
      · exact Or.inr ⟨((x : V),(s : V)),by simp [N],Or.inl rfl⟩
      · exact Or.inr ⟨((x : V),(s : V)),by simp [N],Or.inr rfl⟩
      · exact Or.inr ⟨((q : V),(p : V)),by simp [N],Or.inl rfl⟩
      · exact Or.inr ⟨((q : V),(p : V)),by simp [N],Or.inr rfl⟩
  have hprivate : ∀ t ∈ Subtype.val '' C.supp, t ≠ (x : V) → eDegree J t ≤ 1 := by
    intro t ht htx
    obtain ⟨a,ha,rfl⟩ := ht
    have hax : (evenSubgraph G).Adj x a :=
      ((bare_windmill h x H C hxC).1 a).mp ha |>.resolve_left
        (fun hh => htx (congrArg Subtype.val hh))
    apply private_eDegree_le_one_of_odd_hub_except_centre v x a hsub hprofile
      x.property hxOdd hax.symm (bare_hub_private_eDegree_eq_two h x a H hax.reachable htx)
    exact fun hav => hsep a ⟨a,ha,rfl⟩ (hsub hav).symm
  have hwExists : ∃ w ∈ evenNeighbors G x,
      w ≠ (q : V) ∧ w ≠ (p : V) ∧ w ≠ (s : V) := by
    by_contra hn
    push Not at hn
    have hs : evenNeighbors G x ⊆ {(q : V),(p : V),(s : V)} := by
      intro w hw
      by_cases hwq : w = (q : V)
      · simp [hwq]
      · by_cases hwp : w = (p : V)
        · simp [hwp]
        · have hws := hn w hw hwq hwp
          simp [hws]
    have hc := Finset.card_le_card hs
    have hb : #({(q : V),(p : V),(s : V)} : Finset V) ≤ 3 := by
      calc
        _ ≤ #({(p : V),(s : V)} : Finset V) + 1 := Finset.card_insert_le _ _
        _ ≤ (#({(s : V)} : Finset V) + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp
    have hxgt := H.counterexample.exception_gt_three
    change #(evenNeighbors G x) > 3 at hxgt
    omega
  obtain ⟨w,hw,hwq,hwp,hws⟩ := hwExists
  obtain ⟨hxw,hwEven⟩ := (mem_evenNeighbors (G := G) x w).mp hw
  let we : evenVertices G := ⟨w,hwEven⟩
  have hwC : we ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxw
  have hxwQ : Q.Adj x w := ((hwind x ⟨x,hxC,rfl⟩).2 w).mpr hxw
  have hwu : w ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ hwEven)
  have hxwStar : (starPuncture Q u (insert v S)).Adj x w := by
    refine ⟨hxwQ,?_⟩
    intro hs
    exact hwu ((star_sup_adj_off_center u (insert v S) x w hxu).mp hs).2
  have hxwJ : J.Adj x w := by
    apply ((ordinaryMatePuncture_adj_of_avoids (G := starPuncture Q u (insert v S)) N w x
      (by
        intro e he
        simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hwq,hwp⟩
        · exact ⟨hxw.ne.symm,hws⟩)).mpr
      hxwStar.symm).symm
  have hhu : h ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hhx : h ≠ (x : V) := H.counterexample.1.2.1
  have hhq : h ≠ (q : V) := by
    intro hh
    have hm : (p : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h p).mpr ⟨hh.symm ▸ hqp,p.property⟩
    have hz := H.counterexample.1.2.2.2.2.2.1
    have hc := Finset.card_pos.mpr ⟨(p : V),hm⟩
    change 0 < eDegree G h at hc
    omega
  have hhp : h ≠ (p : V) := by
    intro hh
    have hm : (q : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h q).mpr ⟨hh.symm ▸ hqp.symm,q.property⟩
    have hz := H.counterexample.1.2.2.2.2.2.1
    have hc := Finset.card_pos.mpr ⟨(q : V),hm⟩
    change 0 < eDegree G h at hc
    omega
  have hhs : h ≠ (s : V) := by
    intro hh
    have hm : (x : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h x).mpr ⟨hh.symm ▸ hxs.symm,x.property⟩
    have hz := H.counterexample.1.2.2.2.2.2.1
    have hc := Finset.card_pos.mpr ⟨(x : V),hm⟩
    change 0 < eDegree G h at hc
    omega
  have hhdegree : J.degree h = G.degree h :=
    ((long_ordinary_preparation_unchanged (G := Q) u h (insert v S) N hhu
      (by simp [hhv,hhS]) (by
        intro e he
        simp only [N,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hhq,hhp⟩
        · exact ⟨hhx,hhs⟩)).1).trans hdh
  refine ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,?_⟩
  apply bare_long_joint_endpoint_budget h u v x H B S O N hprofile hhdegree hxOdd hcenter
  refine ⟨?_,hOrd.1,?_,hOrd.2,?_,⟨w,hxwJ,hprivate w ⟨we,hwC,rfl⟩ hxw.ne.symm⟩⟩
  · change eDegree J u ≤ 1
    rw [huCap]; decide
  · intro t ht
    by_cases htx : t = (x : V)
    · exact Or.inl htx
    · exact Or.inr (hprivate t (hS t ht).2 htx)
  · intro e he t ht
    rcases ht with rfl | rfl
    · by_cases htx : e.1 = (x : V)
      · exact Or.inl htx
      · exact Or.inr (hprivate e.1 (hNC e he).1 htx)
    · by_cases htx : e.2 = (x : V)
      · exact Or.inl htx
      · exact Or.inr (hprivate e.2 (hNC e he).2 htx)

end Gallai.TwoException
