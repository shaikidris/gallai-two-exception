/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongNativeOrdinaryBounds
public import Gallai.TwoException.BareLongJointBudget

@[expose] public section

/-! # Native joint auxiliary budget for the hub-selected contact row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longE3Adj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- The hub-selected odd contact star has a native endpoint-rich joint
auxiliary budget. The ordinary preparation is chosen inside the proof;
no auxiliary cap, parity certificate, component budget or decomposition is
assumed. This is the E3 budget, not yet its reconstruction to G. -/
theorem bare_long_E3_auxiliary_endpoint
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∈ S) (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ S) :
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
          u (insert v S)) []),
        D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  obtain ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,hQ,hdu,hdh,hcenterQ,hwind,hOrd⟩ :=
    bare_long_native_ordinary_boundary_bounds h u v x H C hxC huOdd hvOdd huv
      hsep S [] hSodd hS (by simp)
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let J := ordinaryMatePuncture (starPuncture Q u (insert v S)) []
  have hQE : Q ≤ G := (ordinaryMatePuncture_le O).trans (fun _ _ ht => ht.1)
  have hsub : J ≤ G := (ordinaryMatePuncture_le []).trans
    ((show starPuncture Q u (insert v S) ≤ Q from fun _ _ ht => ht.1).trans hQE)
  have hSE : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t) := by
    intro t ht
    obtain ⟨w,hw,hwt⟩ := (hS t ht).2
    exact ⟨(hS t ht).1,hwt ▸ w.property⟩
  have hOE : ∀ e ∈ O, Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).2.1,(hO e he).2.2.1⟩
  have hprofile := (long_joint_original_parity_profile u v B S O [] huOdd hvOdd huv
    (fun t ht => (hB t ht).2.1) hOE hSE hSodd (by simp)).1
  have huS : u ∉ S := fun ht => G.irrefl (hS u ht).1
  have huI : u ∉ insert v S := by simp [huv.ne,huS]
  have hxQEven : Even (Q.degree x) := by
    rw [(hwind x ⟨x,hxC,rfl⟩).1]
    exact x.property
  have hxOdd : Odd (J.degree x) := long_joint_selected_leaf_odd u v x S [] hxS
    ((hwind x ⟨x,hxC,rfl⟩).2 u |>.mpr (hS x hxS).1.symm).symm hxQEven (by simp)
  have hcenter : ∀ t, J.Adj v t → Even (J.degree t) → t = h :=
    long_joint_reserved_center_inherited (G := Q) h u v S [] huS huv.ne
      (fun t ht hvt => hsep t (hS t ht).2 (hQE hvt)) (by simp) hcenterQ
  have huCap : eDegree J u = 0 := by
    apply long_joint_contact_center_eDegree_zero u v S [] J hsub hprofile
    · exact starPuncture_missing Q u (insert v S) huI v (Finset.mem_insert_self _ _)
    · intro t ht
      exact starPuncture_missing Q u (insert v S) huI t (Finset.mem_insert_of_mem ht)
    · simp
    · intro t hut he
      exact Or.inl (hcontacts t hut he)
  have hprivate : ∀ t ∈ Subtype.val '' C.supp, t ≠ (x : V) → eDegree J t ≤ 1 := by
    intro t ht htx
    obtain ⟨a,ha,rfl⟩ := ht
    have hax : (evenSubgraph G).Adj x a :=
      ((bare_windmill h x H C hxC).1 a).mp ha |>.resolve_left
        (fun hh => htx (congrArg Subtype.val hh))
    apply private_eDegree_le_one_of_odd_hub_except_centre v x a hsub hprofile
      x.property hxOdd hax.symm
      (bare_hub_private_eDegree_eq_two h x a H hax.reachable htx)
    exact fun hav => hsep a ⟨a,ha,rfl⟩ (hsub hav).symm
  have hxpos : 0 < eDegree G x := by
    have hh := H.counterexample.exception_gt_three
    omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hxpos
  obtain ⟨hxp,hpEven⟩ := (mem_evenNeighbors (G := G) x p).mp hp
  let pe : evenVertices G := ⟨p,hpEven⟩
  have hpC : pe ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxp
  have hxpQ : Q.Adj x p := ((hwind x ⟨x,hxC,rfl⟩).2 p).mpr hxp
  have hxu : (x : V) ≠ u := fun hh =>
    (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ x.property)
  have hpu : p ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ hpEven)
  have hxpJ : J.Adj x p := by
    refine ⟨hxpQ,?_⟩
    intro hs
    exact hpu ((star_sup_adj_off_center u (insert v S) x p hxu).mp hs).2
  have hhu : h ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  have hhI : h ∉ insert v S := by simp [hhv,hhS]
  have hhdegree : J.degree h = G.degree h :=
    ((long_ordinary_preparation_unchanged (G := Q) u h (insert v S) []
      hhu hhI (by simp)).1).trans hdh
  refine ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,?_⟩
  apply bare_long_joint_endpoint_budget h u v x H B S O [] hprofile hhdegree hxOdd hcenter
  refine ⟨?_,hOrd.1,?_,hOrd.2,by simp,?_⟩
  · change eDegree J u ≤ 1
    rw [huCap]
    decide
  · intro t ht
    by_cases htx : t = (x : V)
    · exact Or.inl htx
    · exact Or.inr (hprivate t (hS t ht).2 htx)
  · exact ⟨p,hxpJ,hprivate p ⟨pe,hpC,rfl⟩ hxp.ne.symm⟩

end Gallai.TwoException
