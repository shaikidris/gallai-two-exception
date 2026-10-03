/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE12Budget
public import Gallai.TwoException.BareLongOrdinaryRestore
public import Gallai.TwoException.ContactE2

@[expose] public section

/-! # Complete reconstruction for the two hub-spoke deletion rows -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longE12RestoreAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Both E1 and E2 reconstruct by restoring xq towards q first. The
restoration needs no adjacency between u and q, so the single-contact and
double-contact packets share this consumer. The auxiliary decomposition,
all positivity guards and the final ordinary restoration are constructed
inside the proof. -/
theorem bare_long_E12_endpoint
    (h u v : V) (x q : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (hqC : q ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∉ S) (hqS : (q : V) ∉ S)
    (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hxq : G.Adj x q)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (x : V) ∨ t = (q : V))
    (p : V) (hp : p ∈ S) (hux : ¬ G.Adj u x)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = (x : V) ∨ t = p) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h := by
  classical
  obtain ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,⟨R⟩,D,hsize,hhD⟩ :=
    bare_long_E12_auxiliary_endpoint h u v x q H C hxC hqC huOdd hvOdd huv
      hsep S hxS hqS hhS hSodd hS hxq hcontacts
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let N : List (V × V) := [((x : V),(q : V))]
  let J0 := starPuncture Q u (insert v S)
  let J := ordinaryMatePuncture J0 N
  have hadj := fun t ht => (hB t ht).1
  have hEven := fun t ht => (hB t ht).2.1
  have hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).1,(hO e he).2.1,(hO e he).2.2.1⟩
  have havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hedges e he).2.1),fun hh => hn (hh ▸ (hedges e he).2.2),
      (hO e he).2.2.2.1,(hO e he).2.2.2.2.1⟩
  have hprof := ordinary_star_mates_even_preserved v B O hadj hEven hdis havoid hedges
  have hsub : Q ≤ G := (ordinaryMatePuncture_le O).trans (fun _ _ ht => ht.1)
  have hwind := long_ordinary_preparation_windmill_unchanged v hvOdd C B O
    (fun t ht => (hB t ht).2.2.2)
    (fun e he => ⟨(hO e he).2.2.2.2.2.2.2.1,(hO e he).2.2.2.2.2.2.2.2⟩)
  obtain ⟨hQ,hdu,_⟩ := long_ordinary_preparation_reserved_degree u v B O huOdd hvOdd huv
    (fun t ht => ⟨hadj t ht,hEven t ht⟩) (fun e he => (hedges e he).2)
  have huQOdd : Odd (Q.degree u) := by rw [hdu]; exact huOdd
  have huS : u ∉ S := fun ht => G.irrefl (hS u ht).1
  have hvS : v ∉ S := by
    intro ht
    obtain ⟨a,_,ha⟩ := (hS v ht).2
    exact (Nat.not_even_iff_odd.mpr hvOdd) (ha ▸ a.property)
  have hSE : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t) := by
    intro t ht
    obtain ⟨a,_,rfl⟩ := (hS t ht).2
    exact ⟨(hS a ht).1,a.property⟩
  have hQS : ∀ t ∈ S, Q.Adj u t ∧ Even (Q.degree t) := by
    intro t ht
    refine ⟨((hwind t (hS t ht).2).2 u).mpr (hS t ht).1.symm |>.symm,?_⟩
    rw [(hwind t (hS t ht).2).1]
    exact (hSE t ht).2
  have hcap : ∀ t ∈ S, eDegree Q t ≤ 2 := by
    intro t ht
    have htx : t ≠ (x : V) := fun he => hxS (he ▸ ht)
    obtain ⟨a,ha,haval⟩ := (hS t ht).2
    have hax : (evenSubgraph G).Adj x a :=
      ((bare_windmill h x H C hxC).1 a).mp ha |>.resolve_left
        (fun hh => htx ((congrArg Subtype.val hh).symm.trans haval).symm)
    have hd : eDegree G t = 2 := by
      rw [← haval]
      exact bare_hub_private_eDegree_eq_two h x a H hax.reachable
        (fun hh => htx (haval.symm.trans hh))
    have hs : evenNeighbors Q t ⊆ evenNeighbors G t := by
      intro w hw
      obtain ⟨htw,he⟩ := (mem_evenNeighbors (G := Q) t w).mp hw
      rcases hprof w he with heG | rfl
      · exact (mem_evenNeighbors (G := G) t w).mpr ⟨hsub htw,heG⟩
      · exact False.elim (hsep t (hS t ht).2 (hsub htw).symm)
    exact (Finset.card_le_card hs).trans_eq hd
  have hc : ∀ t, G.Adj v t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ O, t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hvt he
    by_cases hth : t = h
    · exact Or.inr (Or.inr hth)
    · rcases hvcontacts t hvt he hth with hb | ho
      · exact Or.inl hb
      · exact Or.inr (Or.inl ho)
  have hcenterQ := (bare_long_ordinary_preparation_cap h v x H B O
    hadj hEven hdis havoid hedges hc).2.2.2
  have hcenter : ∀ t, J.Adj v t → Even (J.degree t) → t = h :=
    long_joint_reserved_center_inherited (G := Q) h u v S N huS huv.ne
      (fun t ht hvt => hsep t (hS t ht).2 (hsub hvt))
      (by
        intro e he
        simp only [N,List.mem_singleton] at he
        subst e
        exact ⟨fun ha => hsep x ⟨x,hxC,rfl⟩ (hsub ha),
          fun ha => hsep q ⟨q,hqC,rfl⟩ (hsub ha)⟩) hcenterQ
  have hxu : (x : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ x.property)
  have hxv : (x : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ x.property)
  have hqu : (q : V) ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ q.property)
  have hqv : (q : V) ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ q.property)
  have hvpositive : ∀ t, J0.Adj v t → 0 < D.endpointCount t := by
    intro t hvt
    have hJvt : J.Adj v t := (ordinaryMatePuncture_adj_of_avoids (G := J0) N v t
      (by intro e he; simp only [N,List.mem_singleton] at he; subst e; exact ⟨hxv.symm,hqv.symm⟩)).mpr hvt
    rcases Nat.even_or_odd (J.degree t) with he | ho
    · have hth := hcenter t hJvt he
      subst t; omega
    · exact D.endpointCount_pos_of_odd_degree t ho
  have hNE : ∀ e ∈ N, Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    simp only [N,List.mem_singleton] at he
    subst e; exact ⟨x.property,q.property⟩
  have hdv := (long_joint_original_parity_profile u v B S O N huOdd hvOdd huv
    hEven (fun e he => (hedges e he).2) hSE hSodd hNE).2.2
  have hdvJ : J.degree v + 1 = Q.degree v := by
    simpa only [J,J0,Q,N,← SimpleGraph.ncard_neighborSet] using hdv
  have hretained : ∀ t, Q.Adj u t → t ∉ S → t ≠ (q : V) →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS htq
    rcases Nat.even_or_odd (Q.degree t) with he | ho
    · have htv : t = v := by
        rcases hprof t he with heG | htv
        · rcases hcontacts t (hsub hut) heG with ht | rfl | rfl
          · exact False.elim (htS ht)
          · exact False.elim (hux (hsub hut))
          · exact False.elim (htq rfl)
        · exact htv
      subst t
      have hoJ : Odd (J.degree v) := by
        simp only [← SimpleGraph.ncard_neighborSet] at hdvJ he ⊢
        rw [Nat.even_iff] at he
        rw [Nat.odd_iff]
        omega
      exact Or.inr (D.endpointCount_pos_of_odd_degree v hoJ)
    · exact Or.inl ho
  have hxQE : Even (Q.degree x) := by rw [(hwind x ⟨x,hxC,rfl⟩).1]; exact x.property
  have hqQE : Even (Q.degree q) := by rw [(hwind q ⟨q,hqC,rfl⟩).1]; exact q.property
  have hpairQ : ∀ t, Q.Adj q t → Even (Q.degree t) → t = (x : V) ∨ t = p := by
    intro t hqt he
    rcases hprof t he with heG | rfl
    · exact hpair t (hsub hqt) heG
    · exact False.elim (hsep q ⟨q,hqC,rfl⟩ (hsub hqt).symm)
  have hhu : h ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hhx : h ≠ (x : V) := H.counterexample.1.2.1
  have hhq : h ≠ (q : V) := by
    intro hh
    have hm : (x : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors (G := G) h x).mpr ⟨hh.symm ▸ hxq.symm,x.property⟩
    have hz := H.counterexample.1.2.2.2.2.2.1
    have hp := Finset.card_pos.mpr ⟨(x : V),hm⟩
    change 0 < eDegree G h at hp
    omega
  obtain ⟨F,hFD,_,hFv,hFh⟩ := restore_contact_E2 (R := Q) u v x p q h S
    huS hvS huv.ne huQOdd hSodd hQ (fun t ht => (hQS t ht).1)
    (fun t ht => (hQS t ht).2) hp (fun t ht _ => hcap t ht)
    (fun t ht ha => hsep t (hS t ht).2 (hsub ha)) hxu hxv hxS hqu hqv hqS
    (((hwind x ⟨x,hxC,rfl⟩).2 q).mpr hxq) hxQE hqQE
    (fun ha => hsep q ⟨q,hqC,rfl⟩ (hsub ha).symm) hpairQ
    (fun ha => hsep x ⟨x,hxC,rfl⟩ (hsub ha)) (fun ha => hux (hsub ha))
    hhu hhv hhx hhq hhS D hretained hvpositive
  obtain ⟨E,hEF,hEh⟩ := bare_long_restore_ordinary_preparation h v x H hvOdd C B O
    hB hdis hO hvcontacts hpacket R F (by omega) (by rw [hFh]; exact hhD)
  refine ⟨E,?_,hEh⟩
  rw [hEF,hFD]
  exact hsize

end Gallai.TwoException
