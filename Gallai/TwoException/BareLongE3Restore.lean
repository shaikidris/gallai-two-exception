/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongE3Budget
public import Gallai.TwoException.ContactE3

@[expose] public section

/-! # First-side reconstruction for the long-corridor E3 row -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longE3RestoreAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore the first contact star and reserved edge in the actual
ordinary-prepared graph. All half-star and reserved-neighbour conditions
are derived from the native preparation labels and h's endpoint reserve. -/
theorem bare_long_E3_restore_first_side
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (hxS : (x : V) ∈ S) (hhS : h ∉ S) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ S)
    (B : Finset V) (O : List (V × V))
    (hB : ∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
      t ∉ Subtype.val '' C.supp)
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hO : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
      e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
      e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp)
    (hvcontacts : ∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
      t ∈ B ∨ ∃ e ∈ O, t = e.1 ∨ t = e.2)
    (D : Decomposition (starPuncture
      (ordinaryMatePuncture (starPuncture G v B) O) u (insert v S)))
    (hhD : 2 ≤ D.endpointCount h) :
    ∃ F : Decomposition (ordinaryMatePuncture (starPuncture G v B) O),
      F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
      F.endpointCount v = D.endpointCount v + 1 ∧
      F.endpointCount h = D.endpointCount h := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let J := starPuncture Q u (insert v S)
  have hadj := fun t ht => (hB t ht).1
  have hEven := fun t ht => (hB t ht).2.1
  have hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).1,(hO e he).2.1,(hO e he).2.2.1⟩
  have havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hedges e he).2.1),
      fun hh => hn (hh ▸ (hedges e he).2.2),
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
  have hQS : ∀ t ∈ S, Q.Adj u t ∧ Even (Q.degree t) := by
    intro t ht
    obtain ⟨a,ha,haval⟩ := (hS t ht).2
    have hwt := hwind t (hS t ht).2
    refine ⟨((hwt.2 u).mpr (hS t ht).1.symm).symm,?_⟩
    rw [hwt.1]
    exact haval ▸ a.property
  have hcap : ∀ t ∈ S, t ≠ (x : V) → eDegree Q t ≤ 2 := by
    intro t ht htx
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
      rcases hprof w he with heG | hwv
      · exact (mem_evenNeighbors (G := G) t w).mpr ⟨hsub htw,heG⟩
      · subst w
        exact False.elim (hsep t (hS t ht).2 (hsub htw).symm)
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
  have hcenter : ∀ t, J.Adj v t → Even (J.degree t) → t = h := by
    have hc := long_joint_reserved_center_inherited (G := Q) h u v S [] huS huv.ne
      (fun t ht hvt => hsep t (hS t ht).2 (hsub hvt)) (by simp) hcenterQ
    dsimp only [ordinaryMatePuncture] at hc
    simp only [← SimpleGraph.ncard_neighborSet] at hc ⊢
    simpa only [J] using hc
  have hvpositive : ∀ t, J.Adj v t → 0 < D.endpointCount t := by
    intro t hvt
    rcases Nat.even_or_odd (J.degree t) with he | ho
    · have hth := hcenter t hvt he
      subst t
      omega
    · exact D.endpointCount_pos_of_odd_degree t ho
  have hretained : ∀ t, Q.Adj u t → t ∉ S →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS
    rcases Nat.even_or_odd (Q.degree t) with he | ho
    · have htv : t = v := (hprof t he).resolve_left
        (fun heG => htS (hcontacts t (hsub hut) heG))
      subst t
      have hd := starPuncture_degree_leaf (G := Q) u (insert v S) v
        (Finset.mem_insert_self _ _) hQ
      have hoJ : Odd (J.degree v) := by
        simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
        dsimp only [J]
        rw [Nat.even_iff] at he
        rw [Nat.odd_iff]
        omega
      exact Or.inr (D.endpointCount_pos_of_odd_degree v hoJ)
    · exact Or.inl ho
  obtain ⟨F,hsize,hFu,hFv,hkeep⟩ := restore_contact_E3_with_retained_reserves
    u v x S huS hvS huv.ne huQOdd hSodd hQ
    (fun t ht => (hQS t ht).1) (fun t ht => (hQS t ht).2)
    hxS hcap (fun t ht hvt => hsep t (hS t ht).2 (hsub hvt)) D hretained hvpositive
  have hhu : h ≠ u := fun hh => (Nat.not_even_iff_odd.mpr huOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  have hhv : h ≠ v := fun hh => (Nat.not_even_iff_odd.mpr hvOdd)
    (hh ▸ H.counterexample.1.2.2.2.1)
  exact ⟨F,hsize,hFu,hFv,hkeep h hhu hhv hhS⟩

/-- Construct and restore the first side of the E3 joint puncture in one
coherent preparation. Only the ordinary star and mates remain deleted;
both corridor endpoints are exposed and h retains its two endpoints. -/
theorem bare_long_E3_prepared_endpoint
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
      ∃ F : Decomposition (ordinaryMatePuncture (starPuncture G v B) O),
        F.size ≤ (Fintype.card V + 1) / 2 ∧ 1 ≤ F.endpointCount u ∧
        1 ≤ F.endpointCount v ∧ 2 ≤ F.endpointCount h := by
  classical
  obtain ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,D,hsize,hhD⟩ :=
    bare_long_E3_auxiliary_endpoint h u v x H C hxC huOdd hvOdd huv
      hsep S hxS hhS hSodd hS hcontacts
  obtain ⟨F,hFsize,hFu,hFv,hFh⟩ := bare_long_E3_restore_first_side h u v x H C hxC
    huOdd hvOdd huv hsep S hxS hhS hSodd hS hcontacts B O hB hdis hO hvcontacts D hhD
  refine ⟨B,O,hB,hdis,hO,hvcontacts,hpacket,hmeta,F,by omega,hFu,by omega,?_⟩
  rw [hFh]
  exact hhD

end Gallai.TwoException
