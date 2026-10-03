/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongOrdinaryWitness
public import Gallai.TwoException.OrdinaryRegularStarRestoration

@[expose] public section

/-! # Native ordinary-boundary bounds for a selected windmill packet -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeOrdinaryAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Choose one actual ordinary preparation family and derive its joint
boundary bounds. Neither a preparation family, parity profile nor boundary
E-degree bound is supplied as an input. -/
theorem bare_long_native_ordinary_boundary_bounds
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t)
    (S : Finset V) (N : List (V × V)) (hSodd : Odd #S)
    (hS : ∀ t ∈ S, G.Adj u t ∧ t ∈ Subtype.val '' C.supp)
    (hN : ∀ e ∈ N, e.1 ∈ Subtype.val '' C.supp ∧ e.2 ∈ Subtype.val '' C.supp) :
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
      let Q := ordinaryMatePuncture (starPuncture G v B) O
      Q.Adj u v ∧ Q.degree u = G.degree u ∧ Q.degree h = G.degree h ∧
      (∀ t, Q.Adj v t → Even (Q.degree t) → t = h) ∧
      (∀ w ∈ Subtype.val '' C.supp, Q.degree w = G.degree w ∧
        ∀ t, Q.Adj w t ↔ G.Adj w t) ∧
      let J := ordinaryMatePuncture (starPuncture
        (ordinaryMatePuncture (starPuncture G v B) O) u (insert v S)) N
      (∀ t ∈ B, eDegree J t ≤ 1) ∧
        (∀ e ∈ O, eDegree J e.1 ≤ 1 ∧ eDegree J e.2 ≤ 1) := by
  classical
  let T : Finset (evenVertices G) :=
    Finset.univ.filter (fun t => G.Adj v t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  let F := T.image (evenSubgraph G).connectedComponentMk
  obtain ⟨P,mates,hP,_,hdata,hcover,hdonor,hB,hdis,hO,hcontacts⟩ :=
    bare_long_ordinary_preparation_family h v x H C hxC hsep
  let B := (F.biUnion P).image Subtype.val
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hevenC : ∀ t ∈ Subtype.val '' C.supp, Even (G.degree t) := by
    intro t ht
    obtain ⟨w,_,rfl⟩ := ht
    exact w.property
  have hSE : ∀ t ∈ S, G.Adj u t ∧ Even (G.degree t) :=
    fun t ht => ⟨(hS t ht).1,hevenC t (hS t ht).2⟩
  have hNE : ∀ e ∈ N, Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨hevenC e.1 (hN e he).1,hevenC e.2 (hN e he).2⟩
  have hOE : ∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hO e he).1,(hO e he).2.1,(hO e he).2.2.1⟩
  have havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hOE e he).2.1),
      fun hh => hn (hh ▸ (hOE e he).2.2),
      (hO e he).2.2.2.1,(hO e he).2.2.2.2.1⟩
  have hprof := (long_joint_original_parity_profile u v B S O N huOdd hvOdd huv
    (fun t ht => (hB t ht).2.1) (fun e he => (hOE e he).2) hSE hSodd hNE).1
  have hxF := (ordinary_outside_hub_contact_family G x C hxC v h).1
  have houtside : ∀ Z ∈ F, Z ≠ C := by
    intro Z hZ heq
    exact hxF Z hZ (heq.symm ▸ hxC)
  have hsupp : ∀ Z ∈ F, ∀ t ∈ P Z, t ∈ Z.supp := by
    intro Z hZ t ht
    exact (Finset.mem_filter.mp (hP Z hZ ht)).2
  have hm : ∀ Z ∈ F, ∀ e ∈ mates Z, e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp := by
    intro Z hZ e he
    exact ⟨((hdata Z hZ).2.1 e he).2.1,((hdata Z hZ).2.1 e he).2.2.1⟩
  have hb := long_joint_family_ordinary_bounds u v huOdd hvOdd C F P mates S N
    houtside hsupp hm hcover (fun t ht => (hS t ht).2) hN
    ⟨fun t ht => ⟨(hB t ht).1,(hB t ht).2.1⟩,hdis,havoid,hOE⟩ hprof
  have hc : ∀ t, G.Adj v t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ O, t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hvt ht
    by_cases hth : t = h
    · exact Or.inr (Or.inr hth)
    · rcases hcontacts t hvt ht hth with htb | hto
      · exact Or.inl htb
      · exact Or.inr (Or.inl hto)
  obtain ⟨_,_,_,hcenter⟩ := bare_long_ordinary_preparation_cap h v x H B O
    (fun t ht => (hB t ht).1) (fun t ht => (hB t ht).2.1)
    hdis havoid hOE hc
  obtain ⟨hQ,hdu,_⟩ := long_ordinary_preparation_reserved_degree u v B O huOdd hvOdd huv
    (fun t ht => ⟨(hB t ht).1,(hB t ht).2.1⟩) (fun e he => (hOE e he).2)
  have hhv : h ≠ v := by
    intro hh
    exact (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hdh := (long_ordinary_preparation_unchanged (G := G) v h B O hhv
    (fun ht => (hB h ht).2.2.1 rfl)
    (fun e he => ⟨(hO e he).2.2.2.2.2.1,(hO e he).2.2.2.2.2.2.1⟩)).1
  have hwind := long_ordinary_preparation_windmill_unchanged v hvOdd C B O
    (fun t ht => (hB t ht).2.2.2)
    (fun e he => ⟨(hO e he).2.2.2.2.2.2.2.1,(hO e he).2.2.2.2.2.2.2.2⟩)
  have hpacket : ∀ e ∈ O, ∃ (Z : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      Z.supp = {a,b,c} ∧ (a : V) ∈ B := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨Z,hZ,hfZ⟩ := List.mem_flatMap.mp hf
    have hZF := Finset.mem_toList.mp hZ
    obtain ⟨a,hs,ha,_,_⟩ := (hdata Z hZF).2.2 f hfZ
    exact ⟨Z,a,f.1,f.2,rfl,hs,Finset.mem_image.mpr
      ⟨a,Finset.mem_biUnion.mpr ⟨Z,hZF,ha⟩,rfl⟩⟩
  have hmeta : Nonempty (OrdinaryRegularPacketData G h x v B O) := by
    refine ⟨{
      contacts := T
      components := F
      packets := P
      mates := mates
      component_contact := by rfl
      exception_absent := hxF
      packet_subset := hP
      contacts_avoid_h := fun t ht => (Finset.mem_filter.mp ht).2.2.2
      spoke_eq := rfl
      mate_eq := rfl
      cover := hcover
      mate_avoid := ?_
      mate_labels := ?_
      donor_avoid := ?_ }⟩
    · intro Z hZ e he
      obtain ⟨_,_,_,hl,hr⟩ := (hdata Z hZ).2.1 e he
      exact ⟨hl,hr⟩
    · intro Z hZ e he
      obtain ⟨a,hs,ha,_,_⟩ := (hdata Z hZ).2.2 e he
      exact ⟨a,hs,ha⟩
    · intro e he hve
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      obtain ⟨Z,hZ,hfZ⟩ := List.mem_flatMap.mp hf
      have hZF := Finset.mem_toList.mp hZ
      obtain ⟨_,_,_,_,_,_,hh2,_,hout2⟩ := hO ((f.1 : V),(f.2 : V)) he
      apply hdonor Z hZF f hfZ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hve,
        (fun ht => hout2 ⟨f.2,ht,rfl⟩),hh2.symm⟩
  exact ⟨B,O,hB,hdis,hO,hcontacts,hpacket,hmeta,hQ,hdu,hdh,hcenter,hwind,hb⟩

end Gallai.TwoException
