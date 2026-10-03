/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongJointBoundary
public import Gallai.TwoException.BareLongFamilyLabels
public import Gallai.TwoException.OrdinaryTriangleBudget

@[expose] public section

/-! # Ordinary-component witnesses after both corridor preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longWitnessAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- A covered ordinary even component becomes wholly odd in the actual
second-side preparation and stays odd through a disjoint first-side
preparation. It therefore supplies a low-E-degree witness in the joint
auxiliary, including when the second centre becomes newly even. -/
theorem long_joint_prepared_ordinary_witness
    (u v : V) (B S : Finset V) (O N : List (V × V))
    (C : (evenSubgraph G).ConnectedComponent) (p : evenVertices G) (hp : p ∈ C.supp)
    (hadj : ∀ t ∈ B, G.Adj v t) (hEven : ∀ t ∈ B, Even (G.degree t))
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcover : ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ O, (t : V) = e.1 ∨ (t : V) = e.2)
    (hsep : ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ≠ u ∧ (t : V) ∉ insert v S ∧
      ∀ e ∈ N, (t : V) ≠ e.1 ∧ (t : V) ≠ e.2)
    (hprofile : ∀ t,
      Even ((ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) N).degree t) → Even (G.degree t) ∨ t = v) :
    eDegree (ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
        u (insert v S)) N) p ≤ 1 := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) O
  let J := ordinaryMatePuncture (starPuncture Q u (insert v S)) N
  have hleaf := ordinary_star_mates_leaves_odd (G := G) v B O hadj hEven
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have hmate := ordinary_star_mates_endpoints_odd (G := G) v B O hdis havoid hedges
  have hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t) := by
    intro t ht
    have ho : Odd (Q.degree t) := by
      rcases hcover t ht with hb | ⟨e,he,hte⟩
      · exact hleaf t hb
      · rcases hte with hte | hte
        · exact hte ▸ (hmate e he).1
        · exact hte ▸ (hmate e he).2
    obtain ⟨htu,htS,htN⟩ := hsep t ht
    have hd := (long_ordinary_preparation_unchanged (G := Q) u t
      (insert v S) N htu htS htN).1
    change Odd ((ordinaryMatePuncture (starPuncture Q u (insert v S)) N).degree t)
    rw [hd]
    exact ho
  have hsub : J ≤ G := by
    intro a b hab
    have hs : (starPuncture Q u (insert v S)).Adj a b :=
      (ordinaryMatePuncture_le N) hab
    have hq : Q.Adj a b := hs.1
    exact ((ordinaryMatePuncture_le O) hq).1
  exact prepared_ordinary_component_eDegree_le_one C p hp v hsub hprofile hodd

/-- The same finite family used to define the ordinary puncture discharges
both ordinary-boundary obligations of the joint budget consumer. Its local
coverage and separation are derived before invoking the component witness. -/
theorem long_joint_family_ordinary_bounds
    (u v : V) (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v))
    (C : (evenSubgraph G).ConnectedComponent)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (S : Finset V) (N : List (V × V))
    (houtside : ∀ Z ∈ F, Z ≠ C)
    (hsupp : ∀ Z ∈ F, ∀ t ∈ P Z, t ∈ Z.supp)
    (hmates : ∀ Z ∈ F, ∀ e ∈ mates Z, e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp)
    (hcover : ∀ Z ∈ F, ∀ t ∈ Z.supp,
      t ∈ P Z ∨ ∃ e ∈ mates Z, t = e.1 ∨ t = e.2)
    (hS : ∀ t ∈ S, t ∈ Subtype.val '' C.supp)
    (hN : ∀ e ∈ N, e.1 ∈ Subtype.val '' C.supp ∧ e.2 ∈ Subtype.val '' C.supp)
    (hdata : let B := (F.biUnion P).image Subtype.val
      let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
      (∀ t ∈ B, G.Adj v t ∧ Even (G.degree t)) ∧
      O.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ O, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B) ∧
      (∀ e ∈ O, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)))
    (hprofile : let B := (F.biUnion P).image Subtype.val
      let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
      ∀ t, Even ((ordinaryMatePuncture
        (starPuncture (ordinaryMatePuncture (starPuncture G v B) O)
          u (insert v S)) N).degree t) → Even (G.degree t) ∨ t = v) :
    let B := (F.biUnion P).image Subtype.val
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    let J := ordinaryMatePuncture
      (starPuncture (ordinaryMatePuncture (starPuncture G v B) O) u (insert v S)) N
    (∀ t ∈ B, eDegree J t ≤ 1) ∧
      (∀ e ∈ O, eDegree J e.1 ≤ 1 ∧ eDegree J e.2 ≤ 1) := by
  classical
  let B := (F.biUnion P).image Subtype.val
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  let J := ordinaryMatePuncture
    (starPuncture (ordinaryMatePuncture (starPuncture G v B) O) u (insert v S)) N
  obtain ⟨hadj,hdis,havoid,hedges⟩ := hdata
  obtain ⟨hcoverage,hBlabels,hOlabels⟩ :=
    long_ordinary_family_boundary_labels F P mates hsupp hmates hcover
  have hlocal : ∀ Z ∈ F, ∀ p : evenVertices G, p ∈ Z.supp → eDegree J p ≤ 1 := by
    intro Z hZ p hp
    exact long_joint_prepared_ordinary_witness u v B S O N Z p hp
      (fun t ht => (hadj t ht).1) (fun t ht => (hadj t ht).2)
      hdis havoid hedges (hcoverage Z hZ)
      (long_ordinary_component_avoids_windmill_packet C Z (houtside Z hZ)
        u v huOdd hvOdd S N hS hN) hprofile
  change (∀ t ∈ B, eDegree J t ≤ 1) ∧
    (∀ e ∈ O, eDegree J e.1 ≤ 1 ∧ eDegree J e.2 ≤ 1)
  refine ⟨?_,?_⟩
  · intro t ht
    obtain ⟨Z,hZ,p,hp,rfl⟩ := hBlabels t ht
    exact hlocal Z hZ p hp
  · intro e he
    obtain ⟨Z,hZ,p,q,hp,hq,rfl⟩ := hOlabels e he
    exact ⟨hlocal Z hZ p hp,hlocal Z hZ q hq⟩

end Gallai.TwoException
