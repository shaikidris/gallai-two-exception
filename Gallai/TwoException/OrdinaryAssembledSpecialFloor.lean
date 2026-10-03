/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryFiniteMateAssembly
public import Gallai.TwoException.OrdinarySpecialPacket

@[expose] public section

/-! # Special component floors from actual finite preparation data -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledSpecialEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance assembledSpecialAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Any contact with the special original component supplies its floor.
Finite-family separation derives mate avoidance; retained triangle edges
place the third-vertex witness in the actual auxiliary component. -/
theorem ordinary_assembled_special_floor
    (u : V) (hu : Odd (G.degree u)) (x : evenVertices G)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (hxu : G.Adj u x)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ D ∈ F, P D ⊆ ordinaryComponentPacket G S D)
    (hlen : ∀ D ∈ F, (mates D).length ≤ 1)
    (hmates : ∀ D ∈ F, ∀ e ∈ mates D,
      G.Adj e.1 e.2 ∧ e.1 ∈ D.supp ∧ e.2 ∈ D.supp ∧ e.1 ∉ P D ∧ e.2 ∉ P D)
    (hx : ∀ D ∈ F, x ∉ D.supp)
    (C : (evenSubgraph G).ConnectedComponent) (hC : C ∈ F)
    (a b c : evenVertices G) (hs : C.supp = {a,b,c})
    (ha : a ∈ P C) (hb : b ∈ P C) (hempty : mates C = [])
    (hac : G.Adj a c) (hbc : G.Adj b c) (hcu : ¬ G.Adj c u)
    (t : evenVertices G) (htC : t ∈ C.supp) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    let J := ordinaryMatePuncture (starPuncture G u B) M
    (∀ v, Even (J.degree v) → eDegree J v ≤ 3) →
    ∀ K : J.ConnectedComponent, (t : V) ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hsupp : ∀ D ∈ F, ∀ v ∈ P D, v ∈ D.supp :=
    fun D hD v hv => (Finset.mem_filter.mp (hP D hD hv)).2
  obtain ⟨hdis,hguard⟩ := ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx
  have hcAvoid := ordinary_empty_component_avoids_finite_mates G F mates
    (fun D hD e he => ⟨(hmates D hD e he).2.1,(hmates D hD e he).2.2.1⟩)
    C hempty c (by rw [hs]; simp)
  have hne : ∀ v : evenVertices G, (v : V) ≠ u := by
    intro v he
    exact (Nat.not_even_iff_odd.mpr hu) (he ▸ v.property)
  have hadj : ∀ v ∈ B, G.Adj u v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · simpa only [hv] using hxu
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨D,hD,hwD⟩ := Finset.mem_biUnion.mp hw
      exact hS w (Finset.mem_filter.mp (hP D hD hwD)).1
  have heven : ∀ v ∈ B, Even (G.degree v) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · rw [hv]; exact x.property
    · obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
      exact w.property
  have hcentre := ordinary_even_mates_avoid_odd_centre G M u hu
    (fun e he => ⟨(hguard e he).2.1,(hguard e he).2.2.1⟩)
  have hav : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B :=
    fun e he => ⟨(hcentre e he).1,(hcentre e he).2,
      (hguard e he).2.2.2.1,(hguard e he).2.2.2.2⟩
  have hed : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hguard e he).1,(hguard e he).2.1,(hguard e he).2.2.1⟩
  have hmem : ∀ v ∈ P C, (v : V) ∈ B := by
    intro v hv
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨v,Finset.mem_biUnion.mpr ⟨C,hC,hv⟩,rfl⟩
  dsimp only
  intro hcap K htK
  have hcontact : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp := by
    rw [hs] at htC
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
    rcases htC with he | he | he
    · exact Or.inl (he ▸ htK)
    · exact Or.inr (Or.inl (he ▸ htK))
    · exact Or.inr (Or.inr (he ▸ htK))
  have hcK := ordinary_special_witness_in_component u B M a b c hac hbc
    (hne a) (hne b) (hne c) hcAvoid K hcontact
  exact ordinary_special_star_mates_floor u B M hadj heven hdis hav hed C a b c hs
    (hmem a ha) (hmem b hb) hcu hcap K hcK

end Gallai.TwoException
