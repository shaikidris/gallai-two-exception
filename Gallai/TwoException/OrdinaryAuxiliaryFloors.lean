/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledBoundary
public import Gallai.TwoException.OrdinaryAssembledFloor
public import Gallai.TwoException.OrdinaryAssembledSpecialFloor
public import Gallai.TwoException.OrdinaryHubComponentFloor

@[expose] public section

/-! # Complete component floors for the hub-deleting ordinary auxiliary -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance auxiliaryFloorsEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance auxiliaryFloorsAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- All actual auxiliary components have floor decompositions. Original
regular coverage and special triangle labels are preparation data; no
auxiliary component budget, witness, cap or parity profile is assumed. -/
theorem bare_ordinary_auxiliary_component_floors
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hlen : ∀ C ∈ F, (mates C).length ≤ 1)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t, t ∈ C.supp →
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ a ∈ P C ∧ b ∈ P C ∧ mates C = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent,
      HasPathBudget ((ordinaryMatePuncture (starPuncture G u B) M).induce K.supp)
        (Fintype.card K.supp / 2) := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  let J := ordinaryMatePuncture (starPuncture G u B) M
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp :=
    fun C hC t ht => (Finset.mem_filter.mp (hP C hC ht)).2
  have hmateSupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp :=
    fun C hC e he => ⟨(hmates C hC e he).2.1,(hmates C hC e he).2.2.1⟩
  obtain ⟨hdis,hguard⟩ := ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx
  have hadj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · simpa only [ht] using hxu
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,hvC⟩ := Finset.mem_biUnion.mp hv
      exact hS v (Finset.mem_filter.mp (hP C hC hvC)).1
  have heven : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · rw [ht]; exact x.property
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
      exact v.property
  have hc := ordinary_even_mates_avoid_odd_centre G M u hu
    (fun e he => ⟨(hguard e he).2.1,(hguard e he).2.2.1⟩)
  have hav : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B :=
    fun e he => ⟨(hc e he).1,(hc e he).2,
      (hguard e he).2.2.2.1,(hguard e he).2.2.2.2⟩
  have hed : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hguard e he).1,(hguard e he).2.1,(hguard e he).2.2.1⟩
  have hcoverage := ordinary_finite_contact_coverage G S F P mates htouched hcover (x : V)
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hut ht
    rcases hclass t hut ht with htx | hth | htS
    · left
      simp [B,htx]
    · exact Or.inr (Or.inr hth)
    · rcases hcoverage ⟨t,ht⟩ htS with htB | hmate
      · exact Or.inl htB
      · exact Or.inr (Or.inl hmate)
  have hcentre := ordinary_star_mates_centre_eDegree_le_one h u B M
    hadj heven hdis hav hed hcontacts
  have hprofile := ordinary_star_mates_even_preserved u B M hadj heven hdis hav hed
  have hxOdd := ordinary_star_mates_leaves_odd u B M hadj heven
    (fun e he => ⟨(hav e he).2.2.1,(hav e he).2.2.2⟩) x (by simp [B])
  have hcap := bare_ordinary_assembled_cap h x H u hu hxu S hS F P mates hP hlen
    hmates hx htouched hcover hclass
  dsimp only
  intro K
  rcases H.counterexample.1 with ⟨hconn,_,_,_,_,_,_⟩
  rcases ordinary_assembled_component_contact hconn u x F P mates hsupp hmateSupp K with
    huK | hxK | ⟨C,hC,t,htC,htK⟩
  · exact contact_component_floor_of_eDegree_le_one hcap K u huK hcentre
  · exact bare_ordinary_hub_component_floor h x H u hu B S F mates htouched hx
      hmateSupp hclass hprofile hxOdd hcap K hxK
  · by_cases hCs : C ∈ special
    · obtain ⟨a,b,c,hs,ha,hb,hempty,hac,hbc,hcu⟩ := hspecial C hC hCs
      exact ordinary_assembled_special_floor u hu x S hS hxu F P mates hP hlen
        hmates hx C hC a b c hs ha hb hempty hac hbc hcu t htC hcap K htK
    · exact bare_ordinary_assembled_regular_floor h x H u hu hxu S hS F P mates hP hlen
        hmates hx htouched hcover hclass C hC (hregular C hC hCs) t htC K htK

end Gallai.TwoException
