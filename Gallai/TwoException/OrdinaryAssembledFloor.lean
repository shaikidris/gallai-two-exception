/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledCap
public import Gallai.TwoException.OrdinaryStarMateBudget

@[expose] public section

/-! # Regular component floors for assembled ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledFloorComponentEq : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance assembledFloorAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A regular original component supplies a floor budget in each actual
puncture component containing one of its vertices. Whole-support coverage
is required; the special two-contact packet does not satisfy this interface. -/
theorem bare_ordinary_assembled_regular_floor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (F : Finset (evenSubgraph G).ConnectedComponent)
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
    (C : (evenSubgraph G).ConnectedComponent) (hC : C ∈ F)
    (hwhole : ∀ t, t ∈ C.supp → t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (p : evenVertices G) (hpC : p ∈ C.supp) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent,
      (p : V) ∈ K.supp →
      HasPathBudget ((ordinaryMatePuncture (starPuncture G u B) M).induce K.supp)
        (Fintype.card K.supp / 2) := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  let J := ordinaryMatePuncture (starPuncture G u B) M
  have hsupp : ∀ D ∈ F, ∀ t ∈ P D, t ∈ D.supp :=
    fun D hD t ht => (Finset.mem_filter.mp (hP D hD ht)).2
  obtain ⟨hdis,hguard⟩ := ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx
  have hadj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · simpa only [ht] using hxu
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨D,hD,hvD⟩ := Finset.mem_biUnion.mp hv
      exact hS v (Finset.mem_filter.mp (hP D hD hvD)).1
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
  have hl := ordinary_star_mates_leaves_odd u B M hadj heven
    (fun e he => ⟨(hav e he).2.2.1,(hav e he).2.2.2⟩)
  have hm := ordinary_star_mates_endpoints_odd u B M hdis hav hed
  have hcoverage := ordinary_finite_component_coverage G F P mates C hC hwhole (x : V)
  have hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t) := by
    intro t ht
    rcases hcoverage t ht with htB | hmate
    · exact hl t htB
    · obtain ⟨e,he,hte⟩ := hmate
      obtain ⟨hleft,hright⟩ := hm e he
      dsimp only [J]
      simp only [← SimpleGraph.ncard_neighborSet] at hleft hright ⊢
      rcases hte with hte | hte
      · rw [hte]; exact hleft
      · rw [hte]; exact hright
  have hsubM : ∀ L : List (V × V), ordinaryMatePuncture (starPuncture G u B) L ≤ G := by
    intro L
    induction L with
    | nil => exact fun _ _ ha => ha.1
    | cons e L ih => exact fun _ _ ha => ih ha.1
  have hprofile := ordinary_star_mates_even_preserved u B M hadj heven hdis hav hed
  have hcap := bare_ordinary_assembled_cap h x H u hu hxu S hS F P mates
    hP hlen hmates hx htouched hcover hclass
  dsimp only
  intro K hpK
  exact prepared_ordinary_component_floor C p hpC u (hsubM M) hprofile hodd hcap K hpK

end Gallai.TwoException
