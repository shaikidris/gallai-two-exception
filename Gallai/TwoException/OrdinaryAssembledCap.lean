/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledRestoration
public import Gallai.TwoException.OrdinaryStarMateCap

@[expose] public section

/-! # E-degree cap for the actual assembled hub-deleting preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance assembledCapComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance assembledCapAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Complete ordinary-contact coverage supplies the global cap for the
actual assembled puncture. The original contact classification is explicit:
this consumer applies to the hub-deleting, not arbitrary private-contact,
preparation branch. -/
theorem bare_ordinary_assembled_cap
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
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ t, Even ((ordinaryMatePuncture (starPuncture G u B) M).degree t) →
      eDegree (ordinaryMatePuncture (starPuncture G u B) M) t ≤ 3 := by
  classical
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp :=
    fun C hC t ht => (Finset.mem_filter.mp (hP C hC ht)).2
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
    · rw [ht]
      exact x.property
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp ht
      exact v.property
  have hcentre := ordinary_even_mates_avoid_odd_centre G M u hu
    (fun e he => ⟨(hguard e he).2.1,(hguard e he).2.2.1⟩)
  have havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B :=
    fun e he => ⟨(hcentre e he).1,(hcentre e he).2,
      (hguard e he).2.2.2.1,(hguard e he).2.2.2.2⟩
  have hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hguard e he).1,(hguard e he).2.1,(hguard e he).2.2.1⟩
  have hcoverage := ordinary_finite_contact_coverage G S F P mates htouched hcover (x : V)
  have hc : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hut ht
    rcases hclass t hut ht with htx | hth | htS
    · left
      simp [B,htx]
    · exact Or.inr (Or.inr hth)
    · rcases hcoverage ⟨t,ht⟩ htS with htB | hmate
      · exact Or.inl htB
      · exact Or.inr (Or.inl hmate)
  exact bare_ordinary_star_mates_cap h x H u B M (by simp [B]) hadj heven
    hdis havoid hedges hc

end Gallai.TwoException
