/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledCap

@[expose] public section

/-! # Protected vertex locality in simultaneous ordinary preparations -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance protectedDegreeComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance protectedDegreeAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The bare prescribed vertex keeps its exact ordinary degree. Ordinary
spokes exclude it, and no genuine even mate can touch an E-degree-zero
vertex. This preserves both positivity and evenness for endpoint assembly. -/
theorem bare_ordinary_assembled_protected_degree
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u))
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, (t : V) ≠ h)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hedges : ∀ C ∈ F, ∀ e ∈ mates C, G.Adj e.1 e.2) :
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    (ordinaryMatePuncture (starPuncture G u B) M).degree h = G.degree h := by
  classical
  rcases H.counterexample.1 with ⟨_,hhx,_,hhEven,_,hhzero,_⟩
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr hu) (he ▸ hhEven)
  have hhB : h ∉ B := by
    intro hb
    rcases Finset.mem_insert.mp hb with he | hm
    · exact hhx he
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hm
      obtain ⟨C,hC,htC⟩ := Finset.mem_biUnion.mp ht
      exact hS t (Finset.mem_filter.mp (hP C hC htC)).1 he
  have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
  have hav : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hedge := hedges C (Finset.mem_toList.mp hC) f hfC
    constructor
    · intro heq
      have ha : G.Adj h f.2 := by simpa only [heq] using hedge
      have hm := (mem_evenNeighbors (G := G) h f.2).mpr ⟨ha,f.2.property⟩
      rw [hempty] at hm
      simpa using hm
    · intro heq
      have ha : G.Adj h f.1 := by simpa only [heq] using hedge.symm
      have hm := (mem_evenNeighbors (G := G) h f.1).mpr ⟨ha,f.1.property⟩
      rw [hempty] at hm
      simpa using hm
  have hm := ordinaryMatePuncture_degree_of_avoids (G := starPuncture G u B) M h hav
  have hs := starPuncture_degree_other (G := G) u B h hhu hhB
  simp only [← SimpleGraph.ncard_neighborSet] at hm hs ⊢
  exact hm.trans hs

end Gallai.TwoException
