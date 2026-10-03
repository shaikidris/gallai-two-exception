/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTriangleComponent

@[expose] public section

/-! # Non-SET boundary witnesses in prepared ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
noncomputable local instance budgetMateAdj (u b c : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(b,c)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- When a whole even component becomes odd, every one of its vertices
has at most the newly even contact centre as an even neighbour. -/
theorem prepared_ordinary_component_eDegree_le_one
    (C : (evenSubgraph G).ConnectedComponent) (p : evenVertices G)
    (hpC : p ∈ C.supp) (u : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t)) :
    eDegree J p ≤ 1 := by
  classical
  have hsubset : evenNeighbors J p ⊆ {u} := by
    intro t ht
    obtain ⟨hpt, htEven⟩ := (mem_evenNeighbors (G := J) p t).mp ht
    rcases hprofile t htEven with htOriginal | htu
    · let te : evenVertices G := ⟨t, htOriginal⟩
      have htC : te ∈ C.supp := C.mem_supp_of_adj_mem_supp hpC (hsub hpt)
      have ho := hodd te htC
      change Odd (J.degree t) at ho
      rw [Nat.even_iff] at htEven
      rw [Nat.odd_iff] at ho
      omega
    · exact Finset.mem_singleton.mpr htu
  have hc := Finset.card_le_card hsubset
  simpa only [eDegree, Finset.card_singleton] using hc

/-- The boundary witness gives the actual puncture component its floor
budget, once the global puncture cap has been established. -/
theorem prepared_ordinary_component_floor
    (C : (evenSubgraph G).ConnectedComponent) (p : evenVertices G)
    (hpC : p ∈ C.supp) (u : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t))
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (K : J.ConnectedComponent) (hpK : (p : V) ∈ K.supp) :
    HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  exact contact_component_floor_of_eDegree_le_one hcap K p hpK
    (prepared_ordinary_component_eDegree_le_one C p hpC u hsub hprofile hodd)

/-- The actual T1/regular-T2 puncture supplies the prepared-component
parity hypotheses. Only the global cap and choice of its puncture
component remain inputs to the floor assembly. -/
theorem ordinary_triangle_puncture_component_floor
    (C : (evenSubgraph G).ConnectedComponent) (a b c p : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (hpC : p ∈ C.supp)
    (u : V) (B : Finset V) (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) (haB : (a : V) ∈ B)
    (hab : (a : V) ≠ b) (hac : (a : V) ≠ c)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c)
    (hcap : ∀ t, Even (((starPuncture G u B).deleteEdges
      {s((b : V),(c : V))}).degree t) →
      eDegree ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}) t ≤ 3)
    (K : ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).ConnectedComponent)
    (hpK : (p : V) ∈ K.supp) :
    HasPathBudget (((starPuncture G u B).deleteEdges
      {s((b : V),(c : V))}).induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  obtain ⟨hprofile, hbOdd, hcOdd⟩ := ordinary_triangle_puncture_profile
    u b c B hadj hleaves hbu hcu hbB hcB hbc b.property c.property
  have haOdd := contact_spoke_puncture_leaf_odd u b c a B haB
    (hadj a haB) a.property hab hac
  have hodd : ∀ t : evenVertices G, t ∈ C.supp →
      Odd (((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).degree t) := by
    intro t ht
    rw [hsupp] at ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact haOdd
    · exact hbOdd
    · exact hcOdd
  have hsub : ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}) ≤ G := by
    intro v w hvw
    exact hvw.1.1
  exact prepared_ordinary_component_floor C p hpC u hsub hprofile hodd hcap K hpK

end Gallai.TwoException
