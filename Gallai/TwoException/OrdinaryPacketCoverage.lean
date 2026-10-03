/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateBudget

@[expose] public section

/-! # Original-component coverage of ordinary preparation packets -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance packetAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A triangle preparation consisting of one contact leaf and the opposite
mate covers its entire original even component, even in a larger family. -/
theorem ordinary_triangle_packet_covered
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (B : Finset V) (M : List (V × V))
    (haB : (a : V) ∈ B) (hmate : ((b : V), (c : V)) ∈ M) :
    ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2 := by
  intro t ht
  rw [hsupp] at ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl
  · exact Or.inl haB
  · exact Or.inr ⟨_, hmate, Or.inl rfl⟩
  · exact Or.inr ⟨_, hmate, Or.inr rfl⟩

/-- A fully deleted ordinary contact component needs no mate. This includes
isolates and the three-contact triangle preparation. -/
theorem ordinary_full_star_packet_covered
    (C : (evenSubgraph G).ConnectedComponent) (B : Finset V) (M : List (V × V))
    (hstar : ∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B) :
    ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2 :=
  fun t ht => Or.inl (hstar t ht)

/-- A retained contact of a prepared triangle has its native floor in the
combined puncture: the component coverage guard follows from the packet,
not from an independently assumed parity profile. -/
theorem bare_ordinary_triangle_packet_floor
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u : V) (B : Finset V) (M : List (V × V)) (hxB : x ∈ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (C : (evenSubgraph G).ConnectedComponent) (a b c p : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (hpC : p ∈ C.supp)
    (haB : (a : V) ∈ B) (hmate : ((b : V), (c : V)) ∈ M)
    (K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent)
    (hpK : (p : V) ∈ K.supp) :
    HasPathBudget ((ordinaryMatePuncture (starPuncture G u B) M).induce K.supp)
      (Fintype.card K.supp / 2) := by
  classical
  exact bare_ordinary_star_mates_component_floor h x H u B M hxB hadj hleaves
    hdis havoid hedges hcontacts C p hpC
    (ordinary_triangle_packet_covered C a b c hsupp B M haB hmate) K hpK

end Gallai.TwoException
