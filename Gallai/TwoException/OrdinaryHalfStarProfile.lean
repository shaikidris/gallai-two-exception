/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeFailure

@[expose] public section

/-! # Exact graph and parity profile after partial contact restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance halfProfileAdj (G : SimpleGraph V) (u : V)
    (B A : Finset V) : DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Partial restoration leaves exactly the star puncture at the pending
leaves, not merely an unspecified intermediate subgraph. -/
theorem ordinary_half_star_graph
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) :
    starPuncture G u B ⊔ A.sup (SimpleGraph.edge u) = starPuncture G u (B \ A) := by
  classical
  have huB : u ∉ B := fun hu => G.irrefl (hadj u hu)
  have huA : u ∉ A := fun hu => huB (hAB hu)
  have huR : u ∉ B \ A := fun hu => huB (Finset.mem_sdiff.mp hu).1
  ext v w
  by_cases hv : v = u
  · subst v
    simp only [SimpleGraph.sup_adj, starPuncture, SimpleGraph.sdiff_adj,
      star_sup_adj_center u B huB, star_sup_adj_center u A huA,
      star_sup_adj_center u (B \ A) huR, Finset.mem_sdiff]
    by_cases hwA : w ∈ A
    · have hwB := hAB hwA
      simp [hwA, hwB, hadj w hwB]
    · simp [hwA]
  · simp only [SimpleGraph.sup_adj, starPuncture, SimpleGraph.sdiff_adj,
      star_sup_adj_off_center u B v w hv, star_sup_adj_off_center u A v w hv,
      star_sup_adj_off_center u (B \ A) v w hv, Finset.mem_sdiff]
    by_cases hw : w = u
    · subst w
      by_cases hvA : v ∈ A
      · have hvB := hAB hvA
        simp [hvA, hvB, (hadj v hvB).symm]
      · simp [hvA]
    · simp [hw]

/-- The no-new-even profile survives the half-star, deriving the guard
used by all native tight-failure contribution lemmas. -/
theorem ordinary_half_star_even_preserved
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t)) :
    ∀ t, Even (((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u := by
  classical
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hp := ordinary_star_mates_even_preserved u (B \ A) []
    (fun t ht => hadj t (Finset.mem_sdiff.mp ht).1)
    (fun t ht => hleaves t (Finset.mem_sdiff.mp ht).1)
    (by simp) (by simp) (by simp)
  intro t ht
  simp only [← SimpleGraph.ncard_neighborSet] at ht hp ⊢
  rw [heq] at ht
  exact hp t ht

end Gallai.TwoException
