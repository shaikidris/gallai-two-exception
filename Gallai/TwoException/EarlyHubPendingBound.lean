/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyNativeGuards
public import Gallai.TwoException.EarlyWindmillAggregate

@[expose] public section

/-! # Pending-leaf guards with a prescribed exceptional hub -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubPendingStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance hubPendingHalf (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Prescribing the exceptional hub removes it from the pending leaves.
The original E-degree bound is required only at those remaining leaves. -/
theorem bare_early_prescribed_hub_pending_le_two
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (B A : Finset V) (hAB : A ⊆ B) (hxA : (x : V) ∈ A)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u))) :
    ∀ w ∈ B \ A, passingNeighborCount E w ≤ 2 := by
  classical
  intro w hw
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    intro a b hab
    rw [heq] at hab
    exact hab.1
  have hwu : w ≠ u := by
    intro he
    exact G.irrefl (he ▸ hadj w (Finset.mem_sdiff.mp hw).1)
  have hmissing : ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj w u := by
    intro ha
    rw [heq] at ha
    exact ha.2 ((star_sup_adj_off_center u (B \ A) w u hwu).mpr ⟨hw,rfl⟩)
  have hwx : w ≠ (x : V) := fun he =>
    (Finset.mem_sdiff.mp hw).2 (he ▸ hxA)
  exact (ordinary_pending_passing_le_eDegree E u w hsub
    (ordinary_half_star_even_preserved u B A hAB hadj hleaves) hmissing).trans
    (bare_nonhub_eDegree_le_two h x ⟨w,hleaves w (Finset.mem_sdiff.mp hw).1⟩ H hwx)

/-- Literal early restoration permits the exceptional hub among the deleted
leaves when its edge is prescribed. Packet gains remain branch-specific. -/
theorem bare_restore_actual_early_hub_star_of_partition_gains
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (K L : Finset V) (O : List (V × V)) (N epsilon : ℕ)
    (hdis : Disjoint K L) (hxB : (x : V) ∈ K ∪ L)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ O, t = e.1)
    (D : Decomposition (starPuncture G u (K ∪ L)))
    (hh : 0 < D.endpointCount h) (hrec : ∀ e ∈ O, 2 ≤ D.endpointCount e.1)
    (hround : 0 < D.endpointCount u ∨ Odd #(K ∪ L))
    (hstrict : epsilon + 1 < D.endpointCount u + N)
    (hgains : ∀ A : Finset V, A ⊆ K ∪ L → (x : V) ∈ A →
      ∀ E : Decomposition ((starPuncture G u (K ∪ L)) ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      (∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t = 2) →
      #(K \ A) ≤ #(K ∩ A) ∧ #(L \ A) + N ≤ #(L ∩ A) + epsilon) :
    ∃ F : Decomposition G, F.size = D.size ∧ 0 < F.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → F.endpointCount t = D.endpointCount t := by
  classical
  have hu : u ∉ K ∪ L := fun ht => G.irrefl (hadj u ht)
  have hpositive := early_prefix_full_neighbourhood_positive u h (K ∪ L) O
    hadj hleaves hcover D hh hrec
  have hout := restore_early_star_of_partition_gains D u x K L 0 N epsilon
    hdis hu hxB hround (by simpa only [Nat.add_zero] using hstrict)
    (fun t ht => starPuncture_missing G u (K ∪ L) hu t ht)
    hpositive (fun A hA hxA E _ =>
      bare_early_prescribed_hub_pending_le_two h x H u (K ∪ L) A hA hxA hadj hleaves E)
    (by simpa only [Nat.add_zero] using hgains)
  rwa [starPuncture_restore G u (K ∪ L) hadj] at hout

end Gallai.TwoException
