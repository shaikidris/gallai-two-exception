/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryFamilyRestoration

@[expose] public section

/-! # One-step descent in the pending ordinary mate family -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance headRestoreAdj (G : SimpleGraph V) (u : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restoring the head mate leaves exactly the tail puncture. -/
theorem ordinaryMatePuncture_head_restore
    (M : List (V × V)) (b c : V)
    (hbc : (ordinaryMatePuncture G M).Adj b c) :
    ordinaryMatePuncture G ((b,c) :: M) ⊔ SimpleGraph.edge b c =
      ordinaryMatePuncture G M := by
  exact delete_edge_sup_edge (ordinaryMatePuncture G M) b c hbc

/-- The first ordinary triangle mate can be paid without path loss,
returning the decomposition on the shorter puncture. Centre and all
unrelated endpoint counts are preserved, so their reserves survive. -/
theorem restore_ordinary_family_head
    (u : V) (B : Finset V) (M : List (V × V))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (haB : (a : V) ∈ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : (((b : V), (c : V)) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ ((b : V), (c : V)) :: M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ ((b : V), (c : V)) :: M,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B)
      (((b : V), (c : V)) :: M)))
    (hcentre : ¬ (ordinaryMatePuncture (starPuncture G u B)
      (((b : V), (c : V)) :: M)).Adj b u ∨ 0 < D.endpointCount u) :
    ∃ E : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      E.size = D.size ∧ 2 ≤ E.endpointCount b ∧
      E.endpointCount u = D.endpointCount u ∧
      ∀ t, t ≠ (b : V) → t ≠ (c : V) → E.endpointCount t = D.endpointCount t := by
  classical
  have hmem : ((b : V), (c : V)) ∈ ((b : V), (c : V)) :: M := List.mem_cons_self ..
  obtain ⟨hbu, hcu, hbB, hcB⟩ := havoid _ hmem
  obtain ⟨hbc, _, _⟩ := hedges _ hmem
  have hbcStar : (starPuncture G u B).Adj b c := by
    refine ⟨hbc, ?_⟩
    intro ha
    exact hcu ((star_sup_adj_off_center u B (b : V) (c : V) hbu).mp ha).2
  have hhead := (List.pairwise_cons.mp hdis).1
  have hbAvoid : ∀ e ∈ M, (b : V) ≠ e.1 ∧ (b : V) ≠ e.2 :=
    fun e he => ⟨(hhead e he).1, (hhead e he).2.1⟩
  have heq := ordinaryMatePuncture_head_restore (G := starPuncture G u B) M b c
    ((ordinaryMatePuncture_adj_of_avoids M b c hbAvoid).mpr hbcStar)
  have hr := restore_ordinary_family_triangle_mate u B (((b : V), (c : V)) :: M)
    hadj hleaves hdis havoid hedges C a b c hsupp haB hmem D hcentre
  rw [heq] at hr
  obtain ⟨E, hs, hb, hv⟩ := hr
  have hkeep : ∀ t, t ≠ (b : V) → t ≠ (c : V) → E.endpointCount t = D.endpointCount t := by
    intro t htb htc
    have ht := hv t
    simpa only [Ne.symm htb, Ne.symm htc, ite_false, Nat.add_zero] using ht
  exact ⟨E, hs, hb, hkeep u hbu.symm hcu.symm, hkeep⟩

end Gallai.TwoException
