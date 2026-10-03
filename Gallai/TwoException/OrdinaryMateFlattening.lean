/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeSpokeFamily
public import Gallai.TwoException.OrdinaryMateSpokeAvoidance

@[expose] public section

/-! # Vertex-disjoint flattening of component-local mate lists -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Flattening at most one mate per distinct original even component
produces the vertex-disjoint ambient family required by puncture parity
and sequential restoration. -/
theorem ordinary_flattened_mates_pairwise_disjoint
    (Cs : List (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hunique : Cs.Pairwise (fun C D => C ≠ D))
    (hlen : ∀ C ∈ Cs, (mates C).length ≤ 1)
    (hsupp : ∀ C ∈ Cs, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp) :
    ((Cs.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))).Pairwise
      (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by
  rw [List.pairwise_map, List.pairwise_flatMap]
  constructor
  · intro C hC
    have hl := hlen C hC
    cases he : mates C with
    | nil => simp
    | cons e es =>
      cases es with
      | nil => simp
      | cons f fs => simp [he] at hl
  · apply hunique.imp_of_mem
    intro C D hC hD hCD e he f hf
    obtain ⟨hel,her⟩ := hsupp C hC e he
    obtain ⟨hfl,hfr⟩ := hsupp D hD f hf
    have hne : ∀ a b : evenVertices G, a ∈ C.supp → b ∈ D.supp → (a : V) ≠ b := by
      intro a b ha hb hab
      have heq : a = b := Subtype.val_injective hab
      subst b
      exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hb)
    exact ⟨hne e.1 f.1 hel hfl, hne e.1 f.2 hel hfr,
      hne e.2 f.1 her hfl, hne e.2 f.2 her hfr⟩

/-- Ordinary-component deletions and hub-component deletions form one
disjoint list. The latter may include the unpaid spoke at the hub itself. -/
theorem ordinary_hub_mate_families_disjoint
    (x : evenVertices G) (O N : List (V × V))
    (hOdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hNdis : N.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hO : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b : evenVertices G), e = ((a : V),(b : V)) ∧
      x ∉ C.supp ∧ a ∈ C.supp ∧ b ∈ C.supp)
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b) :
    (O ++ N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by
  rw [List.pairwise_append]
  refine ⟨hOdis,hNdis,?_⟩
  intro e he f hf
  obtain ⟨C,a,b,heq,hx,ha,hb⟩ := hO e he
  obtain ⟨c,d,hfeq,hc,hd⟩ := hN f hf
  subst e
  subst f
  have hne : ∀ a b : evenVertices G, a ∈ C.supp →
      (evenSubgraph G).Reachable x b → (a : V) ≠ b := by
    intro a b ha hr hab
    have hab' : a = b := Subtype.val_injective hab
    subst b
    apply hx
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans ha
  exact ⟨hne a c ha hc,hne a d ha hd,hne b c hb hc,hne b d hb hd⟩

/-- Move an unpaid spoke before the ordinary prefix, keeping the exact
vertex-disjoint deletion interface required by the auxiliary constructor. -/
theorem disjoint_deletion_spoke_to_head
    (O N : List (V × V)) (s : V × V)
    (hdis : (O ++ s :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)) :
    (s :: (O ++ N)).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
    (∀ e, e ∈ O ++ s :: N ↔ e ∈ s :: (O ++ N)) := by
  obtain ⟨hO,hSN,hcross⟩ := List.pairwise_append.mp hdis
  obtain ⟨hs,hN⟩ := List.pairwise_cons.mp hSN
  constructor
  · apply List.pairwise_cons.mpr
    constructor
    · intro e he
      rcases List.mem_append.mp he with he | he
      · have h := hcross e he s (List.mem_cons_self ..)
        exact ⟨h.1.symm,h.2.2.1.symm,h.2.1.symm,h.2.2.2.symm⟩
      · exact hs e he
    · exact List.pairwise_append.mpr ⟨hO,hN,
        fun e he f hf => hcross e he f (List.mem_cons_of_mem s hf)⟩
  · intro e
    simp only [List.mem_append,List.mem_cons]
    tauto

end Gallai.TwoException
