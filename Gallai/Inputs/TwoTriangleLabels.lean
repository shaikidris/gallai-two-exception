/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.NoEvenIsolates
public import Gallai.Structure.TriangleHubLabels

@[expose] public section

/-! # Structural labels for Claim 10's two touched triangles -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Under strict minimality a touched even triangle has two initial hub
neighbours. All hub even neighbours and leaf E-degree bounds are derived. -/
theorem minimal_counterexample_triangle_labels
    (u : V) (hu : Odd (G.degree u))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C : (evenSubgraph G).ConnectedComponent)
    (htouch : ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj u w) :
    ∃ a b c : evenVertices G,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (∀ w, w ∈ C.supp ↔ w = a ∨ w = b ∨ w = c) ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ G.Adj u a ∧ G.Adj u b ∧
      (∀ w, G.Adj u w → Even (G.degree w) → w = a ∨ w = b ∨ w = c) ∧
      (∀ w ∈ ({(a : V), (b : V), (c : V)} : Finset V), eDegree G w ≤ 2) := by
  classical
  have ht := minimal_counterexample_even_components_triangles hconn hcap hnot hset hmin
  obtain ⟨a, b, c, hab, hac, hbc, hm, habE, hacE, hbcE, hua, horder⟩ :=
    even_triangle_hub_labels u C (ht C).1 (ht C).2 htouch
  have hNu : ∀ w, G.Adj u w → Even (G.degree w) → w = a ∨ w = b ∨ w = c := by
    intro w huw hwEven
    let q : evenVertices G := ⟨w, hwEven⟩
    let E := (evenSubgraph G).connectedComponentMk q
    have hqE : q ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hCE := minimal_counterexample_odd_neighbors_one_component u hu
      hconn hcap hnot hset hmin C E htouch ⟨q, hqE, huw⟩
    have hqC : q ∈ C.supp := by rw [hCE]; exact hqE
    rcases (hm q).mp hqC with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  have hub : G.Adj u b := by
    by_contra hnb
    have hnc : ¬ G.Adj u c := fun h => hnb (horder h)
    have hs : evenNeighbors G u = {(a : V)} := by
      ext w
      constructor
      · intro hw
        obtain ⟨ha, he⟩ := (mem_evenNeighbors u w).mp hw
        rcases hNu w ha he with rfl | rfl | rfl
        · simp
        · exact (hnb ha).elim
        · exact (hnc ha).elim
      · intro hw
        have hw := Finset.mem_singleton.mp hw
        subst w
        exact (mem_evenNeighbors u a).mpr ⟨hua, a.property⟩
    apply minimal_counterexample_eDegree_ne_one hconn hcap hnot hset hmin u
    change #(evenNeighbors G u) = 1
    rw [hs]
    simp
  let A : Finset V := {(a : V), (b : V), (c : V)}
  have habN : (a : V) ≠ b := fun h => hab (Subtype.ext h)
  have hacN : (a : V) ≠ c := fun h => hac (Subtype.ext h)
  have hbcN : (b : V) ≠ c := fun h => hbc (Subtype.ext h)
  have hA : #A = 3 := by simp [A, habN, hacN, hbcN]
  have hmA (q : evenVertices G) : (q : V) ∈ A ↔ q ∈ C.supp := by
    rw [hm q]
    simp only [A, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · rintro (rfl | rfl | rfl) <;> simp
  have hlocal : ∀ w ∈ A, eDegree G w ≤ 2 := by
    intro w hw
    have he : Even (G.degree w) := by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact a.property
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact b.property
      have hwc := Finset.mem_singleton.mp hw
      exact hwc ▸ c.property
    let q : evenVertices G := ⟨w, he⟩
    have hqC := (hmA q).mp hw
    have hs : evenNeighbors G w ⊆ A.erase w := by
      intro t ht
      obtain ⟨ha, het⟩ := (mem_evenNeighbors w t).mp ht
      let r : evenVertices G := ⟨t, het⟩
      exact Finset.mem_erase.mpr ⟨ha.ne.symm,
        (hmA r).mpr (C.mem_supp_of_adj_mem_supp hqC ha)⟩
    have hc := Finset.card_le_card hs
    have hec := Finset.card_erase_add_one hw
    change #(evenNeighbors G w) ≤ 2
    omega
  exact ⟨a, b, c, hab, hac, hbc, hm, habE, hacE, hbcE, hua, hub, hNu, hlocal⟩

end Gallai
