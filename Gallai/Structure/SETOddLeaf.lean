/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SET
public import Gallai.Structure.TriangleComponents

@[expose] public section

/-! # The retained even pair in the odd-leaf SET case

When one SET even vertex changes parity, the other two remain even. Original
triangle components force any promoted odd vertex to complete their triangle.
-/

namespace Gallai

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]
variable {G : SimpleGraph W} [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The induced even graph of a SET graph is literally one triangle. -/
theorem IsSET.even_components_triangles (h : IsSET H) :
    ComponentsAreTriangles (evenSubgraph H) := by
  classical
  have hk : evenSubgraph H = ⊤ := by
    ext a b
    change H.Adj a.val b.val ↔ a ≠ b
    constructor
    · intro ha he
      exact ha.ne (congrArg Subtype.val he)
    · intro hn
      exact h.even_clique a b a.property b.property (fun he => hn (Subtype.ext he))
  rw [hk]
  intro C
  constructor
  · rw [SimpleGraph.ConnectedComponent.top_supp_eq_univ]
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Set.mem_ofPred_eq] using h.card_even
  · ext a b
    change (a.val ≠ b.val) ↔ a ≠ b
    exact not_congr Subtype.val_injective.eq_iff

/-- Every SET vertex has an even neighbour other than a prescribed vertex. -/
theorem IsSET.even_neighbor_ne (h : IsSET H) (v z : V) :
    ∃ w, H.Adj v w ∧ Even (H.degree w) ∧ w ≠ z := by
  have hp : 1 < (evenNeighbors H v).card := by
    rcases h.eDegree_two_or_three v with he | he <;> unfold eDegree at he <;> omega
  obtain ⟨w, hw, hn⟩ := Finset.exists_mem_ne hp z
  obtain ⟨ha, he⟩ := (mem_evenNeighbors (G := H) v w).mp hw
  exact ⟨w, ha, he, hn⟩

/-- A promoted old odd vertex completes the retained even pair's original
triangle. Its only original even neighbours are those two retained vertices. -/
theorem IsSET.promoted_odd_completes_pair (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃v w⦄, H.Adj v w → G.Adj (f v) (f w))
    (ht : ComponentsAreTriangles (evenSubgraph G)) (z a b : V)
    (ha : Even (H.degree a)) (hb : Even (H.degree b)) (hab : a ≠ b)
    (hcover : ∀ v, Even (H.degree v) → v = z ∨ v = a ∨ v = b)
    (hga : Even (G.degree (f a))) (hgb : Even (G.degree (f b)))
    (y : V) (hy : Odd (H.degree y)) (hgy : Even (G.degree (f y))) :
    G.Adj (f a) (f y) ∧ G.Adj (f b) (f y) ∧
      ∀ v, Even (G.degree v) → G.Adj (f y) v → v = f a ∨ v = f b := by
  have hya : y ≠ a := fun he => (Nat.not_even_iff_odd.mpr hy) (he ▸ ha)
  have hyb : y ≠ b := fun he => (Nat.not_even_iff_odd.mpr hy) (he ▸ hb)
  have habG := hle (h.even_clique a b ha hb hab)
  obtain ⟨w, hyw, hew, hnw⟩ := h.even_neighbor_ne y z
  have hboth : G.Adj (f a) (f y) ∧ G.Adj (f b) (f y) := by
    rcases hcover w hew with hw | hw | hw
    · exact (hnw hw).elim
    · subst w
      have hclose := even_triangle_close_path ht hgy hga hgb (hle hyw) habG
        (fun he => hyb (f.injective he))
      exact ⟨(hle hyw).symm, hclose.1.symm⟩
    · subst w
      have hclose := even_triangle_close_path ht hgy hgb hga (hle hyw) habG.symm
        (fun he => hya (f.injective he))
      exact ⟨hclose.1.symm, (hle hyw).symm⟩
  refine ⟨hboth.1, hboth.2, ?_⟩
  exact (even_triangle_close_path ht hga hgy hgb hboth.1 hboth.2.symm
    (fun he => hab (f.injective he))).2

/-- With the retained pair fixed, there is at most one promoted old odd
vertex, even though the third SET even vertex need not preserve its parity. -/
theorem IsSET.promoted_odd_pair_subsingleton (h : IsSET H) (f : V ↪ W)
    (hle : ∀ ⦃v w⦄, H.Adj v w → G.Adj (f v) (f w))
    (ht : ComponentsAreTriangles (evenSubgraph G)) (z a b : V)
    (ha : Even (H.degree a)) (hb : Even (H.degree b)) (hab : a ≠ b)
    (hcover : ∀ v, Even (H.degree v) → v = z ∨ v = a ∨ v = b)
    (hga : Even (G.degree (f a))) (hgb : Even (G.degree (f b))) :
    Set.Subsingleton {v | Odd (H.degree v) ∧ Even (G.degree (f v))} := by
  intro y hy t ht'
  have hY := h.promoted_odd_completes_pair f hle ht z a b ha hb hab hcover hga hgb y hy.1 hy.2
  have hT := h.promoted_odd_completes_pair f hle ht z a b ha hb hab hcover hga hgb t ht'.1 ht'.2
  have hby : b ≠ y := by
    intro he
    exact (Nat.not_even_iff_odd.mpr hy.1) (he ▸ hb)
  have hlocal := even_triangle_close_path ht hgb hga hy.2
    (hle (h.even_clique b a hb ha hab.symm)) hY.1
    (fun he => hby (f.injective he))
  rcases hlocal.2 (f t) ht'.2 hT.1 with he | he
  · have htb := f.injective he
    exact False.elim ((Nat.not_even_iff_odd.mpr ht'.1) (htb ▸ hb))
  · exact (f.injective he).symm

end Gallai
