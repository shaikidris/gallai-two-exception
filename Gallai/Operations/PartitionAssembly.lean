/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.DecompositionMap
public import Gallai.Operations.Union
public import Mathlib.Data.Set.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Floor-budget assembly on an actual vertex partition -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

omit [DecidableEq V] in
/-- A floor decomposition on a vertex set containing every vertex transports back. -/
theorem floor_of_induce_all (S : Set V) [DecidablePred (· ∈ S)]
    (hall : ∀ v, v ∈ S) (h : HasPathBudget (G.induce S) (Fintype.card S / 2)) :
    HasPathBudget G (Fintype.card V / 2) := by
  classical
  obtain ⟨D, hD⟩ := h
  have he : (G.induce S).map (Function.Embedding.subtype _) = G :=
    (G.spanningCoe_induce_eq_self S).mpr (fun v _ => hall v)
  have hc : Fintype.card S = Fintype.card V := Fintype.card_of_bijective
    (show Function.Bijective (Subtype.val : S → V) from
      ⟨Subtype.val_injective, fun v => ⟨⟨v, hall v⟩, rfl⟩⟩)
  have hm : HasPathBudget ((G.induce S).map (Function.Embedding.subtype _))
      (Fintype.card V / 2) := ⟨D.map (Function.Embedding.subtype _), by simpa [hc] using hD⟩
  simpa only [he] using hm

/-- Floor decompositions on disjoint, covering, neighbour-closed parts assemble
to a floor decomposition on all vertices, including empty parts and isolates. -/
theorem floor_of_closed_partition (S T : Set V)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hcover : S ∪ T = Set.univ) (hdis : Disjoint S T)
    (hs : ∀ v ∈ S, G.neighborSet v ⊆ S)
    (ht : ∀ v ∈ T, G.neighborSet v ⊆ T)
    (hS : HasPathBudget (G.induce S) (Fintype.card S / 2))
    (hT : HasPathBudget (G.induce T) (Fintype.card T / 2)) :
    HasPathBudget G (Fintype.card V / 2) := by
  classical
  let A := (G.induce S).spanningCoe
  let B := (G.induce T).spanningCoe
  have hA (a b : V) (h : A.Adj a b) : a ∈ S := by
    obtain ⟨p, q, _, hp, _⟩ := (SimpleGraph.map_adj (Function.Embedding.subtype _)
      (G.induce S) a b).mp h
    exact hp ▸ p.property
  have hB (a b : V) (h : B.Adj a b) : a ∈ T := by
    obtain ⟨p, q, _, hp, _⟩ := (SimpleGraph.map_adj (Function.Embedding.subtype _)
      (G.induce T) a b).mp h
    exact hp ▸ p.property
  have he : A ⊔ B = G := by
    apply le_antisymm
    · exact sup_le (G.spanningCoe_induce_le S) (G.spanningCoe_induce_le T)
    · intro a b hab
      have ha : a ∈ S ∪ T := by rw [hcover]; trivial
      rcases ha with ha | ha
      · exact Or.inl ((SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce S) a b).mpr
          ⟨⟨a, ha⟩, ⟨b, hs a ha hab⟩, hab, rfl, rfl⟩)
      · exact Or.inr ((SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce T) a b).mpr
          ⟨⟨a, ha⟩, ⟨b, ht a ha hab⟩, hab, rfl, rfl⟩)
  have hd : Disjoint A.edgeSet B.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro ha hb
      exact Set.disjoint_left.mp hdis (hA a b ha) (hB a b hb)
  have hcu : S.toFinset ∪ T.toFinset = Finset.univ := by
    ext v
    simpa using Set.ext_iff.mp hcover v
  have hci : S.toFinset ∩ T.toFinset = ∅ := by
    ext v
    simp only [Finset.mem_inter, Set.mem_toFinset, Finset.notMem_empty, iff_false, not_and]
    exact fun hv hw => Set.disjoint_left.mp hdis hv hw
  have hn := Finset.card_union_add_card_inter S.toFinset T.toFinset
  simp only [hcu, hci, Finset.card_univ, Finset.card_empty, Nat.add_zero,
    Set.toFinset_card] at hn
  obtain ⟨D, hD⟩ := hS
  obtain ⟨E, hE⟩ := hT
  obtain ⟨F, hF⟩ := (D.map (Function.Embedding.subtype _)).union_disjoint
    (E.map (Function.Embedding.subtype _)) hd
  have hout : HasPathBudget (A ⊔ B) (Fintype.card V / 2) := by
    refine ⟨F, ?_⟩
    simp only [Decomposition.map_size] at hF
    omega
  simpa only [he] using hout

end Gallai
