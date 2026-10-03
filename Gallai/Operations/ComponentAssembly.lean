/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.FiniteUnion
public import Gallai.Operations.DecompositionMap
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Sum
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Floor-budget assembly over all connected components -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Floor decompositions of the actual connected components combine into a
floor decomposition of the whole graph, including isolates and the empty graph. -/
theorem floor_of_components (G : SimpleGraph V) [DecidableRel G.Adj]
    (hb : ∀ C : G.ConnectedComponent,
      HasPathBudget (G.induce C.supp) (Fintype.card C.supp / 2)) :
    HasPathBudget G (Fintype.card V / 2) := by
  classical
  let K (C : G.ConnectedComponent) := (G.induce C.supp).spanningCoe
  have hm (C : G.ConnectedComponent) (a b : V) (h : (K C).Adj a b) : a ∈ C.supp := by
    obtain ⟨p, q, _, hp, _⟩ :=
      (SimpleGraph.map_adj (Function.Embedding.subtype _) (G.induce C.supp) a b).mp h
    exact hp ▸ p.property
  have hd : (↑(Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).Pairwise
      (fun C D => Disjoint (K C).edgeSet (K D).edgeSet) := by
    intro C _ D _ hCD
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hc hd
      exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hCD)
        (hm C a b hc) (hm D a b hd)
  have he : Finset.univ.sup K = G := by
    rw [Finset.sup_eq_iSup]
    apply le_antisymm
    · exact iSup_le fun C => iSup_le fun _ => G.spanningCoe_induce_le C.supp
    · intro a b hab
      simp only [SimpleGraph.iSup_adj]
      refine ⟨G.connectedComponentMk a, Finset.mem_univ _, ?_⟩
      exact (SimpleGraph.map_adj (Function.Embedding.subtype _)
        (G.induce (G.connectedComponentMk a).supp) a b).mpr
        ⟨⟨a, rfl⟩, ⟨b, (G.connectedComponentMk a).mem_supp_of_adj_mem_supp rfl hab⟩,
          hab, rfl, rfl⟩
  have hc : (∑ C : G.ConnectedComponent, Fintype.card C.supp) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  have hn : (∑ C : G.ConnectedComponent, Fintype.card C.supp / 2) ≤
      Fintype.card V / 2 := by
    have hmul : 2 * (∑ C : G.ConnectedComponent, Fintype.card C.supp / 2) ≤
        ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun C _ => by omega
    omega
  obtain ⟨D, hD⟩ := pathBudget_finset_sup Finset.univ K
    (fun C => Fintype.card C.supp / 2) hd (fun C _ => by
      obtain ⟨E, hE⟩ := hb C
      exact ⟨E.map (Function.Embedding.subtype _), by simpa using hE⟩)
  have hout : HasPathBudget (Finset.univ.sup K) (Fintype.card V / 2) :=
    ⟨D, hD.trans hn⟩
  simpa only [he] using hout

end Gallai
