/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # Component ceilings with a protected endpoint reserve -/

namespace Gallai.TwoException

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A ceiling-budget decomposition on the component of `y`, exposing `y`
twice, combines with floor decompositions on every other actual component. -/
theorem assemble_one_ceiling (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (D : Decomposition (G.induce (G.connectedComponentMk y).supp))
    (hD : D.size ≤ (Fintype.card (G.connectedComponentMk y).supp + 1) / 2)
    (hy : 2 ≤ D.endpointCount ⟨y, rfl⟩)
    (hf : ∀ C : G.ConnectedComponent, C ≠ G.connectedComponentMk y →
      HasPathBudget (G.induce C.supp) (Fintype.card C.supp / 2)) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  classical
  let C₀ := G.connectedComponentMk y
  let K (C : G.ConnectedComponent) := C.toSimpleGraph.spanningCoe
  let s : Finset G.ConnectedComponent := Finset.univ.erase C₀
  have hd : (s : Set G.ConnectedComponent).Pairwise
      (fun C B => Disjoint (K C).edgeSet (K B).edgeSet) := by
    intro C _ B _ hCB
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hc hb
      exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hCB)
        ((C.adj_spanningCoe_toSimpleGraph).mp hc).1
        ((B.adj_spanningCoe_toSimpleGraph).mp hb).1
  have he : Finset.univ.sup K = G := by
    rw [Finset.sup_eq_iSup]
    apply le_antisymm
    · exact iSup_le fun C => iSup_le fun _ => G.spanningCoe_induce_le C.supp
    · intro a b hab
      simp only [SimpleGraph.iSup_adj]
      exact ⟨G.connectedComponentMk a, Finset.mem_univ _,
        (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph _).mpr ⟨rfl, hab⟩⟩
  have hgraph : K C₀ ⊔ s.sup K = G := by
    rw [← Finset.sup_insert]
    have hins : insert C₀ s = Finset.univ := Finset.insert_erase (Finset.mem_univ _)
    rw [hins, he]
  have hdis : Disjoint (K C₀).edgeSet (s.sup K).edgeSet := by
    rw [Finset.sup_eq_iSup]
    simp only [SimpleGraph.edgeSet_iSup, Set.disjoint_iUnion_right]
    intro C hC
    have hne : C₀ ≠ C := (Finset.mem_erase.mp hC).1.symm
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hc hb
      exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hne)
        ((C₀.adj_spanningCoe_toSimpleGraph).mp hc).1
        ((C.adj_spanningCoe_toSimpleGraph).mp hb).1
  obtain ⟨E, hE⟩ := pathBudget_finset_sup s K (fun C => Fintype.card C.supp / 2) hd
    (fun C hC => by
      obtain ⟨P, hP⟩ := hf C (Finset.mem_erase.mp hC).1
      exact ⟨P.map (Function.Embedding.subtype _), by simpa using hP⟩)
  obtain ⟨F, hs, hends⟩ :=
    (D.map (Function.Embedding.subtype _)).union_disjoint_endpoints E hdis
  have htotal : (∑ C : G.ConnectedComponent, Fintype.card C.supp) = Fintype.card V := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  have hcard : (∑ C ∈ s, Fintype.card C.supp) + Fintype.card C₀.supp =
      Fintype.card V := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ _)]
    exact htotal
  have hdouble : 2 * (∑ C ∈ s, Fintype.card C.supp / 2) ≤
      ∑ C ∈ s, Fintype.card C.supp := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun C _ => by omega
  have hsize : F.size ≤ (Fintype.card V + 1) / 2 := by
    simp only [Decomposition.map_size] at hs
    change D.size ≤ (Fintype.card C₀.supp + 1) / 2 at hD
    omega
  have hexpose : 2 ≤ F.endpointCount y := by
    rw [hends y]
    have hmap := D.map_endpointCount (Function.Embedding.subtype _) ⟨y, rfl⟩
    change (D.map (Function.Embedding.subtype _)).endpointCount y =
      D.endpointCount ⟨y, rfl⟩ at hmap
    rw [hmap]
    omega
  have hout : ∃ F : Decomposition (K C₀ ⊔ s.sup K),
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount y :=
    ⟨F, hsize, hexpose⟩
  rwa [hgraph] at hout

end Gallai.TwoException
