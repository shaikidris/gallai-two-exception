/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EvenSubgraph
public import Mathlib.Data.Set.Card

@[expose] public section

/-! # Literal triangle components and their local consequences

Claim 3's odd-leaf branch assumes that every original even-graph component
is a triangle. Cardinality and completeness are both retained explicitly.
-/

namespace Gallai

variable {V : Type*} [Fintype V] {K : SimpleGraph V}

/-- Each connected component has exactly three vertices and is complete. -/
def ComponentsAreTriangles (K : SimpleGraph V) : Prop :=
  ∀ C : K.ConnectedComponent, C.supp.ncard = 3 ∧ C.toSimpleGraph = ⊤

/-- Three distinct vertices joined by a two-edge path exhaust their triangle
component. The closing edge exists, and no fourth vertex neighbours the middle. -/
theorem ComponentsAreTriangles.close_path (ht : ComponentsAreTriangles K)
    {a b c : V} (hab : K.Adj a b) (hbc : K.Adj b c) (hac : a ≠ c) :
    K.Adj a c ∧ ∀ v, K.Adj b v → v = a ∨ v = c := by
  classical
  let C := K.connectedComponentMk a
  have ha : a ∈ C.supp := rfl
  have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hab
  have hc : c ∈ C.supp := C.mem_supp_of_adj_mem_supp hb hbc
  have hs : ({a, b, c} : Finset V) ⊆ C.supp.toFinset := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> simpa using (show _ from ‹_ ∈ C.supp›)
  have hcard : C.supp.toFinset.card = 3 := by
    simpa only [Set.ncard_eq_toFinset_card'] using (ht C).1
  have hthree : ({a, b, c} : Finset V).card = 3 := by
    simp [hab.ne, hbc.ne, hac]
  have heq : ({a, b, c} : Finset V) = C.supp.toFinset :=
    Finset.eq_of_subset_of_card_le hs (by omega)
  refine ⟨?_, ?_⟩
  · have hcomplete := (ht C).2
    have he : C.toSimpleGraph.Adj ⟨a, ha⟩ ⟨c, hc⟩ := by
      rw [hcomplete]
      exact fun hh => hac (congrArg Subtype.val hh)
    exact he
  · intro v hv
    have hm : v ∈ C.supp.toFinset := by
      simpa using C.mem_supp_of_adj_mem_supp hb hv
    rw [← heq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · exact (hv.ne h.symm).elim
    · exact Or.inr h

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The triangle-component condition on the induced even graph gives exact
original even-neighbour control, rather than an ordinary-degree bound. -/
theorem even_triangle_close_path (ht : ComponentsAreTriangles (evenSubgraph G))
    {a b c : V} (ha : Even (G.degree a)) (hb : Even (G.degree b))
    (hc : Even (G.degree c)) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) :
    G.Adj a c ∧ ∀ v, Even (G.degree v) → G.Adj b v → v = a ∨ v = c := by
  have h := ht.close_path (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩)
    hab hbc (fun hh => hac (congrArg Subtype.val hh))
  refine ⟨h.1, ?_⟩
  intro v hv hav
  rcases h.2 ⟨v, hv⟩ hav with he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (congrArg Subtype.val he)

end Gallai
