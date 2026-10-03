/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.ESET
public import Gallai.Structure.SETIso

@[expose] public section

/-! # Explicit two-spoke ESET construction

The attachment constructor derives the graph equality in the literal ESET
definition from the connection vertex's exact neighbourhood.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A SET core with one odd and one even attachment is a type-ii ESET. -/
theorem isESETAt_of_two_neighbors (u : V)
    (hS : IsSET (G.induce {v | v ≠ u}))
    (x y : {v : V // v ≠ u})
    (hx : Odd ((G.induce {v | v ≠ u}).degree x))
    (hy : Even ((G.induce {v | v ≠ u}).degree y))
    (hn : ∀ v, G.Adj u v ↔ v = x.val ∨ v = y.val) : IsESETAt G u := by
  classical
  refine Or.inr ⟨hS, x, y, hx, hy, ?_⟩
  ext v w
  change G.Adj v w ↔
    (((G.induce {v | v ≠ u}).map (Function.Embedding.subtype _)).Adj v w ∨
      (SimpleGraph.edge u x.val).Adj v w) ∨ (SimpleGraph.edge u y.val).Adj v w
  constructor
  · intro hvw
    by_cases hv : v = u
    · subst v
      rcases (hn w).mp hvw with hw | hw
      · subst w
        exact Or.inl (Or.inr (by simp [SimpleGraph.edge_adj, x.property, x.property.symm]))
      · subst w
        exact Or.inr (by simp [SimpleGraph.edge_adj, y.property, y.property.symm])
    by_cases hw : w = u
    · subst w
      rcases (hn v).mp hvw.symm with hvx | hvy
      · subst v
        exact Or.inl (Or.inr (by simp [SimpleGraph.edge_adj, x.property]))
      · subst v
        exact Or.inr (by simp [SimpleGraph.edge_adj, y.property])
    · left
      left
      exact (SimpleGraph.map_adj (Function.Embedding.subtype _) _ v w).mpr
        ⟨⟨v, hv⟩, ⟨w, hw⟩, hvw, rfl, rfl⟩
  · rintro ((h | h) | h)
    · obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ v w).mp h
      exact hab
    · have he : SimpleGraph.edge u x.val ≤ G := by
        exact (SimpleGraph.edge_le_iff G).mpr (Or.inr ((hn x.val).mpr (Or.inl rfl)))
      exact he h
    · have he : SimpleGraph.edge u y.val ≤ G := by
        exact (SimpleGraph.edge_le_iff G).mpr (Or.inr ((hn y.val).mpr (Or.inr rfl)))
      exact he h

/-- Deleting the freshly inserted vertex from an induced attachment gives
exactly the original core, including when represented by nested subtypes. -/
def insertedCoreIso (S : Set V) (u : V) (hu : u ∉ S) :
    G.induce S ≃g (G.induce (insert u S)).induce
      {v | v ≠ ⟨u, Set.mem_insert u S⟩} where
  toFun v := ⟨⟨v, Set.mem_insert_of_mem u v.property⟩,
    fun he => hu (by
      have he' : v.val = u := congrArg Subtype.val he
      exact he' ▸ v.property)⟩
  invFun v := ⟨v.val.val, (Set.mem_insert_iff.mp v.val.property).resolve_left
    (fun he => v.property (Subtype.ext he))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intro a b; rfl

/-- Construct the ESET on an actual induced core plus a fresh connection
vertex from its two attachment edges and their opposite core parities. -/
theorem isESETAt_induce_insert (S : Set V) [DecidablePred (· ∈ S)]
    (u : V) (hu : u ∉ S) (hS : IsSET (G.induce S)) (x y : S)
    (hx : Odd ((G.induce S).degree x)) (hy : Even ((G.induce S).degree y))
    (hn : ∀ v ∈ S, G.Adj u v ↔ v = x.val ∨ v = y.val) :
    IsESETAt (G.induce (insert u S)) ⟨u, Set.mem_insert u S⟩ := by
  classical
  let f := insertedCoreIso (G := G) S u hu
  apply isESETAt_of_two_neighbors _ (hS.iso f) (f x) (f y)
    (by rw [f.degree_eq]; exact hx) (by rw [f.degree_eq]; exact hy)
  intro v
  constructor
  · intro hv
    have hvs : v.val ∈ S := (Set.mem_insert_iff.mp v.property).resolve_left
      (fun he => hv.ne (Subtype.ext he.symm))
    rcases (hn v hvs).mp hv with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)
  · rintro (he | he)
    · subst v
      exact (hn x x.property).mpr (Or.inl rfl)
    · subst v
      exact (hn y y.property).mpr (Or.inr rfl)

end Gallai
