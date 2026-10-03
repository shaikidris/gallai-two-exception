/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryComponentPartition
public import Gallai.TwoException.OrdinaryTriangleSelection

@[expose] public section

/-! # Exhaustive actual contact shapes in ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The actual contact packet at a singleton component is its unique contact. -/
theorem ordinary_singleton_contact_packet
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (w : evenVertices G) (hsupp : C.supp = {w}) (hw : w ∈ S) :
    ordinaryComponentPacket G S C = {w} := by
  classical
  ext t
  simp only [ordinaryComponentPacket, Finset.mem_filter, hsupp, Set.mem_singleton_iff,
    Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · intro ht
    subst t
    exact ⟨hw, rfl⟩

/-- Every touched ordinary component gives an isolate or one of the four
nonempty contact subsets of a triangle containing the chosen contact.
The labels and support are extracted from bare minimality, not supplied. -/
theorem bare_ordinary_contact_shapes
    (h : V) (z w : evenVertices G)
    (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S) :
    (C.supp = {w} ∧ ordinaryComponentPacket G S C = {w}) ∨
    ∃ b c : evenVertices G, C.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      (ordinaryComponentPacket G S C = {w} ∨
       ordinaryComponentPacket G S C = {w,b} ∨
       ordinaryComponentPacket G S C = {w,c} ∨
       ordinaryComponentPacket G S C = {w,b,c}) := by
  classical
  by_cases hn : ((evenSubgraph G).neighborSet w).Nonempty
  · obtain ⟨b,c, hs, hwb, hbc, hcw⟩ :=
      bare_ordinary_component_triangle_vertices h z w H C hz hwC hn
    refine Or.inr ⟨b,c,hs,hwb,hbc,hcw,?_⟩
    by_cases hb : b ∈ S <;> by_cases hc : c ∈ S
    · right; right; right
      ext t
      simp only [ordinaryComponentPacket, Finset.mem_filter, hs,
        Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · right; left
      ext t
      simp only [ordinaryComponentPacket, Finset.mem_filter, hs,
        Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · right; right; left
      ext t
      simp only [ordinaryComponentPacket, Finset.mem_filter, hs,
        Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · left
      ext t
      simp only [ordinaryComponentPacket, Finset.mem_filter, hs,
        Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_singleton]
      aesop
  · obtain hs | ⟨p,hp,hlen,hverts⟩ :=
      bare_ordinary_component_isolate_or_triangle h z w H C hz hwC
    · exact Or.inl ⟨hs, ordinary_singleton_contact_packet S C w hs hwS⟩
    · have hadj : ((evenSubgraph G).neighborSet w).Nonempty := by
        refine ⟨p.getVert 1, ?_⟩
        simpa using p.adj_getVert_succ (i := 0) (by omega)
      exact False.elim (hn hadj)

end Gallai.TwoException
