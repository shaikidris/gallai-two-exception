/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactStarAssembly
public import Gallai.TwoException.EarlyT3MateRestoration

@[expose] public section

/-! # Retained centre-neighbour guard for the T3/E5 puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E5RetainedGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- Original contact classification supplies E5's retained-neighbour guard.
The reserved triangle vertex is odd in the spoke-and-two-mate puncture; the two
opposite vertices are odd before contact restoration. -/
theorem t3_E5_retained_guard
    (a b c : evenVertices G) (hbc : G.Adj b c)
    (u x s p q h : V) (S : Finset V)
    (hab : (a : V) ≠ (b : V)) (hac : (a : V) ≠ (c : V))
    (hau : (a : V) ≠ u) (hua : G.Adj u a)
    (hap : (a : V) ≠ p) (haq : (a : V) ≠ q)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = p ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (haxs : (a : V) ≠ x) (hass : (a : V) ≠ s)
    (D : Decomposition (((starPuncture (G.deleteEdges {s((b : V),(c : V))}) u
      (insert (a : V) S)).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}))
    (hh : 2 ≤ D.endpointCount h) :
    ∀ t, (G.deleteEdges {s((b : V),(c : V))}).Adj u t → t ∉ S → t ≠ p →
      Odd ((G.deleteEdges {s((b : V),(c : V))}).degree t) ∨
      0 < D.endpointCount t := by
  classical
  let Q := G.deleteEdges {s((b : V),(c : V))}
  have hkeep := even_edge_deletion_even_preserved (G := G) b c hbc b.property c.property
  have haEvenQ : Even (Q.degree a) := by
    have hd := degree_delete_edge_of_ne G b c a hab hac
    have he : Even (G.degree a) := a.property
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet a).ncard
    rwa [hd]
  have huaQ : Q.Adj u a := by
    refine ⟨hua,?_⟩
    intro he
    rw [SimpleGraph.fromEdgeSet_adj] at he
    have he := Set.mem_singleton_iff.mp he.1
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hbu he.1.symm
    · exact hcu he.1.symm
  have haOdd := contact_star_leaf_odd (G := Q) u a (insert (a : V) S)
    (by simp) huaQ haEvenQ
  have haOddD : Odd ((((starPuncture Q u (insert (a : V) S)).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree a) := by
    have hd1 := degree_delete_edge_of_ne (starPuncture Q u (insert (a : V) S)) x s a haxs hass
    have hd2 := degree_delete_edge_of_ne ((starPuncture Q u (insert (a : V) S)).deleteEdges {s(x,s)}) q p a haq hap
    simp only [← SimpleGraph.ncard_neighborSet] at hd1 hd2 haOdd ⊢
    rw [hd2,hd1]
    exact haOdd
  intro t hut htS htp
  by_cases ho : Odd (Q.degree t)
  · exact Or.inl ho
  have heQ : Even (Q.degree t) := (Nat.even_or_odd _).resolve_right ho
  have heG := hkeep t heQ
  rcases hcontacts t hut.1 heG with ht | ht | ht | ht | ht | ht
  · exact False.elim (htS ht)
  · exact Or.inr (ht ▸ D.endpointCount_pos_of_odd_degree a haOddD)
  · exact False.elim (htp ht)
  · subst t
    have hd := degree_delete_edge_add_one G b c hbc
    have he : Even (G.degree b) := b.property
    simp only [← SimpleGraph.ncard_neighborSet] at hd he heQ
    change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet b).ncard at heQ
    rw [Nat.even_iff] at he heQ
    omega
  · subst t
    have hd := degree_delete_edge_add_one_other G b c hbc
    have he : Even (G.degree c) := c.property
    simp only [← SimpleGraph.ncard_neighborSet] at hd he heQ
    change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet c).ncard at heQ
    rw [Nat.even_iff] at he heQ
    omega
  · exact Or.inr (ht ▸ (by omega : 0 < D.endpointCount h))

end Gallai.TwoException
