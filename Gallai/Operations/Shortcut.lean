/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Gallai.Foundations.HubProfiles
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Replacing a displayed two-edge run by its shortcut -/

namespace Gallai

open scoped Finset

universe u
variable {V : Type u} {G : SimpleGraph V} {a b x y z : V}

/-- Extract the actual two-edge run around an internal supported vertex.
The outer walks may be nil; no carrier-avoidance or selection premise is added. -/
theorem exists_internal_run (P : G.Walk a b) (hz : z ∈ P.support)
    (ha : a ≠ z) (hb : z ≠ b) :
    ∃ (x y : V) (L : G.Walk a x) (R : G.Walk y b)
      (hxz : G.Adj x z) (hzy : G.Adj z y),
      P = L.append (.cons hxz (.cons hzy R)) := by
  obtain ⟨L, R, hP⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hz
  obtain ⟨x, hzx, L', hL⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne ha.symm L.reverse
  obtain ⟨y, hzy, R', hR⟩ :=
    SimpleGraph.Walk.exists_eq_cons_of_ne hb R
  refine ⟨x, y, L'.reverse, R', hzx.symm, hzy, ?_⟩
  have hleft : L = L'.reverse.concat hzx.symm := by
    have h := congrArg SimpleGraph.Walk.reverse hL
    simpa only [SimpleGraph.Walk.reverse_reverse, SimpleGraph.Walk.reverse_cons,
      SimpleGraph.Walk.concat_eq_append] using h
  rw [hP, hleft, hR, SimpleGraph.Walk.concat_append]

/-- Removing the middle vertex from a displayed run preserves simplicity. -/
theorem isPath_shortcut (P : G.Walk a x) (Q : G.Walk y b)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : G.Adj x y)
    (hp : (P.append (.cons hxz (.cons hzy Q))).IsPath) :
    (P.append (.cons hxy Q)).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  have hn := hp.support_nodup
  simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
    List.tail_cons] at hn ⊢
  exact hn.sublist ((List.Sublist.refl P.support).append
    ((List.Sublist.refl Q.support).cons z))

/-- Build the nonempty shortcut path, allowing either outer walk to be nil. -/
def NonemptyPath.shortcut (P : G.Walk a x) (Q : G.Walk y b)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : G.Adj x y)
    (hp : (P.append (.cons hxz (.cons hzy Q))).IsPath) : NonemptyPath G where
  start := a
  finish := b
  walk := P.append (.cons hxy Q)
  isPath := isPath_shortcut P Q hxz hzy hxy hp
  nonempty := by
    intro hn
    have h := hn.length_eq_zero
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons] at h
    omega

/-- Exact balance: remove the two run edges and introduce exactly the shortcut. -/
theorem NonemptyPath.shortcut_edge_count [DecidableEq V]
    (P : G.Walk a x) (Q : G.Walk y b)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : G.Adj x y)
    (hp : (P.append (.cons hxz (.cons hzy Q))).IsPath) (e : Sym2 V) :
    (NonemptyPath.shortcut P Q hxz hzy hxy hp).walk.edges.count e +
        (if s(x, z) = e then 1 else 0) + (if s(z, y) = e then 1 else 0) =
      (P.append (.cons hxz (.cons hzy Q))).edges.count e +
        (if s(x, y) = e then 1 else 0) := by
  simp only [shortcut, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
    List.count_append, List.count_cons]
  split <;> split <;> split <;> simp_all <;> omega

/-- The suppressed vertex is absent from the resulting carrier. -/
theorem NonemptyPath.shortcut_notMem_support
    (P : G.Walk a x) (Q : G.Walk y b)
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : G.Adj x y)
    (hp : (P.append (.cons hxz (.cons hzy Q))).IsPath) :
    z ∉ (NonemptyPath.shortcut P Q hxz hzy hxy hp).walk.support := by
  have hn := hp.support_nodup
  simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
    List.tail_cons] at hn
  have hd := List.disjoint_of_nodup_append hn
  have hq := (List.nodup_cons.mp hn.of_append_right).1
  simp only [shortcut, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_cons, List.tail_cons, List.mem_append, not_or]
  exact ⟨fun hz => hd hz (List.mem_cons_self), hq⟩

/-- A degree-two vertex with no endpoints has exactly one containing carrier,
and that occurrence is internal. This selects the carrier to suppress. -/
theorem Decomposition.degree_two_unique_carrier [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (D : Decomposition G) (z : V)
    (hd : G.degree z = 2) (hz : D.endpointCount z = 0) :
    ∃ i : Fin D.size, (D.path i).start ≠ z ∧ (D.path i).finish ≠ z ∧
      ∀ j, z ∈ (D.path j).walk.support ↔ j = i := by
  have hb := D.degree_eq_endpoint_add_twice_through z
  have hc : #(D.throughCarriers z) = 1 := by
    rw [D.card_throughCarriers]
    omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have ht : D.terminalCarriers z = ∅ :=
    Finset.card_eq_zero.mp ((D.card_terminalCarriers z).trans hz)
  have himem : i ∈ D.throughCarriers z := by rw [hi]; simp
  have hip := (Finset.mem_filter.mp himem).2
  refine ⟨i, hip.2.1, hip.2.2, ?_⟩
  intro j
  rw [D.mem_support_iff_terminal_or_through, ht, hi]
  simp

/-- Locate the prescribed neighbour pair, in either orientation, on the unique
carrier through a degree-two vertex with zero endpoints. -/
theorem Decomposition.exists_suppression_run [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (D : Decomposition G) (z x y : V)
    (hd : G.degree z = 2) (hz : D.endpointCount z = 0)
    (hn : ∀ v, G.Adj z v → v = x ∨ v = y) :
    ∃ (i : Fin D.size) (u v : V)
      (L : G.Walk (D.path i).start u) (R : G.Walk v (D.path i).finish)
      (huz : G.Adj u z) (hzv : G.Adj z v),
      (D.path i).walk = L.append (.cons huz (.cons hzv R)) ∧
      ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∧
      ∀ j, j ≠ i → z ∉ (D.path j).walk.support := by
  obtain ⟨i, hs, ht, hi⟩ := D.degree_two_unique_carrier z hd hz
  obtain ⟨u, v, L, R, huz, hzv, he⟩ :=
    exists_internal_run (D.path i).walk ((hi i).mpr rfl) hs ht.symm
  have hp := (D.path i).isPath
  rw [he] at hp
  have huv : u ≠ v := by
    intro h
    have havoid := (SimpleGraph.Walk.cons_isPath_iff huz (.cons hzv R)).mp
      hp.of_append_right
    apply havoid.2
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
    exact Or.inr (h ▸ R.start_mem_support)
  have hu := hn u huz.symm
  have hv := hn v hzv
  refine ⟨i, u, v, L, R, huz, hzv, he, ?_, ?_⟩
  · rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (huv rfl).elim
  · intro j hj hmem
    exact hj ((hi j).mp hmem)

end Gallai
