/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.PendantExtension
public import Gallai.Structure.WalkPuncture
public import Gallai.Structure.SET
public import Gallai.Inputs.FloorOrSET
public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # The arbitrary corridor auxiliary

The bare-hub reduction deletes a simple even corridor ending at a degree-three
vertex `a`, deletes the two remaining incident even edges `aq` and `ar`, and
attaches a fresh pendant edge at the prescribed bare vertex.  This file names
that graph operation.  It records only literal adjacency and containment;
parity, component and path-decomposition arguments belong to the reduction
which supplies the corridor hypotheses.
-/

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete a corridor and the two additional terminal spokes at its endpoint. -/
def corridorPuncture {x a : V} (p : G.Walk x a) (q r : V) : SimpleGraph V :=
  (walkPuncture G p).deleteEdges {s(a, q), s(a, r)}

/-- The two terminal spoke deletions are unordered. -/
theorem corridorPuncture_swap {x a : V} (p : G.Walk x a) (q r : V) :
    corridorPuncture G p q r = corridorPuncture G p r q := by
  unfold corridorPuncture
  congr 1
  ext e
  simp [or_comm]

/-- The two terminal-spoke deletions can be performed sequentially after the
corridor puncture.  This normal form exposes the three exact degree changes
at the terminal endpoint. -/
theorem corridorPuncture_eq_delete_terminal_spokes {x a q r : V}
    (p : G.Walk x a) :
    corridorPuncture G p q r =
      ((walkPuncture G p).deleteEdges {s(a, q)}).deleteEdges {s(a, r)} := by
  rw [SimpleGraph.deleteEdges_deleteEdges]
  unfold corridorPuncture
  congr 1

/-- At a nontrivial corridor terminal, the puncture removes exactly the
terminal corridor edge and the two terminal spokes. -/
theorem degree_corridorPuncture_terminal_add_three
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support)
    (hqr : q ≠ r) (haq : G.Adj a q) (har : G.Adj a r) :
    (corridorPuncture G p q r).degree a + 3 = G.degree a := by
  have haqWalk : (walkPuncture G p).Adj a q := by
    apply (walkPuncture_adj_iff G p).mpr
    refine ⟨haq, ?_⟩
    intro he
    apply hqoff
    exact p.snd_mem_support_of_mem_edges he
  have harWalk : (walkPuncture G p).Adj a r := by
    apply (walkPuncture_adj_iff G p).mpr
    refine ⟨har, ?_⟩
    intro he
    apply hroff
    exact p.snd_mem_support_of_mem_edges he
  have harAfter : ((walkPuncture G p).deleteEdges {s(a, q)}).Adj a r := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨harWalk, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro e
    rcases Sym2.eq_iff.mp e with e | e
    · exact hqr e.2.symm
    · exact haq.ne e.1
  have h1 := degree_walkPuncture_end_add_one G p hp hnil
  have h2 := degree_delete_edge_add_one (walkPuncture G p) a q haqWalk
  have h3 := degree_delete_edge_add_one ((walkPuncture G p).deleteEdges {s(a, q)}) a r harAfter
  have hneigh : (corridorPuncture G p q r).neighborFinset a =
      (((walkPuncture G p).deleteEdges {s(a, q)}).deleteEdges {s(a, r)}).neighborFinset a := by
    rw [SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.neighborFinset_eq_filter]
    ext z
    simp [corridorPuncture, SimpleGraph.deleteEdges_adj, and_assoc, and_left_comm,
      and_comm, not_or]
  have hdeg : (corridorPuncture G p q r).degree a =
      (((walkPuncture G p).deleteEdges {s(a, q)}).deleteEdges {s(a, r)}).degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree, hneigh]
  rw [hdeg]
  omega

/-- The full auxiliary also adds a fresh pendant edge at `h`. -/
abbrev corridorAuxiliary {x a : V} (p : G.Walk x a) (q r h : V) :
    SimpleGraph (V ⊕ Unit) :=
  pendantExtension (corridorPuncture G p q r) h

/-- If the terminal is originally even, deleting its corridor edge and two
additional even spokes makes it odd; the pendant extension preserves that
parity away from its attachment. -/
theorem odd_degree_corridorAuxiliary_terminal_center
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support)
    (hqr : q ≠ r) (haq : G.Adj a q) (har : G.Adj a r)
    (haeven : Even (G.degree a)) (hah : a ≠ h) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl a)) := by
  rw [pendantExtension_odd_old_ne (corridorPuncture G p q r) h a hah]
  apply Nat.not_even_iff_odd.mp
  intro hpuncture
  have hsum : Even ((corridorPuncture G p q r).degree a + 3) := by
    rw [degree_corridorPuncture_terminal_add_three G p hp hnil hqoff hroff hqr haq har]
    exact haeven
  have hthree : Even 3 := (Nat.even_add.mp hsum).mp hpuncture
  rcases hthree with ⟨k, hk⟩
  omega

/-- The complete corridor auxiliary is likewise invariant under swapping the
two terminal spoke leaves. -/
theorem corridorAuxiliary_swap {x a : V} (p : G.Walk x a) (q r h : V) :
    corridorAuxiliary G p q r h = corridorAuxiliary G p r q h := by
  unfold corridorAuxiliary
  rw [corridorPuncture_swap]

@[simp]
theorem corridorPuncture_le {x a : V} (p : G.Walk x a) (q r : V) :
    corridorPuncture G p q r ≤ G := by
  exact le_trans (SimpleGraph.deleteEdges_le _) (walkPuncture_le G p)

/-- A surviving old edge of the corridor puncture is exactly an original edge
which is neither a corridor edge nor one of the two terminal spokes. -/
theorem corridorPuncture_adj_iff {x a q r s t : V} (p : G.Walk x a) :
    (corridorPuncture G p q r).Adj s t ↔
      G.Adj s t ∧ s(s, t) ∉ p.edges ∧ s(s, t) ≠ s(a, q) ∧ s(s, t) ≠ s(a, r) := by
  simp [corridorPuncture, walkPuncture_adj_iff, and_assoc, and_left_comm,
    and_comm, not_or]

/-- The old-vertex restriction of the pendant auxiliary has precisely the
adjacencies of its corridor puncture. -/
theorem corridorAuxiliary_adj_old_iff {x a q r h s t : V} (p : G.Walk x a) :
    (corridorAuxiliary G p q r h).Adj (.inl s) (.inl t) ↔
      G.Adj s t ∧ s(s, t) ∉ p.edges ∧ s(s, t) ≠ s(a, q) ∧ s(s, t) ≠ s(a, r) := by
  rw [pendantExtension_adj_old, corridorPuncture_adj_iff]

/-- Every predecessor edge at a proper corridor position is absent from the
auxiliary.  This is the literal missing-edge premise for a restoration step
towards that position. -/
theorem corridorAuxiliary_not_adj_internal_previous
    {x a q r h : V} (p : G.Walk x a) (i : ℕ)
    (hi : 0 < i) (hiend : i < p.length) :
    ¬ (corridorAuxiliary G p q r h).Adj
      (.inl (p.getVert i)) (.inl (p.getVert (i - 1))) := by
  intro hadj
  have hnot := (corridorAuxiliary_adj_old_iff G p).mp hadj |>.2.1
  apply hnot
  rw [Sym2.eq_swap]
  apply p.mk_mem_edges_iff_exists.mpr
  refine ⟨i - 1, by omega, ?_⟩
  rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]

/-- An original old-vertex edge crossing a connected component of the full
corridor auxiliary must be one of the deleted edges.  This is the literal
boundary transport behind the later non-cut and hanging-SET alternatives. -/
theorem corridorAuxiliary_component_crossing_is_deleted
    {x a q r h s t : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hs : (.inl s : V ⊕ Unit) ∈ C.supp)
    (ht : (.inl t : V ⊕ Unit) ∉ C.supp)
    (hst : G.Adj s t) :
    s(s, t) ∈ p.edges ∨ s(s, t) = s(a, q) ∨ s(s, t) = s(a, r) := by
  by_contra hnot
  push Not at hnot
  have haux : (corridorAuxiliary G p q r h).Adj (.inl s) (.inl t) :=
    (corridorAuxiliary_adj_old_iff G p).mpr
      ⟨hst, hnot.1, hnot.2.1, hnot.2.2⟩
  exact ht (C.mem_supp_of_adj_mem_supp hs haux)

/-- If a component meets the deleted corridor interface only at the terminal
leaf `q`, then its original boundary is exactly the deleted terminal spoke
`q-a`.  Proper internal corridor vertices are excluded by their literal walk
indices, so this is a structural boundary statement rather than a parity
argument. -/
theorem corridorAuxiliary_component_crossing_is_terminal_q_of_one_contact
    {x a q r h u v : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hqC : (.inl q : V ⊕ Unit) ∈ C.supp)
    (hxC : (.inl x : V ⊕ Unit) ∉ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hrC : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (huC : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hvC : (.inl v : V ⊕ Unit) ∉ C.supp)
    (huv : G.Adj u v) :
    u = q ∧ v = a := by
  obtain hwalk | hqa | hra :=
    corridorAuxiliary_component_crossing_is_deleted G p C huC hvC huv
  · have huSupp : u ∈ p.support := p.fst_mem_support_of_mem_edges hwalk
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at huSupp
    obtain ⟨i, hi, hile⟩ := huSupp
    by_cases hi0 : i = 0
    · exact False.elim (hxC (by
        subst i
        have hux : u = x := by simpa using hi.symm
        exact hux ▸ huC))
    by_cases hilast : i = p.length
    · exact False.elim (haC (by
        subst i
        have hua : u = a := by simpa using hi.symm
        exact hua ▸ huC))
    · exact False.elim (hinternal i (Nat.pos_of_ne_zero hi0)
        (Nat.lt_of_le_of_ne (by simpa using hile) hilast) (by simpa [hi] using huC))
  · rcases Sym2.eq_iff.mp hqa with h | h
    · exact False.elim (haC (by simpa [h.1] using huC))
    · exact ⟨h.1, h.2⟩
  · rcases Sym2.eq_iff.mp hra with h | h
    · exact False.elim (haC (by simpa [h.1] using huC))
    · exact False.elim (hrC (by simpa [h.1] using huC))

/-- Symmetrically, if the unique terminal-leaf contact is `r`, its original
boundary is exactly the deleted terminal spoke `r-a`. -/
theorem corridorAuxiliary_component_crossing_is_terminal_r_of_one_contact
    {x a q r h u v : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hrC : (.inl r : V ⊕ Unit) ∈ C.supp)
    (hxC : (.inl x : V ⊕ Unit) ∉ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hqC : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (huC : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hvC : (.inl v : V ⊕ Unit) ∉ C.supp)
    (huv : G.Adj u v) :
    u = r ∧ v = a := by
  obtain hwalk | hqa | hra :=
    corridorAuxiliary_component_crossing_is_deleted G p C huC hvC huv
  · have huSupp : u ∈ p.support := p.fst_mem_support_of_mem_edges hwalk
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at huSupp
    obtain ⟨i, hi, hile⟩ := huSupp
    by_cases hi0 : i = 0
    · exact False.elim (hxC (by
        subst i
        have hux : u = x := by simpa using hi.symm
        exact hux ▸ huC))
    by_cases hilast : i = p.length
    · exact False.elim (haC (by
        subst i
        have hua : u = a := by simpa using hi.symm
        exact hua ▸ huC))
    · exact False.elim (hinternal i (Nat.pos_of_ne_zero hi0)
        (Nat.lt_of_le_of_ne (by simpa using hile) hilast) (by simpa [hi] using huC))
  · rcases Sym2.eq_iff.mp hqa with h | h
    · exact False.elim (haC (by simpa [h.1] using huC))
    · exact False.elim (hqC (by simpa [h.1] using huC))
  · rcases Sym2.eq_iff.mp hra with h | h
    · exact False.elim (haC (by simpa [h.1] using huC))
    · exact ⟨h.1, h.2⟩

/-- The old vertices in a corridor-auxiliary component. -/
def corridorAuxiliary_oldSet {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent) : Set V :=
  {v | (.inl v : V ⊕ Unit) ∈ C.supp}

@[simp] theorem mem_corridorAuxiliary_oldSet {x a q r h v : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent) :
    v ∈ corridorAuxiliary_oldSet G p C ↔ (.inl v : V ⊕ Unit) ∈ C.supp := Iff.rfl

/-- If the fresh pendant leaf is outside an auxiliary component, its support
is canonically equivalent to the old vertices that it contains. -/
noncomputable def corridorAuxiliary_oldComponentEquiv {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    C.supp ≃ corridorAuxiliary_oldSet G p C where
  toFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl v => exact ⟨v, hz⟩
    | inr u => cases u; exact False.elim (hleaf hz)
  invFun z := ⟨.inl z.val, z.property⟩
  left_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl v => rfl
    | inr u => cases u; exact False.elim (hleaf hz)
  right_inv z := by
    rcases z with ⟨z, hz⟩
    rfl

/-- When a pendant-auxiliary component avoids the fresh leaf and every
corridor vertex, none of the puncture's deleted edges lies inside it.
Consequently its induced graph is isomorphic to the original graph induced on
its old vertices. -/
noncomputable def corridorAuxiliary_oldComponentIso_of_avoids_support
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hsupport : ∀ z : V, (.inl z : V ⊕ Unit) ∈ C.supp → z ∉ p.support) :
    (corridorAuxiliary G p q r h).induce C.supp ≃g G.induce (corridorAuxiliary_oldSet G p C) where
  __ := corridorAuxiliary_oldComponentEquiv G p C hleaf
  map_rel_iff' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        change G.Adj u v ↔ (corridorAuxiliary G p q r h).Adj (.inl u) (.inl v)
        constructor
        · intro huv
          apply (corridorAuxiliary_adj_old_iff G p).mpr
          refine ⟨huv, ?_, ?_, ?_⟩
          · intro hedge
            exact hsupport u hu (p.fst_mem_support_of_mem_edges hedge)
          · intro hspoke
            rcases Sym2.eq_iff.mp hspoke with hspoke | hspoke
            · exact hsupport u hu (by simpa [hspoke.1] using p.end_mem_support)
            · exact hsupport v hv (by simpa [hspoke.2] using p.end_mem_support)
          · intro hspoke
            rcases Sym2.eq_iff.mp hspoke with hspoke | hspoke
            · exact hsupport u hu (by simpa [hspoke.1] using p.end_mem_support)
            · exact hsupport v hv (by simpa [hspoke.2] using p.end_mem_support)
        · intro huv
          exact (corridorAuxiliary_adj_old_iff G p).mp huv |>.1
      | inr z =>
        cases z
        exact False.elim (hleaf hv)
    | inr z =>
      cases z
      exact False.elim (hleaf hu)

/-- A SET certificate on a component avoiding the full deleted corridor
interface transfers to the original induced old-vertex core. -/
theorem corridorAuxiliary_old_component_isSET_of_avoids_support
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ corridorAuxiliary_oldSet G p C)]
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hsupport : ∀ z : V, (.inl z : V ⊕ Unit) ∈ C.supp → z ∉ p.support)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    IsSET (G.induce (corridorAuxiliary_oldSet G p C)) := by
  classical
  exact SimpleGraph.Iso.isSET_map
    (corridorAuxiliary_oldComponentIso_of_avoids_support G p C hleaf hsupport) hset

/-- A SET component of a corridor auxiliary containing an old vertex and
excluding the fresh pendant leaf contains a distinct second old vertex.  This
is intrinsic to SET: every vertex of the induced component has degree at
least two. -/
theorem corridorAuxiliary_set_component_exists_second_old_of_mem
    {x a q r h v : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hv : (.inl v : V ⊕ Unit) ∈ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    ∃ t : V, (.inl t : V ⊕ Unit) ∈ C.supp ∧ t ≠ v := by
  let vC : C.supp := ⟨.inl v, hv⟩
  have hdegree : 2 ≤ ((corridorAuxiliary G p q r h).induce C.supp).degree vC :=
    hset.two_le_degree vC
  have hcard : 0 <
      (((corridorAuxiliary G p q r h).induce C.supp).neighborFinset vC).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  cases hzval : z.val with
  | inl t =>
    have hzC : (.inl t : V ⊕ Unit) ∈ C.supp := by
      simpa [hzval] using z.property
    refine ⟨t, hzC, ?_⟩
    intro htv
    have hAdj : ((corridorAuxiliary G p q r h).induce C.supp).Adj vC z := by
      simpa using hz
    apply hAdj.ne
    apply Subtype.ext
    simp [vC, hzval, htv]
  | inr u =>
    cases u
    apply False.elim
    apply hleaf
    simpa [hzval] using z.property

/-- A component avoiding the fresh pendant leaf also avoids its old
attachment: the two vertices are adjacent in the auxiliary. -/
theorem corridorAuxiliary_attachment_not_mem_of_leaf_not_mem
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    (.inl h : V ⊕ Unit) ∉ C.supp := by
  intro hh
  apply hleaf
  exact C.mem_supp_of_adj_mem_supp hh
    ((pendantExtension_adj_new (corridorPuncture G p q r) h (.inl h)).mpr rfl).symm

/-- Endpoint and proper-internal avoidance imply avoidance of every old
corridor-support vertex. -/
theorem corridorAuxiliary_component_avoids_support_of_endpoint_internal_avoids
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp) :
    ∀ z : V, (.inl z : V ⊕ Unit) ∈ C.supp → z ∉ p.support := by
  intro z hz hzsupp
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hzsupp
  obtain ⟨i, hzi, hile⟩ := hzsupp
  by_cases hi0 : i = 0
  · apply hx
    subst i
    have hzx : z = x := by simpa using hzi.symm
    simpa [hzx] using hz
  by_cases hilast : i = p.length
  · apply ha
    subst i
    have hza : z = a := by simpa using hzi.symm
    simpa [hza] using hz
  · exact hinternal i (Nat.pos_of_ne_zero hi0)
      (Nat.lt_of_le_of_ne (by simpa using hile) hilast) (by simpa [hzi] using hz)

/-- An `x`-side SET component of a leaf-free corridor auxiliary makes the
corridor start `x` a cut vertex of the original graph.  After deleting `x`, a
path from the pendant attachment to a second old SET vertex cannot enter the
component: every crossing would be a deleted corridor edge and its endpoint
inside the component would have to be `x`. -/
theorem corridorAuxiliary_x_side_set_forces_not_connected
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hhx : h ≠ x)
    (hxC : (.inl x : V ⊕ Unit) ∈ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hqC : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hrC : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hinternal : ∀ i : ℕ, 0 < i → i < p.length →
      (.inl (p.getVert i) : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    ¬ (G.induce {v | v ≠ x}).Connected := by
  have hhC : (.inl h : V ⊕ Unit) ∉ C.supp :=
    corridorAuxiliary_attachment_not_mem_of_leaf_not_mem G p C hleaf
  obtain ⟨t, htC, htx⟩ :=
    corridorAuxiliary_set_component_exists_second_old_of_mem G p C hxC hleaf hset
  intro hconn
  have hreach : (G.induce {v | v ≠ x}).Reachable ⟨h, hhx⟩ ⟨t, htx⟩ :=
    hconn ⟨h, hhx⟩ ⟨t, htx⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hnoenter : ∀ {u v : {v : V | v ≠ x}},
      (.inl u.val : V ⊕ Unit) ∉ C.supp →
        (.inl v.val : V ⊕ Unit) ∈ C.supp →
          (G.induce {v | v ≠ x}).Adj u v → False := by
    intro u v huC hvC huv
    rcases corridorAuxiliary_component_crossing_is_deleted G p C hvC huC huv.symm with
        hwalk | hqa | hra
    · have hvSupp : v.val ∈ p.support := p.fst_mem_support_of_mem_edges hwalk
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hvSupp
      obtain ⟨i, hvi, hile⟩ := hvSupp
      by_cases hi0 : i = 0
      · have hvx : v.val = x := by simpa [hi0] using hvi.symm
        exact v.property hvx
      by_cases hilast : i = p.length
      · exact False.elim (haC (by
          subst i
          have hva : v.val = a := by simpa using hvi.symm
          simpa [hva] using hvC))
      · exact False.elim (hinternal i (Nat.pos_of_ne_zero hi0)
          (Nat.lt_of_le_of_ne (by simpa using hile) hilast) (by simpa [hvi] using hvC))
    · rcases Sym2.eq_iff.mp hqa with hqa | hqa
      · exact False.elim (haC (by simpa [hqa.1] using hvC))
      · exact False.elim (hqC (by simpa [hqa.1] using hvC))
    · rcases Sym2.eq_iff.mp hra with hra | hra
      · exact False.elim (haC (by simpa [hra.1] using hvC))
      · exact False.elim (hrC (by simpa [hra.1] using hvC))
  have hstay : ∀ {v : {v : V | v ≠ x}},
      Relation.ReflTransGen (G.induce {v | v ≠ x}).Adj ⟨h, hhx⟩ v →
        (.inl v.val : V ⊕ Unit) ∉ C.supp := by
    intro v hv
    induction hv with
    | refl => exact hhC
    | tail _ huv ih => exact fun hvC => hnoenter ih hvC huv
  exact hstay hreach htC

/-- In a connected original graph, every corridor-auxiliary component that
avoids the fresh pendant leaf meets the deleted corridor support or one of the
two terminal spoke leaves.  Otherwise its old vertices are closed under every
original edge, contradicting reachability to the pendant attachment. -/
theorem corridorAuxiliary_component_meets_deleted_support
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    (hconn : G.Connected)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    ∃ z : V, (.inl z : V ⊕ Unit) ∈ C.supp ∧
      (z ∈ p.support ∨ z = q ∨ z = r) := by
  by_contra hnone
  obtain ⟨z, hz⟩ := C.nonempty_supp
  obtain ⟨u, hu⟩ : ∃ u : V, (.inl u : V ⊕ Unit) ∈ C.supp := by
    cases z with
    | inl u => exact ⟨u, hz⟩
    | inr unit => cases unit; exact False.elim (hleaf hz)
  have hhC : (.inl h : V ⊕ Unit) ∉ C.supp := by
    intro hh
    apply hleaf
    exact C.mem_supp_of_adj_mem_supp hh
      ((pendantExtension_adj_new (corridorPuncture G p q r) h (.inl h)).mpr rfl).symm
  have hclosed : ∀ u v : V, (.inl u : V ⊕ Unit) ∈ C.supp → G.Adj u v →
      (.inl v : V ⊕ Unit) ∈ C.supp := by
    intro u v hu huv
    by_contra hv
    rcases corridorAuxiliary_component_crossing_is_deleted G p C hu hv huv with hp | hq | hr
    · apply hnone
      exact ⟨u, hu, Or.inl (p.fst_mem_support_of_mem_edges hp)⟩
    · rcases Sym2.eq_iff.mp hq with h | h
      · apply hnone
        exact ⟨u, hu, Or.inl (h.1 ▸ p.end_mem_support)⟩
      · apply hnone
        exact ⟨u, hu, Or.inr (Or.inl h.1)⟩
    · rcases Sym2.eq_iff.mp hr with h | h
      · apply hnone
        exact ⟨u, hu, Or.inl (h.1 ▸ p.end_mem_support)⟩
      · apply hnone
        exact ⟨u, hu, Or.inr (Or.inr h.1)⟩
  have hreach : G.Reachable u h := hconn u h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj u v →
      (.inl u : V ⊕ Unit) ∈ C.supp → (.inl v : V ⊕ Unit) ∈ C.supp := by
    intro v hv hu
    induction hv with
    | refl => exact hu
    | tail _ huv ih => exact hclosed _ _ ih huv
  exact hhC (hpreserve hreach hu)

omit [DecidableRel G.Adj] in
/-- The component containing the fresh pendant leaf is never SET: its induced
degree at that leaf is one, whereas every SET vertex has degree at least two. -/
theorem corridorAuxiliary_pendant_component_not_set
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hleaf : (.inr () : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((corridorAuxiliary G p q r h).induce C.supp) := by
  intro hset
  have hclosed : ∀ z ∈ C.supp,
      (corridorAuxiliary G p q r h).neighborSet z ⊆ C.supp := by
    intro z hz w hzw
    exact C.mem_supp_of_adj_mem_supp hz hzw
  have hdegree : ((corridorAuxiliary G p q r h).induce C.supp).degree
      ⟨.inr (), hleaf⟩ = 1 := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inr ()) hleaf)]
    exact pendantExtension_degree_new (corridorPuncture G p q r) h
  have htwo := hset.two_le_degree ⟨.inr (), hleaf⟩
  omega

/-- A SET component of the corridor auxiliary cannot be the pendant component,
so connectedness forces it to meet the deleted corridor support or one of the
two deleted terminal spokes. -/
theorem corridorAuxiliary_set_component_meets_deleted_support
    {x a q r h : V} (p : G.Walk x a)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hconn : G.Connected)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    ∃ z : V, (.inl z : V ⊕ Unit) ∈ C.supp ∧
      (z ∈ p.support ∨ z = q ∨ z = r) := by
  apply corridorAuxiliary_component_meets_deleted_support G p C hconn
  intro hleaf
  exact corridorAuxiliary_pendant_component_not_set G p C hleaf hset

/-- Away from the terminal and its two extra spoke leaves, the two terminal
deletions do not affect a punctured corridor vertex's neighbour set. -/
theorem neighborFinset_corridorPuncture_of_not_terminal
    {x a q r z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hza : z ≠ a) (hzq : z ≠ q) (hzr : z ≠ r) :
    (corridorPuncture G p q r).neighborFinset z =
      (walkPuncture G p).neighborFinset z := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset]
  rw [corridorPuncture, SimpleGraph.deleteEdges_adj]
  constructor
  · exact fun h => h.1
  · intro hzw
    refine ⟨hzw, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hzwq
      rcases Sym2.eq_iff.mp hzwq with h | h
      · exact hza h.1
      · exact hzq h.1
    · intro hzwr
      rcases Sym2.eq_iff.mp hzwr with h | h
      · exact hza h.1
      · exact hzr h.1

/-- A vertex outside the corridor support and the two deleted terminal spoke
leaves is completely unchanged by the full corridor puncture. -/
theorem neighborFinset_corridorPuncture_of_not_mem_support
    {x a q r z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hz : z ∉ p.support) (hzq : z ≠ q) (hzr : z ≠ r) :
    (corridorPuncture G p q r).neighborFinset z = G.neighborFinset z := by
  have hza : z ≠ a := by
    intro hza
    exact hz (hza ▸ p.end_mem_support)
  rw [neighborFinset_corridorPuncture_of_not_terminal G p hza hzq hzr,
    neighborFinset_walkPuncture_of_not_mem_support G p hz]

/-- In particular, the complete puncture preserves degree parity away from
the corridor and its two terminal spoke leaves. -/
theorem degree_corridorPuncture_of_not_mem_support
    {x a q r z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hz : z ∉ p.support) (hzq : z ≠ q) (hzr : z ≠ r) :
    (corridorPuncture G p q r).degree z = G.degree z := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_corridorPuncture_of_not_mem_support G p hz hzq hzr,
    ← SimpleGraph.card_neighborFinset_eq_degree]

/-- Every puncture-even vertex was originally even.  On the deleted corridor
and at the two terminal leaves this follows from the explicitly retained
original parity data; everywhere else the puncture leaves degree unchanged. -/
theorem corridorPuncture_even_implies_original_even_of_path
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hpathEven : ∀ z, z ∈ p.support → Even (G.degree z))
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support)
    (hqeven : Even (G.degree q)) (hreven : Even (G.degree r)) :
    ∀ z, Even ((corridorPuncture G p q r).degree z) → Even (G.degree z) := by
  intro z hz
  by_cases hzpath : z ∈ p.support
  · exact hpathEven z hzpath
  by_cases hzq : z = q
  · subst z
    exact hqeven
  by_cases hzr : z = r
  · subst z
    exact hreven
  rw [degree_corridorPuncture_of_not_mem_support G p hzpath hzq hzr] at hz
  exact hz

/-- An originally even pendant attachment which is outside the deleted
corridor and terminal leaves remains even in the same-type puncture. -/
theorem even_degree_corridorPuncture_attach_of_not_mem_support
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hh : h ∉ p.support) (hhq : h ≠ q) (hhr : h ≠ r)
    (hheven : Even (G.degree h)) :
    Even ((corridorPuncture G p q r).degree h) := by
  rw [degree_corridorPuncture_of_not_mem_support G p hh hhq hhr]
  exact hheven

/-- The first vertex of a nontrivial corridor is odd after the complete
same-type puncture: exactly its first corridor edge is deleted. -/
theorem odd_degree_corridorPuncture_start
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hxa : x ≠ a) (hxq : x ≠ q) (hxr : x ≠ r)
    (hxeven : Even (G.degree x)) :
    Odd ((corridorPuncture G p q r).degree x) := by
  have hpuncture : (corridorPuncture G p q r).degree x + 1 = G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      neighborFinset_corridorPuncture_of_not_terminal G p hxa hxq hxr,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    exact degree_walkPuncture_start_add_one G p hp hnil
  apply Nat.not_even_iff_odd.mp
  apply Nat.even_add_one.mp
  rw [hpuncture]
  exact hxeven

/-- If a terminal spoke leaf lies outside the corridor, the full puncture
deletes exactly its terminal spoke. -/
theorem neighborFinset_corridorPuncture_terminal_leaf
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hq : q ∉ p.support) (hqr : q ≠ r) :
    (corridorPuncture G p q r).neighborFinset q =
      (G.neighborFinset q).erase a := by
  have hqa : q ≠ a := by
    intro hqa
    subst q
    exact hq p.end_mem_support
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  rw [corridorPuncture_adj_iff]
  constructor
  · rintro ⟨hqw, -, hqwa, -⟩
    exact ⟨fun hwa => hqwa (by simpa [hwa]), hqw⟩
  · rintro ⟨hwa, hqw⟩
    refine ⟨hqw, ?_, ?_, ?_⟩
    · intro he
      exact hq (p.fst_mem_support_of_mem_edges he)
    · intro he
      have he' : s(q, w) = s(a, q) := he
      rcases Sym2.eq_iff.mp he' with h | h
      · exact hqa h.1
      · exact hwa h.2
    · intro he
      have he' : s(q, w) = s(a, r) := he
      rcases Sym2.eq_iff.mp he' with h | h
      · exact hqa h.1
      · exact hqr h.1

/-- Deleting the corridor and both terminal spokes flips the degree parity of
an off-corridor terminal spoke leaf. -/
theorem degree_corridorPuncture_terminal_leaf_add_one
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hq : q ∉ p.support) (hqr : q ≠ r) (haq : G.Adj a q) :
    (corridorPuncture G p q r).degree q + 1 = G.degree q := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_corridorPuncture_terminal_leaf G p hq hqr,
    ← G.card_neighborFinset_eq_degree q]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset q a).mpr haq.symm)

/-- In particular, an originally even off-corridor terminal leaf is odd in
the corridor puncture. -/
theorem odd_degree_corridorPuncture_terminal_leaf
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hq : q ∉ p.support) (hqr : q ≠ r) (haq : G.Adj a q)
    (hqeven : Even (G.degree q)) :
    Odd ((corridorPuncture G p q r).degree q) := by
  apply Nat.not_even_iff_odd.mp
  apply Nat.even_add_one.mp
  rw [degree_corridorPuncture_terminal_leaf_add_one G p hq hqr haq]
  exact hqeven

/-- The same terminal leaf stays odd after the pendant extension, provided it
is not the pendant attachment. -/
theorem odd_degree_corridorAuxiliary_terminal_leaf
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hq : q ∉ p.support) (hqr : q ≠ r) (hqh : q ≠ h) (haq : G.Adj a q)
    (hqeven : Even (G.degree q)) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl q)) := by
  rw [pendantExtension_odd_old_ne (corridorPuncture G p q r) h q hqh]
  exact odd_degree_corridorPuncture_terminal_leaf G p hq hqr haq hqeven

/-- The second terminal spoke leaf also loses exactly its terminal spoke when
it lies outside the corridor. -/
theorem neighborFinset_corridorPuncture_terminal_leaf_right
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hr : r ∉ p.support) (hrq : r ≠ q) :
    (corridorPuncture G p q r).neighborFinset r =
      (G.neighborFinset r).erase a := by
  have hra : r ≠ a := by
    intro hra
    subst r
    exact hr p.end_mem_support
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
  rw [corridorPuncture_adj_iff]
  constructor
  · rintro ⟨hrw, -, -, hrwa⟩
    exact ⟨fun hwa => hrwa (by simpa [hwa]), hrw⟩
  · rintro ⟨hwa, hrw⟩
    refine ⟨hrw, ?_, ?_, ?_⟩
    · intro he
      exact hr (p.fst_mem_support_of_mem_edges he)
    · intro he
      have he' : s(r, w) = s(a, q) := he
      rcases Sym2.eq_iff.mp he' with h | h
      · exact hra h.1
      · exact hrq h.1
    · intro he
      have he' : s(r, w) = s(a, r) := he
      rcases Sym2.eq_iff.mp he' with h | h
      · exact hra h.1
      · exact hwa h.2

/-- The complete puncture flips the degree parity at the second terminal
spoke leaf. -/
theorem degree_corridorPuncture_terminal_leaf_right_add_one
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hr : r ∉ p.support) (hrq : r ≠ q) (har : G.Adj a r) :
    (corridorPuncture G p q r).degree r + 1 = G.degree r := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_corridorPuncture_terminal_leaf_right G p hr hrq,
    ← G.card_neighborFinset_eq_degree r]
  exact Finset.card_erase_add_one ((G.mem_neighborFinset r a).mpr har.symm)

/-- The symmetric terminal leaf becomes and remains odd in the full corridor
auxiliary. -/
theorem odd_degree_corridorAuxiliary_terminal_leaf_right
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hr : r ∉ p.support) (hrq : r ≠ q) (hrh : r ≠ h) (har : G.Adj a r)
    (hreven : Even (G.degree r)) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl r)) := by
  rw [pendantExtension_odd_old_ne (corridorPuncture G p q r) h r hrh]
  apply Nat.not_even_iff_odd.mp
  apply Nat.even_add_one.mp
  rw [degree_corridorPuncture_terminal_leaf_right_add_one G p hr hrq har]
  exact hreven

/-- An originally even attachment vertex outside the deleted support becomes
odd in the full corridor auxiliary. -/
theorem odd_degree_corridorAuxiliary_attach_of_not_mem_support
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hh : h ∉ p.support) (hhq : h ≠ q) (hhr : h ≠ r)
    (hheven : Even (G.degree h)) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl h)) := by
  rw [pendantExtension_odd_attach_iff,
    degree_corridorPuncture_of_not_mem_support G p hh hhq hhr]
  exact hheven

/-- The initial endpoint of a nontrivial corridor is auxiliary-odd when it
is originally even and is not one of the pendant or terminal-spoke vertices.
The corridor removes its unique first edge there; the two terminal-spoke
deletions are disjoint from that endpoint. -/
theorem odd_degree_corridorAuxiliary_start
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hxa : x ≠ a) (hxq : x ≠ q) (hxr : x ≠ r) (hxh : x ≠ h)
    (hxeven : Even (G.degree x)) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl x)) := by
  have hpuncture : (corridorPuncture G p q r).degree x + 1 = G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      neighborFinset_corridorPuncture_of_not_terminal G p hxa hxq hxr,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    exact degree_walkPuncture_start_add_one G p hp hnil
  rw [pendantExtension_odd_old_ne (corridorPuncture G p q r) h x hxh]
  apply Nat.not_even_iff_odd.mp
  apply Nat.even_add_one.mp
  rw [hpuncture]
  exact hxeven

/-- The literal terminal data for a corridor produces exactly the three
auxiliary-odd old vertices needed by the internal isolation argument. -/
theorem corridorAuxiliary_terminal_odd_profile
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hq : q ∉ p.support) (hr : r ∉ p.support) (hh : h ∉ p.support)
    (hqr : q ≠ r) (hqh : q ≠ h) (hrh : r ≠ h)
    (haq : G.Adj a q) (har : G.Adj a r)
    (hqeven : Even (G.degree q)) (hreven : Even (G.degree r))
    (hheven : Even (G.degree h)) :
    Odd ((corridorAuxiliary G p q r h).degree (.inl q)) ∧
      Odd ((corridorAuxiliary G p q r h).degree (.inl r)) ∧
      Odd ((corridorAuxiliary G p q r h).degree (.inl h)) := by
  refine ⟨odd_degree_corridorAuxiliary_terminal_leaf G p hq hqr hqh haq hqeven,
    odd_degree_corridorAuxiliary_terminal_leaf_right G p hr hqr.symm hrh har hreven,
    odd_degree_corridorAuxiliary_attach_of_not_mem_support G p hh hqh.symm hrh.symm hheven⟩

/-- The pendant auxiliary also preserves parity at old vertices outside the
corridor, terminal spoke leaves, and pendant attachment. -/
theorem even_degree_corridorAuxiliary_iff_of_not_mem_support
    {x a q r h z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hz : z ∉ p.support) (hzq : z ≠ q) (hzr : z ≠ r) (hzh : z ≠ h) :
    Even ((corridorAuxiliary G p q r h).degree (.inl z)) ↔ Even (G.degree z) := by
  rw [pendantExtension_even_old_ne (corridorPuncture G p q r) h z hzh,
    degree_corridorPuncture_of_not_mem_support G p hz hzq hzr]

/-- An auxiliary-even neighbour of an old vertex away from the pendant
attachment is originally even once every corridor vertex is originally even
and the three possible parity-flipped old vertices are auxiliary-odd. -/
theorem corridorAuxiliary_even_neighbor_original_even_of_profile
    {x a q r h z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hpathEven : ∀ w, w ∈ p.support → Even (G.degree w))
    (hqodd : Odd ((corridorAuxiliary G p q r h).degree (.inl q)))
    (hrodd : Odd ((corridorAuxiliary G p q r h).degree (.inl r)))
    (hhodd : Odd ((corridorAuxiliary G p q r h).degree (.inl h)))
    (hzh : z ≠ h) (w : V ⊕ Unit)
    (hzw : (corridorAuxiliary G p q r h).Adj (.inl z) w)
    (hweven : Even ((corridorAuxiliary G p q r h).degree w)) :
    ∃ v : V, w = .inl v ∧ Even (G.degree v) := by
  cases w with
  | inr u =>
    cases u
    have hzeq : (.inl z : V ⊕ Unit) = .inl h :=
      (pendantExtension_adj_new (corridorPuncture G p q r) h (.inl z)).mp hzw.symm
    exact False.elim (hzh (Sum.inl.inj hzeq))
  | inl w =>
    refine ⟨w, rfl, ?_⟩
    by_cases hwpath : w ∈ p.support
    · exact hpathEven w hwpath
    by_cases hwq : w = q
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr hqodd) hweven)
    by_cases hwr : w = r
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr hrodd) hweven)
    by_cases hwh : w = h
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr hhodd) hweven)
    exact (even_degree_corridorAuxiliary_iff_of_not_mem_support G p hwpath hwq hwr hwh).mp
      hweven

/-- Component-local even-neighbour transport for the corridor auxiliary.
An even neighbour in an induced auxiliary component has the same parity in
the ambient auxiliary by component closure, so the global corridor parity
profile transports it to an original even neighbour. -/
theorem corridorAuxiliary_component_evenNeighbor_old_original_of_profile
    {x a q r h z : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hzC : (.inl z : V ⊕ Unit) ∈ C.supp) (w : C.supp)
    (hpathEven : ∀ v, v ∈ p.support → Even (G.degree v))
    (hqodd : Odd ((corridorAuxiliary G p q r h).degree (.inl q)))
    (hrodd : Odd ((corridorAuxiliary G p q r h).degree (.inl r)))
    (hhodd : Odd ((corridorAuxiliary G p q r h).degree (.inl h)))
    (hzh : z ≠ h)
    (hzw : w ∈ evenNeighbors ((corridorAuxiliary G p q r h).induce C.supp)
      ⟨.inl z, hzC⟩) :
    ∃ v : V, w.val = .inl v ∧ v ∈ evenNeighbors G z := by
  obtain ⟨hzwInd, hwEvenInd⟩ :=
    (mem_evenNeighbors (G := (corridorAuxiliary G p q r h).induce C.supp)
      ⟨.inl z, hzC⟩ w).mp hzw
  have hclosed : ∀ u ∈ C.supp,
      (corridorAuxiliary G p q r h).neighborSet u ⊆ C.supp := by
    intro u hu v huv
    exact C.mem_supp_of_adj_mem_supp hu huv
  have hwEvenAux : Even ((corridorAuxiliary G p q r h).degree w.val) := by
    rw [← SimpleGraph.degree_induce_of_neighborSet_subset (hclosed w.val w.property)]
    exact hwEvenInd
  have hzwAux : (corridorAuxiliary G p q r h).Adj (.inl z) w.val := hzwInd
  obtain ⟨v, hwval, hvEven⟩ :=
    corridorAuxiliary_even_neighbor_original_even_of_profile G p hpathEven hqodd hrodd hhodd
      hzh w.val hzwAux hwEvenAux
  refine ⟨v, hwval, ?_⟩
  apply (mem_evenNeighbors (G := G) z v).mpr
  refine ⟨?_, hvEven⟩
  have hdata := (corridorAuxiliary_adj_old_iff G p).mp (hwval ▸ hzwAux)
  exact hdata.1

/-- A SET component cannot contain a pair of affected old vertices when their
common SET witness would have four distinct original even neighbours.  The
statement retains the original-evenness of the pair explicitly: it is the
exact input needed for the reverse neighbour incidences in the subcubic
capacity contradiction. -/
theorem corridorAuxiliary_set_component_not_contains_odd_pair_of_cap
    {x a q r h u v : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hpathEven : ∀ z, z ∈ p.support → Even (G.degree z))
    (hqodd : Odd ((corridorAuxiliary G p q r h).degree (.inl q)))
    (hrodd : Odd ((corridorAuxiliary G p q r h).degree (.inl r)))
    (hhodd : Odd ((corridorAuxiliary G p q r h).degree (.inl h)))
    (hxodd : Odd ((corridorAuxiliary G p q r h).degree (.inl x)))
    (huodd : Odd ((corridorAuxiliary G p q r h).degree (.inl u)))
    (hvodd : Odd ((corridorAuxiliary G p q r h).degree (.inl v)))
    (huEven : Even (G.degree u)) (hvEven : Even (G.degree v))
    (huh : u ≠ h) (hvh : v ≠ h) (huv : u ≠ v)
    (hcap : ∀ z, Even (G.degree z) → z ≠ h → z ≠ x → eDegree G z ≤ 3)
    (huC : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hvC : (.inl v : V ⊕ Unit) ∈ C.supp)
    (hset : IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    False := by
  let A := corridorAuxiliary G p q r h
  let K := A.induce C.supp
  have hclosed : ∀ z ∈ C.supp, A.neighborSet z ⊆ C.supp := by
    intro z hz w hzw
    exact C.mem_supp_of_adj_mem_supp hz hzw
  have hoddK : ∀ (z : V) (hz : (.inl z : V ⊕ Unit) ∈ C.supp),
      Odd (A.degree (.inl z)) → Odd (K.degree ⟨.inl z, hz⟩) := by
    intro z hz hodd
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inl z) hz)]
    exact hodd
  have huK : Odd (K.degree ⟨.inl u, huC⟩) := hoddK u huC huodd
  have hvK : Odd (K.degree ⟨.inl v, hvC⟩) := hoddK v hvC hvodd
  obtain ⟨wC, huw, hvw, hwEvenK⟩ :=
    hset.exists_common_even_neighbor_of_odd ⟨.inl u, huC⟩ ⟨.inl v, hvC⟩ huK hvK
  have huwMem : wC ∈ evenNeighbors K ⟨.inl u, huC⟩ :=
    (mem_evenNeighbors (G := K) ⟨.inl u, huC⟩ wC).mpr ⟨huw, hwEvenK⟩
  obtain ⟨w, hwval, hwGu⟩ :=
    corridorAuxiliary_component_evenNeighbor_old_original_of_profile G p C huC wC
      hpathEven hqodd hrodd hhodd huh huwMem
  have hwC : (.inl w : V ⊕ Unit) ∈ C.supp := by
    simpa [hwval] using wC.property
  have hwCeq : wC = ⟨.inl w, hwC⟩ := Subtype.ext hwval
  subst wC
  have hwh : w ≠ h := by
    intro e
    have hhC : (.inl h : V ⊕ Unit) ∈ C.supp := by simpa [e] using hwC
    have hhK : Odd (K.degree ⟨.inl h, hhC⟩) := hoddK h hhC hhodd
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl h, hhC⟩ :=
      Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr hhK) hwEvenK
  have hwx : w ≠ x := by
    by_cases hxC : (.inl x : V ⊕ Unit) ∈ C.supp
    · intro e
      have hxK : Odd (K.degree ⟨.inl x, hxC⟩) := hoddK x hxC hxodd
      have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl x, hxC⟩ :=
        Subtype.ext (by simpa [e])
      rw [he] at hwEvenK
      exact (Nat.not_even_iff_odd.mpr hxK) hwEvenK
    · intro e
      apply hxC
      simpa [e] using hwC
  have hwEvenG : Even (G.degree w) :=
    (mem_evenNeighbors (G := G) u w).mp hwGu |>.2
  have hvwMem : ⟨.inl w, hwC⟩ ∈ evenNeighbors K ⟨.inl v, hvC⟩ :=
    (mem_evenNeighbors (G := K) ⟨.inl v, hvC⟩ ⟨.inl w, hwC⟩).mpr
      ⟨hvw, hwEvenK⟩
  obtain ⟨w', hw'val, hwGv⟩ :=
    corridorAuxiliary_component_evenNeighbor_old_original_of_profile G p C hvC
      ⟨.inl w, hwC⟩ hpathEven hqodd hrodd hhodd hvh hvwMem
  have hww' : w' = w := by simpa using hw'val.symm
  have huGw : u ∈ evenNeighbors G w := by
    obtain ⟨huwG, _⟩ := (mem_evenNeighbors (G := G) u w).mp hwGu
    exact (mem_evenNeighbors (G := G) w u).mpr ⟨huwG.symm, huEven⟩
  have hvGw : v ∈ evenNeighbors G w := by
    obtain ⟨hvwG, _⟩ := (mem_evenNeighbors (G := G) v w).mp (by
      simpa [hww'] using hwGv)
    exact (mem_evenNeighbors (G := G) w v).mpr ⟨hvwG.symm, hvEven⟩
  have hdegW : eDegree K ⟨.inl w, hwC⟩ = 2 :=
    hset.eDegree_even ⟨.inl w, hwC⟩ hwEvenK
  change (evenNeighbors K ⟨.inl w, hwC⟩).card = 2 at hdegW
  obtain ⟨z₁, z₂, hz₁₂, hN⟩ := Finset.card_eq_two.mp hdegW
  have hz₁ : z₁ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  have hz₂ : z₂ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  obtain ⟨u₁, hz₁val, hu₁G⟩ :=
    corridorAuxiliary_component_evenNeighbor_old_original_of_profile G p C hwC z₁
      hpathEven hqodd hrodd hhodd hwh hz₁
  obtain ⟨u₂, hz₂val, hu₂G⟩ :=
    corridorAuxiliary_component_evenNeighbor_old_original_of_profile G p C hwC z₂
      hpathEven hqodd hrodd hhodd hwh hz₂
  have hz₁Even : Even (K.degree z₁) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₁).mp hz₁ |>.2
  have hz₂Even : Even (K.degree z₂) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₂).mp hz₂ |>.2
  have hu₁u₂ : u₁ ≠ u₂ := by
    intro e
    apply hz₁₂
    apply Subtype.ext
    calc
      z₁.val = .inl u₁ := hz₁val
      _ = .inl u₂ := by rw [e]
      _ = z₂.val := hz₂val.symm
  have hu₁u : u₁ ≠ u := by
    intro e
    have hz : z₁ = ⟨.inl u, huC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr huK) hz₁Even
  have hu₁v : u₁ ≠ v := by
    intro e
    have hz : z₁ = ⟨.inl v, hvC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr hvK) hz₁Even
  have hu₂u : u₂ ≠ u := by
    intro e
    have hz : z₂ = ⟨.inl u, huC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr huK) hz₂Even
  have hu₂v : u₂ ≠ v := by
    intro e
    have hz : z₂ = ⟨.inl v, hvC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr hvK) hz₂Even
  have hfour := eDegree_ge_four_of_four_distinct_evenNeighbors (G := G) w u₁ u₂ u v
    hu₁G hu₂G huGw hvGw hu₁u₂ hu₁u hu₁v hu₂u hu₂v huv
  have hupper := hcap w hwEvenG hwh hwx
  omega

/-- If the terminal even vertex has exactly the predecessor and the two
deleted terminal leaves as its original even neighbours, then it is isolated
in the auxiliary even graph. -/
theorem corridorAuxiliary_terminal_eDegree_eq_zero_of_profile
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (hnil : ¬ p.Nil)
    (hpathEven : ∀ z, z ∈ p.support → Even (G.degree z))
    (hqoff : q ∉ p.support) (hroff : r ∉ p.support)
    (hqr : q ≠ r) (hzh : a ≠ h)
    (haq : G.Adj a q) (har : G.Adj a r)
    (hqEven : Even (G.degree q)) (hrEven : Even (G.degree r))
    (hqodd : Odd ((corridorAuxiliary G p q r h).degree (.inl q)))
    (hrodd : Odd ((corridorAuxiliary G p q r h).degree (.inl r)))
    (hhodd : Odd ((corridorAuxiliary G p q r h).degree (.inl h)))
    (hadeg : eDegree G a = 3) :
    eDegree (corridorAuxiliary G p q r h) (.inl a) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨haz, hzEven⟩ :=
    (mem_evenNeighbors (G := corridorAuxiliary G p q r h) (.inl a) z).mp hz
  obtain ⟨v, hzval, hvEven⟩ :=
    corridorAuxiliary_even_neighbor_original_even_of_profile G p hpathEven hqodd hrodd hhodd
      hzh z haz hzEven
  have hav : G.Adj a v :=
    (corridorAuxiliary_adj_old_iff G p).mp (hzval ▸ haz) |>.1
  have hvMem : v ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a v).mpr ⟨hav, hvEven⟩
  have hpredMem : p.penultimate ∈ p.support :=
    (SimpleGraph.Walk.mem_support_iff_exists_getVert).mpr
      ⟨p.length - 1, rfl, Nat.sub_le _ _⟩
  have hpredEven : Even (G.degree p.penultimate) := hpathEven p.penultimate hpredMem
  have hpredAdj : G.Adj a p.penultimate :=
    (p.adj_of_mem_edges (p.mk_penultimate_end_mem_edges hnil)).symm
  have hpredN : p.penultimate ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a p.penultimate).mpr ⟨hpredAdj, hpredEven⟩
  have hqN : q ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a q).mpr ⟨haq, hqEven⟩
  have hrN : r ∈ evenNeighbors G a :=
    (mem_evenNeighbors (G := G) a r).mpr ⟨har, hrEven⟩
  have hpq : p.penultimate ≠ q := by
    intro e
    apply hqoff
    rw [← e]
    exact hpredMem
  have hpr : p.penultimate ≠ r := by
    intro e
    apply hroff
    rw [← e]
    exact hpredMem
  have hpair : ({p.penultimate, q, r} : Finset V) ⊆ evenNeighbors G a := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwp | hwq | hwr
    · simpa [hwp] using hpredN
    · simpa [hwq] using hqN
    · simpa [hwr] using hrN
  change (evenNeighbors G a).card = 3 at hadeg
  have hneighborhood : ({p.penultimate, q, r} : Finset V) = evenNeighbors G a := by
    apply Finset.eq_of_subset_of_card_le hpair
    rw [hadeg]
    simp [hpq, hpr, hqr]
  rw [← hneighborhood] at hvMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
  rcases hvMem with hv | hv | hv
  · subst v
    have hnot := (corridorAuxiliary_adj_old_iff G p).mp (hzval ▸ haz) |>.2.1
    exact hnot (by simpa only [Sym2.eq_swap] using p.mk_penultimate_end_mem_edges hnil)
  · subst v
    exact ((corridorAuxiliary_adj_old_iff G p).mp (hzval ▸ haz) |>.2.2.1) rfl
  · subst v
    exact ((corridorAuxiliary_adj_old_iff G p).mp (hzval ▸ haz) |>.2.2.2) rfl

/-- Under the literal shortest-corridor parity profile, every internal vertex
whose original E-degree is two is isolated in the auxiliary even graph.  The
proof uses the two predecessor/successor even neighbours to exhaust the
original E-neighbourhood, while both corresponding path edges are deleted. -/
theorem corridorAuxiliary_internal_eDegree_eq_zero_of_profile
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (hpathEven : ∀ w, w ∈ p.support → Even (G.degree w))
    (hqodd : Odd ((corridorAuxiliary G p q r h).degree (.inl q)))
    (hrodd : Odd ((corridorAuxiliary G p q r h).degree (.inl r)))
    (hhodd : Odd ((corridorAuxiliary G p q r h).degree (.inl h)))
    (hzh : p.getVert i ≠ h)
    (hdegree : eDegree G (p.getVert i) = 2) :
    eDegree (corridorAuxiliary G p q r h) (.inl (p.getVert i)) = 0 := by
  let u := p.getVert (i - 1)
  let v := p.getVert (i + 1)
  have huv : u ≠ v := by
    intro huv
    have hidx : i - 1 = i + 1 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) (by simpa [u, v] using huv)
    omega
  have huEven : Even (G.degree u) := by
    apply hpathEven u
    simp [u]
  have hvEven : Even (G.degree v) := by
    apply hpathEven v
    simp [v]
  have huAdj : G.Adj (p.getVert i) u := by
    have huAdj' : G.Adj u (p.getVert i) := by
      dsimp [u]
      rw [← Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)]
      exact p.adj_getVert_succ (i := i - 1) (by omega)
    exact huAdj'.symm
  have hvAdj : G.Adj (p.getVert i) v := by
    dsimp [v]
    exact p.adj_getVert_succ (i := i) hiend
  have huMem : u ∈ evenNeighbors G (p.getVert i) :=
    (mem_evenNeighbors (G := G) _ _).mpr ⟨huAdj, huEven⟩
  have hvMem : v ∈ evenNeighbors G (p.getVert i) :=
    (mem_evenNeighbors (G := G) _ _).mpr ⟨hvAdj, hvEven⟩
  have hpairSub : ({u, v} : Finset V) ⊆ evenNeighbors G (p.getVert i) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact huMem
    · exact hvMem
  have hpairCard : ({u, v} : Finset V).card = 2 := by simp [huv]
  change (evenNeighbors G (p.getVert i)).card = 2 at hdegree
  have hneighborhood : ({u, v} : Finset V) = evenNeighbors G (p.getVert i) := by
    apply Finset.eq_of_subset_of_card_le hpairSub
    rw [hdegree, hpairCard]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  obtain ⟨hzw, hwEven⟩ := (mem_evenNeighbors (G := corridorAuxiliary G p q r h)
    (.inl (p.getVert i)) w).mp hw
  obtain ⟨old, hwo, hOldEven⟩ :=
    corridorAuxiliary_even_neighbor_original_even_of_profile G p hpathEven hqodd hrodd hhodd
      hzh w hzw hwEven
  subst w
  have hOldAdjData := (corridorAuxiliary_adj_old_iff G p).mp hzw
  have hOldMem : old ∈ evenNeighbors G (p.getVert i) :=
    (mem_evenNeighbors (G := G) _ _).mpr ⟨hOldAdjData.1, hOldEven⟩
  rw [← hneighborhood] at hOldMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hOldMem
  rcases hOldMem with hold | hold
  · subst old
    exact hOldAdjData.2.1 (by
      rw [Sym2.eq_swap]
      apply p.mk_mem_edges_iff_exists.mpr
      refine ⟨i - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)])
  · subst old
    exact hOldAdjData.2.1 (p.mk_mem_edges_iff_exists.mpr ⟨i, hiend, rfl⟩)

/-- The literal terminal data therefore isolates every internal original
E-degree-two corridor vertex in the auxiliary even graph.  This is the
profile-free form consumed by the shortest-corridor reduction. -/
theorem corridorAuxiliary_internal_eDegree_eq_zero_of_terminal_data
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (hpathEven : ∀ w, w ∈ p.support → Even (G.degree w))
    (hq : q ∉ p.support) (hr : r ∉ p.support) (hh : h ∉ p.support)
    (hqr : q ≠ r) (hqh : q ≠ h) (hrh : r ≠ h)
    (haq : G.Adj a q) (har : G.Adj a r)
    (hqeven : Even (G.degree q)) (hreven : Even (G.degree r))
    (hheven : Even (G.degree h)) (hzh : p.getVert i ≠ h)
    (hdegree : eDegree G (p.getVert i) = 2) :
    eDegree (corridorAuxiliary G p q r h) (.inl (p.getVert i)) = 0 := by
  obtain ⟨hqodd, hrodd, hhodd⟩ := corridorAuxiliary_terminal_odd_profile G p
    hq hr hh hqr hqh hrh haq har hqeven hreven hheven
  exact corridorAuxiliary_internal_eDegree_eq_zero_of_profile G p hp i hi hiend hpathEven
    hqodd hrodd hhodd hzh hdegree

/-- A component of the corridor auxiliary containing an internal corridor
vertex with even degree and zero E-degree cannot be SET.  This is the
component-local endpoint of the internal-isolation calculation; the
shortest-corridor reduction supplies its two numerical hypotheses. -/
theorem corridorAuxiliary_internal_component_not_set_of_even_eDegree_zero
    {x a q r h : V} (p : G.Walk x a) (i : ℕ)
    (C : (corridorAuxiliary G p q r h).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hiC : (.inl (p.getVert i) : V ⊕ Unit) ∈ C.supp)
    (heven : Even ((corridorAuxiliary G p q r h).degree (.inl (p.getVert i))) )
    (hzero : eDegree (corridorAuxiliary G p q r h) (.inl (p.getVert i)) = 0) :
    ¬ IsSET ((corridorAuxiliary G p q r h).induce C.supp) := by
  exact component_not_set_of_even_eDegree_zero
    (G := corridorAuxiliary G p q r h) C (.inl (p.getVert i)) hiC heven hzero

/-- The complete corridor puncture has the same two-unit internal degree
loss as the underlying path puncture whenever its terminal spoke deletions
are disjoint from that internal vertex. -/
theorem degree_corridorPuncture_internal_add_two
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (hza : p.getVert i ≠ a) (hzq : p.getVert i ≠ q)
    (hzr : p.getVert i ≠ r) :
    (corridorPuncture G p q r).degree (p.getVert i) + 2 =
      G.degree (p.getVert i) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_corridorPuncture_of_not_terminal G p hza hzq hzr,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  exact degree_walkPuncture_internal_add_two G p hp i hi hiend

/-- An internally even corridor vertex remains even after the complete
corridor puncture, provided the terminal spoke deletions avoid it. -/
theorem even_degree_corridorPuncture_internal
    {x a q r : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (hza : p.getVert i ≠ a) (hzq : p.getVert i ≠ q)
    (hzr : p.getVert i ≠ r) (heven : Even (G.degree (p.getVert i))) :
    Even ((corridorPuncture G p q r).degree (p.getVert i)) := by
  have hsum : Even ((corridorPuncture G p q r).degree (p.getVert i) + 2) := by
    rw [degree_corridorPuncture_internal_add_two G p hp i hi hiend hza hzq hzr]
    exact heven
  exact (Nat.even_add.mp hsum).mpr (by simp)

/-- The pendant extension preserves the evenness of an internal corridor
vertex which is distinct from the attachment vertex. -/
theorem even_degree_corridorAuxiliary_internal
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hp : p.IsPath) (i : ℕ) (hi : 0 < i) (hiend : i < p.length)
    (hza : p.getVert i ≠ a) (hzq : p.getVert i ≠ q)
    (hzr : p.getVert i ≠ r) (hzh : p.getVert i ≠ h)
    (heven : Even (G.degree (p.getVert i))) :
    Even ((corridorAuxiliary G p q r h).degree (.inl (p.getVert i))) := by
  rw [pendantExtension_even_old_ne (corridorPuncture G p q r) h (p.getVert i) hzh]
  exact even_degree_corridorPuncture_internal G p hp i hi hiend hza hzq hzr heven

omit [DecidableRel G.Adj] in
/-- A corridor auxiliary has the published floor budget once its local
subcubic even-degree cap is established and every actual component is
excluded from the SET alternative.  The theorem deliberately keeps those two
graph-specific inputs explicit. -/
theorem corridorAuxiliary_floor_of_component_nonSET
    {x a q r h : V} (p : G.Walk x a)
    (hcap : ∀ v, Even ((corridorAuxiliary G p q r h).degree v) →
      eDegree (corridorAuxiliary G p q r h) v ≤ 3)
    (hnot : ∀ (C : (corridorAuxiliary G p q r h).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((corridorAuxiliary G p q r h).induce C.supp)) :
    HasPathBudget (corridorAuxiliary G p q r h)
      (Fintype.card (V ⊕ Unit) / 2) := by
  apply floor_of_components
  intro C
  classical
  apply (floor_or_set ((corridorAuxiliary G p q r h).induce C.supp)
    C.connected_toSimpleGraph ?_).resolve_right
  · exact hnot C
  · have hclosed : ∀ v ∈ C.supp,
        (corridorAuxiliary G p q r h).neighborSet v ⊆ C.supp := by
      intro v hv w hw
      exact C.mem_supp_of_adj_mem_supp hv hw
    exact even_degree_cap_induce_of_closed
      (corridorAuxiliary G p q r h) C.supp hclosed 3 hcap

/-- Cap transfer for a corridor auxiliary.  The only two original vertices
that are exempt from the bare cap are handled separately: `h` has original
E-degree zero, while `x` is odd in the puncture.  Establishing the puncture's
parity preservation and these two local facts is deliberately left to the
literal corridor reduction. -/
theorem corridorAuxiliary_cap_of_puncture_even_preservation
    {x a q r h : V} (p : G.Walk x a)
    [DecidableRel (walkPuncture G p).Adj]
    [DecidableRel (corridorPuncture G p q r).Adj]
    (hpunctureEven : ∀ v, Even ((corridorPuncture G p q r).degree v) →
      Even (G.degree v))
    (hhP : Even ((corridorPuncture G p q r).degree h))
    (hxoddP : Odd ((corridorPuncture G p q r).degree x))
    (hbare : eDegree G h = 0)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((corridorAuxiliary G p q r h).degree v) →
      eDegree (corridorAuxiliary G p q r h) v ≤ 3 := by
  have hpunctureCap : ∀ v, Even ((corridorPuncture G p q r).degree v) →
      eDegree (corridorPuncture G p q r) v ≤ 3 := by
    intro v hv
    have hle : eDegree (corridorPuncture G p q r) v ≤ eDegree G v :=
      eDegree_le_of_subgraph_of_even_preservation
        (G := G) (J := corridorPuncture G p q r)
        (corridorPuncture_le G p q r) hpunctureEven v
    by_cases hvh : v = h
    · subst v
      rw [hbare] at hle
      omega
    by_cases hvx : v = x
    · subst v
      exact False.elim ((Nat.not_even_iff_odd.mpr hxoddP) hv)
    exact hle.trans (hcap v (hpunctureEven v hv) hvh hvx)
  exact pendantExtension_cap (corridorPuncture G p q r) h hhP hpunctureCap

end Gallai
