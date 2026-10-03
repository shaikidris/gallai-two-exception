/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Gallai.Structure.PunctureBoundary
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

@[expose] public section

/-! # Contact sets for consecutive two-vertex cycle arcs -/

namespace Gallai.TwoException

variable {V : Type*}

/-- A nonempty contact set on the arc {a,b} that respects the next arc
partition {b,c} is a singleton, provided a,b,c are distinct. This includes
the contact-set step for a four-cycle. -/
theorem consecutive_arc_contact_singleton
    (S : Set V) (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hne : S.Nonempty) (hS : S ⊆ {a, b})
    (hnext : S ⊆ {b, c} ∨ Disjoint S {b, c}) :
    S = {a} ∨ S = {b} := by
  classical
  rcases hnext with hin | hout
  · right
    apply Set.Subset.antisymm
    · intro v hv
      have hvab := hS hv
      have hvbc := hin hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvab hvbc ⊢
      rcases hvab with rfl | hvb
      · exact (hvbc.elim hab hac).elim
      · exact hvb
    · obtain ⟨v, hv⟩ := hne
      have hvab := hS hv
      have hvbc := hin hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvab hvbc
      have hvb : v = b := hvab.elim (fun hva => by
        subst v
        exact (hvbc.elim hab hac).elim) id
      intro w hw
      have hwb : w = b := hw
      simpa only [hvb, hwb] using hv
  · left
    have hall : ∀ v ∈ S, v = a := by
      intro v hv
      rcases hS hv with hva | hvb
      · exact hva
      · exact (Set.disjoint_left.mp hout hv
          (Set.mem_insert_iff.mpr (Or.inl (show v = b from hvb)))).elim
    apply Set.Subset.antisymm
    · intro v hv
      exact hall v hv
    · obtain ⟨v, hv⟩ := hne
      have hva := hall v hv
      intro w hw
      have hwa : w = a := hw
      simpa only [hva, hwa] using hv

/-- If every edge leaving S has its S-end at a, deleting a prevents
reachability from S to its complement. -/
theorem singleton_boundary_not_reachable_avoiding
    {G : SimpleGraph V} (S : Set V) (a h z : V)
    (hh : h ∈ S) (hz : z ∉ S) (hha : h ≠ a) (hza : z ≠ a)
    (hboundary : ∀ u v, u ∈ S → v ∉ S → G.Adj u v → u = a) :
    ¬ (G.induce {v | v ≠ a}).Reachable ⟨h, hha⟩ ⟨z, hza⟩ := by
  rintro ⟨p⟩
  have step : ∀ {u v : {v : V | v ≠ a}},
      (G.induce {v | v ≠ a}).Walk u v → u.val ∈ S → v.val ∈ S := by
    intro u v q
    induction q with
    | nil => exact id
    | @cons u v w huv q ih =>
      intro hu
      have hv : v.val ∈ S := by
        by_contra hv
        exact u.property (hboundary u.val v.val hu hv huv)
      exact ih hv
  exact hz (step p hh)

/-- A component of a spanning puncture with only one contact among the
removed-edge endpoints has a singleton original boundary. This transports
the contact-set statement to the vertex-deletion reachability obstruction. -/
theorem puncture_singleton_contact_not_reachable
    {G J : SimpleGraph V} (C : J.ConnectedComponent) (A : Set V)
    (a h z : V) (hh : h ∈ C.supp) (hz : z ∉ C.supp)
    (hha : h ≠ a) (hza : z ≠ a)
    (hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A)
    (hcontact : ∀ u, u ∈ C.supp → u ∈ A → u = a) :
    ¬ (G.induce {v | v ≠ a}).Reachable ⟨h, hha⟩ ⟨z, hza⟩ := by
  apply singleton_boundary_not_reachable_avoiding C.supp a h z hh hz hha hza
  intro u v hu hv huv
  have hn : ¬ J.Adj u v := fun hJ => hv (C.mem_supp_of_adj_mem_supp hu hJ)
  exact hcontact u hu (hremoved u v huv hn)

/-- Every component of a proper spanning puncture of a connected graph
has a nonempty contact set on the removed-edge endpoint set. -/
theorem puncture_component_contacts_nonempty
    {G J : SimpleGraph V} (hconn : G.Connected) (hlt : J < G)
    (A : Set V) (hremoved : ∀ u v, G.Adj u v → ¬ J.Adj u v → u ∈ A)
    (C : J.ConnectedComponent) : (C.supp ∩ A).Nonempty := by
  obtain ⟨v, hv, w, hvw, hn⟩ := puncture_closed_boundary_nonempty
    hconn hlt C.supp C.nonempty_supp
    (fun u hu v huv => C.mem_supp_of_adj_mem_supp hu huv)
  exact ⟨v, hv, hremoved v w hvw hn⟩

/-- If both arcs of A are connected in K but h and z are not reachable,
every component of the finer puncture J has all its contacts on one arc.
This derives the partition condition from graph reachability. -/
theorem puncture_contacts_respect_two_arcs
    {J K : SimpleGraph V} (hle : J ≤ K) (A U : Set V) (h z : V)
    (hnot : ¬ K.Reachable h z)
    (hh : ((J.connectedComponentMk h).supp ∩ A).Nonempty)
    (hz : ((J.connectedComponentMk z).supp ∩ A).Nonempty)
    (harc : ∀ u ∈ A, ∀ v ∈ A, u ∈ U → v ∈ U → K.Reachable u v)
    (hother : ∀ u ∈ A, ∀ v ∈ A, u ∉ U → v ∉ U → K.Reachable u v)
    (C : J.ConnectedComponent) :
    C.supp ∩ A ⊆ U ∨ Disjoint (C.supp ∩ A) U := by
  classical
  by_cases hin : C.supp ∩ A ⊆ U
  · exact Or.inl hin
  right
  apply Set.disjoint_left.mpr
  intro u hu huU
  obtain ⟨v, hv, hvU⟩ : ∃ v, v ∈ C.supp ∩ A ∧ v ∉ U := by
    by_contra hn
    apply hin
    intro v hv
    by_contra hvU
    exact hn ⟨v, hv, hvU⟩
  have huv : K.Reachable u v := (C.reachable_of_mem_supp hu.1 hv.1).mono hle
  have hreach : ∀ b ∈ A, K.Reachable b u := by
    intro b hb
    by_cases hbU : b ∈ U
    · exact harc b hb u hu.2 hbU huU
    · exact (hother b hb v hv.2 hbU hvU).trans huv.symm
  obtain ⟨p, hpC, hpA⟩ := hh
  obtain ⟨q, hqC, hqA⟩ := hz
  have hhp : K.Reachable h p :=
    ((J.connectedComponentMk h).reachable_of_mem_supp (show h ∈ _ from rfl) hpC).mono hle
  have hzq : K.Reachable z q :=
    ((J.connectedComponentMk z).reachable_of_mem_supp (show z ∈ _ from rfl) hqC).mono hle
  exact hnot (hhp.trans ((hreach p hpA).trans ((hreach q hqA).symm.trans hzq.symm)))

/-- Any two vertices on the support of an actual walk are reachable. -/
theorem arc_walk_support_reachable {K : SimpleGraph V} {a b u v : V}
    (p : K.Walk a b) (hu : u ∈ p.support) (hv : v ∈ p.support) :
    K.Reachable u v := by
  classical
  exact (p.takeUntil u hu).reachable.symm.trans (p.takeUntil v hv).reachable

/-- Two actual arc walks supply the reachability premises in the contact
partition theorem. Their union is the literal cycle-contact vertex set. -/
theorem puncture_contacts_respect_arc_walks
    {J K : SimpleGraph V} (hle : J ≤ K) {a b c d : V}
    (p : K.Walk a b) (q : K.Walk c d) (h z : V)
    (hnot : ¬ K.Reachable h z)
    (hh : ((J.connectedComponentMk h).supp ∩
      {v | v ∈ p.support ∨ v ∈ q.support}).Nonempty)
    (hz : ((J.connectedComponentMk z).supp ∩
      {v | v ∈ p.support ∨ v ∈ q.support}).Nonempty)
    (C : J.ConnectedComponent) :
    C.supp ∩ {v | v ∈ p.support ∨ v ∈ q.support} ⊆ {v | v ∈ p.support} ∨
      Disjoint (C.supp ∩ {v | v ∈ p.support ∨ v ∈ q.support})
        {v | v ∈ p.support} := by
  apply puncture_contacts_respect_two_arcs hle
    {v | v ∈ p.support ∨ v ∈ q.support} {v | v ∈ p.support} h z hnot hh hz
  · intro u hu v hv huP hvP
    exact arc_walk_support_reachable p huP hvP
  · intro u hu v hv huP hvP
    have huQ : u ∈ q.support := hu.elim (fun hp => (huP hp).elim) id
    have hvQ : v ∈ q.support := hv.elim (fun hp => (hvP hp).elim) id
    exact arc_walk_support_reachable q huQ hvQ

/-- When the two designated components are separated after reconnecting
each arc, at least one has all its contacts on the chosen inner arc. -/
theorem separated_designated_component_on_inner_arc
    {J K : SimpleGraph V} (hle : J ≤ K) (A U : Set V) (h z : V)
    (hnot : ¬ K.Reachable h z)
    (hh : ((J.connectedComponentMk h).supp ∩ A).Nonempty)
    (hz : ((J.connectedComponentMk z).supp ∩ A).Nonempty)
    (hpart : ∀ C : J.ConnectedComponent,
      C.supp ∩ A ⊆ U ∨ Disjoint (C.supp ∩ A) U)
    (hother : ∀ u ∈ A, ∀ v ∈ A, u ∉ U → v ∉ U → K.Reachable u v) :
    (J.connectedComponentMk h).supp ∩ A ⊆ U ∨
      (J.connectedComponentMk z).supp ∩ A ⊆ U := by
  rcases hpart (J.connectedComponentMk h) with hin | hout
  · exact Or.inl hin
  rcases hpart (J.connectedComponentMk z) with hin | hout'
  · exact Or.inr hin
  obtain ⟨u, huC, huA⟩ := hh
  obtain ⟨v, hvC, hvA⟩ := hz
  have huU : u ∉ U := fun hu => Set.disjoint_left.mp hout ⟨huC, huA⟩ hu
  have hvU : v ∉ U := fun hv => Set.disjoint_left.mp hout' ⟨hvC, hvA⟩ hv
  have hhu : K.Reachable h u :=
    ((J.connectedComponentMk h).reachable_of_mem_supp (show h ∈ _ from rfl) huC).mono hle
  have hzv : K.Reachable z v :=
    ((J.connectedComponentMk z).reachable_of_mem_supp (show z ∈ _ from rfl) hvC).mono hle
  exact (hnot (hhu.trans ((hother u huA v hvA huU hvU).trans hzv.symm))).elim

/-- Rotating a cycle does not change its full-deletion graph. Thus
consecutive punctures can use one fixed component universe. -/
theorem full_cycle_deletion_rotate [DecidableEq V]
    {G : SimpleGraph V} {a : V} (p : G.Walk a a) (b : V)
    (hb : b ∈ p.support) :
    G.deleteEdges (p.rotate b hb).edgeSet = G.deleteEdges p.edgeSet := by
  have hs : (p.rotate b hb).edgeSet = p.edgeSet := by
    ext e
    exact (p.rotate_edges b hb).perm.mem_iff
  rw [hs]

/-- The contact vertex set also stays fixed under cycle rotation. -/
theorem cycle_contact_support_rotate [DecidableEq V]
    {G : SimpleGraph V} {a : V} (p : G.Walk a a) (b : V)
    (hb : b ∈ p.support) :
    {v | v ∈ (p.rotate b hb).support} = {v | v ∈ p.support} := by
  ext v
  exact p.mem_support_rotate_iff b hb

/-- Moving the first edge of a closed trail to its end preserves edge
uniqueness, giving the trail required for the next puncture choice. -/
theorem cycle_shift_first_edge_isTrail
    {G : SimpleGraph V} (x a : V) (hxa : G.Adj x a) (q : G.Walk a x)
    (hp : (SimpleGraph.Walk.cons hxa q).IsTrail) :
    (q.append hxa.toWalk).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_append]
  change (q.edges ++ [s(x, a)]).Nodup
  rw [List.nodup_append_comm]
  exact hp.edges_nodup

/-- A closed walk of length at least four has a literal four-edge initial
segment and residual walk, including when the fourth vertex is the root. -/
theorem closed_walk_four_edge_decomposition
    {G : SimpleGraph V} {x : V} (p : G.Walk x x) (hlen : 4 ≤ p.length) :
    ∃ a b c d, ∃ hxa : G.Adj x a, ∃ hab : G.Adj a b,
      ∃ hbc : G.Adj b c, ∃ hcd : G.Adj c d, ∃ r : G.Walk d x,
        p = SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
          (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r))) := by
  cases p with
  | nil => simp at hlen
  | @cons _ a _ hxa q =>
    cases q with
    | nil => simp at hlen
    | @cons _ b _ hab q =>
      cases q with
      | nil => simp at hlen
      | @cons _ c _ hbc q =>
        cases q with
        | nil => simp at hlen
        | @cons _ d _ hcd r => exact ⟨a, b, c, d, hxa, hab, hbc, hcd, r, rfl⟩

/-- Cycle simplicity supplies the nonadjacent-vertex guards for both
consecutive two-edge punctures, also on a cycle of length exactly four. -/
theorem cycle_four_edge_segment_guards
    {G : SimpleGraph V} (x a b c d : V)
    (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (r : G.Walk d x)
    (hp : (SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))).IsCycle) :
    x ≠ b ∧ a ≠ c ∧ b ≠ d := by
  let p := SimpleGraph.Walk.cons hxa (SimpleGraph.Walk.cons hab
    (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd r)))
  have hlen : 4 ≤ p.length := by simp [p]
  refine ⟨?_, ?_, ?_⟩
  · intro hxb
    have he : p.getVert 2 = x := by simpa [p] using hxb.symm
    have hh := (hp.getVert_endpoint_iff (i := 2) (by change 2 ≤ p.length; omega)).mp he
    change 2 = 0 ∨ 2 = p.length at hh
    omega
  · intro hac
    have he : p.getVert 1 = p.getVert 3 := by simpa [p] using hac
    have hi := hp.getVert_injOn (by change 1 ≤ 1 ∧ 1 ≤ p.length; omega)
      (by change 1 ≤ 3 ∧ 3 ≤ p.length; omega) he
    omega
  · intro hbd
    have he : p.getVert 2 = p.getVert 4 := by simpa [p] using hbd
    have hi := hp.getVert_injOn (by change 1 ≤ 2 ∧ 2 ≤ p.length; omega)
      (by change 1 ≤ 4 ∧ 4 ≤ p.length; omega) he
    omega

end Gallai.TwoException
