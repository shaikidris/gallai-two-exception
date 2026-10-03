/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # The length-one three-spoke puncture

The first concrete branch of the degree-three hub reduction deletes the three
even spokes at its first private vertex `a`: one to the hub and two to the
remaining even neighbours.  This module records the literal graph operation
and its degree ledger before any pendant attachment or component analysis.
-/

namespace Gallai

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete the three distinct spokes at the first degree-three private vertex.
The sequential form lets the existing single-edge degree facts account for
each deletion exactly. -/
abbrev threeSpokePuncture (a x q r : V) : SimpleGraph V :=
  ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).deleteEdges {s(a, r)}

/-- The literal multi-edge puncture has decidable adjacency on the finite
ambient type. -/
noncomputable instance instDecidableRelAdjThreeSpokePuncture (a x q r : V) :
    DecidableRel (threeSpokePuncture G a x q r).Adj :=
  by
    change DecidableRel
      (((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).deleteEdges {s(a, r)}).Adj
    infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- A component of the literal three-spoke puncture has no surviving edge to
its complement.  Hence every original crossing edge is one of the three
deleted spokes.  This is the first, orientation-free boundary extraction used
in the length-one corridor SET audit. -/
theorem threeSpokePuncture_component_crossing_is_deleted
    (a x q r u v : V) (C : (threeSpokePuncture G a x q r).ConnectedComponent)
    (hu : u ∈ C.supp) (hv : v ∉ C.supp) (huv : G.Adj u v) :
    s(u, v) = s(a, x) ∨ s(u, v) = s(a, q) ∨ s(u, v) = s(a, r) := by
  by_contra h
  push Not at h
  have h₁ : (G.deleteEdges {s(a, x)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simp [h.1]⟩
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨h₁, by simp [h.2.1]⟩
  have h₃ : (threeSpokePuncture G a x q r).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨h₂, by simp [h.2.2]⟩
  exact hv (C.mem_supp_of_adj_mem_supp hu h₃)

omit [Fintype V] [DecidableRel G.Adj] in
/-- If a three-spoke puncture component contains `q` but none of the other
deleted-spoke endpoints, every original boundary edge is oriented from `q` to
the deleted centre `a`.  This is the literal boundary shape required before
the existing hanging-SET consumer can be applied. -/
theorem threeSpokePuncture_component_crossing_is_qa
    (a x q r u v : V) (C : (threeSpokePuncture G a x q r).ConnectedComponent)
    (ha : a ∉ C.supp) (hx : x ∉ C.supp) (hr : r ∉ C.supp)
    (hu : u ∈ C.supp) (hv : v ∉ C.supp) (huv : G.Adj u v) :
    u = q ∧ v = a := by
  rcases threeSpokePuncture_component_crossing_is_deleted G a x q r u v C hu hv huv with
      hax | haq | har
  · rcases Sym2.eq_iff.mp hax with ⟨hua, hvx⟩ | ⟨hux, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hx (hux ▸ hu)).elim
  · rcases Sym2.eq_iff.mp haq with ⟨hua, hvq⟩ | ⟨huq, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact ⟨huq, hva⟩
  · rcases Sym2.eq_iff.mp har with ⟨hua, hvr⟩ | ⟨hur, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hr (hur ▸ hu)).elim

omit [Fintype V] [DecidableRel G.Adj] in
/-- The symmetric `r`-side orientation of the preceding component-boundary
lemma. -/
theorem threeSpokePuncture_component_crossing_is_ra
    (a x q r u v : V) (C : (threeSpokePuncture G a x q r).ConnectedComponent)
    (ha : a ∉ C.supp) (hx : x ∉ C.supp) (hq : q ∉ C.supp)
    (hu : u ∈ C.supp) (hv : v ∉ C.supp) (huv : G.Adj u v) :
    u = r ∧ v = a := by
  rcases threeSpokePuncture_component_crossing_is_deleted G a x q r u v C hu hv huv with
      hax | haq | har
  · rcases Sym2.eq_iff.mp hax with ⟨hua, hvx⟩ | ⟨hux, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hx (hux ▸ hu)).elim
  · rcases Sym2.eq_iff.mp haq with ⟨hua, hvq⟩ | ⟨huq, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hq (huq ▸ hu)).elim
  · rcases Sym2.eq_iff.mp har with ⟨hua, hvr⟩ | ⟨hur, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact ⟨hur, hva⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Away from the deleted centre, the literal three-spoke puncture preserves
all adjacencies.  This is the internal-edge counterpart to the component
boundary lemmas. -/
theorem threeSpokePuncture_adj_iff_of_ne_center
    (a x q r u v : V) (hua : u ≠ a) (hva : v ≠ a) :
    (threeSpokePuncture G a x q r).Adj u v ↔ G.Adj u v := by
  constructor
  · intro huv
    exact (SimpleGraph.deleteEdges_adj.mp
      (SimpleGraph.deleteEdges_adj.mp
        (SimpleGraph.deleteEdges_adj.mp huv).1).1).1
  · intro huv
    have hne (t : V) : s(u, v) ≠ s(a, t) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨hua', _⟩ | ⟨_, hva'⟩
      · exact hua hua'
      · exact hva hva'
    have h₁ : (G.deleteEdges {s(a, x)}).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simp [hne x]⟩
    have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨h₁, by simp [hne q]⟩
    exact SimpleGraph.deleteEdges_adj.mpr ⟨h₂, by simp [hne r]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An edge distinct from the deleted edge survives a one-edge puncture. -/
theorem adj_delete_edge_of_ne (x y a b : V) (hab : G.Adj a b)
    (hne : s(a, b) ≠ s(x, y)) :
    (G.deleteEdges {s(x, y)}).Adj a b := by
  apply SimpleGraph.deleteEdges_adj.mpr
  exact ⟨hab, by simp [hne]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The second spoke is still present after deleting the hub spoke. -/
theorem threeSpoke_first_keeps_second (a x q : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (hxq : x ≠ q) :
    (G.deleteEdges {s(a, x)}).Adj a q := by
  apply adj_delete_edge_of_ne G a x a q haq
  intro he
  rcases Sym2.eq_iff.mp he with ⟨_, hxq'⟩ | ⟨hax', _⟩
  · exact hxq hxq'.symm
  · exact hax.ne hax'

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The third spoke survives the two earlier deletions. -/
theorem threeSpoke_first_two_keep_third (a x q r : V)
    (hax : G.Adj a x) (har : G.Adj a r)
    (hxr : x ≠ r) (hqr : q ≠ r) :
    ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj a r := by
  have har₁ : (G.deleteEdges {s(a, x)}).Adj a r := by
    apply adj_delete_edge_of_ne G a x a r har
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, hxr'⟩ | ⟨hax', _⟩
    · exact hxr hxr'.symm
    · exact hax.ne hax'
  apply adj_delete_edge_of_ne (G.deleteEdges {s(a, x)}) a q a r har₁
  intro he
  rcases Sym2.eq_iff.mp he with ⟨_, hqr'⟩ | ⟨_, hra⟩
  · exact hqr hqr'.symm
  · exact har.ne hra.symm

/-- The three named spokes are absent from the literal puncture.  These
negative adjacency facts are the local separation facts needed when a
retained centre-neighbour is transported back to the original graph. -/
theorem threeSpokePuncture_not_adj_ax (a x q r : V) :
    ¬ (threeSpokePuncture G a x q r).Adj a x := by
  intro h
  obtain ⟨h₂, _⟩ := SimpleGraph.deleteEdges_adj.mp h
  obtain ⟨h₁, _⟩ := SimpleGraph.deleteEdges_adj.mp h₂
  obtain ⟨_, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h₁
  exact hnot (by simp)

/-- The second named spoke is absent from the literal puncture. -/
theorem threeSpokePuncture_not_adj_aq (a x q r : V) :
    ¬ (threeSpokePuncture G a x q r).Adj a q := by
  intro h
  obtain ⟨h₂, _⟩ := SimpleGraph.deleteEdges_adj.mp h
  obtain ⟨_, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h₂
  exact hnot (by simp)

/-- The third named spoke is absent from the literal puncture. -/
theorem threeSpokePuncture_not_adj_ar (a x q r : V) :
    ¬ (threeSpokePuncture G a x q r).Adj a r := by
  intro h
  obtain ⟨_, hnot⟩ := SimpleGraph.deleteEdges_adj.mp h
  exact hnot (by simp)

/-- Restoring the `ax` and `aq` spokes after the literal three-spoke puncture
leaves exactly the one-edge puncture at `ar`. -/
theorem threeSpokePuncture_restore_ax_aq_eq_delete_ar (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    threeSpokePuncture G a x q r ⊔
      ({x, q} : Finset V).sup (SimpleGraph.edge a) =
      G.deleteEdges {s(a, r)} := by
  ext u v
  by_cases hua : u = a
  · subst u
    by_cases hva : v = a
    · subst v
      simp [threeSpokePuncture, SimpleGraph.edge_adj]
    · by_cases hvx : v = x
      · subst v
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxr]
      · by_cases hvq : v = q
        · subst v
          simp [threeSpokePuncture, SimpleGraph.edge_adj, haq, haq.symm,
            haq.ne, haq.ne.symm, hqr]
        · simp [threeSpokePuncture, SimpleGraph.edge_adj, hva, hvx, hvq]
  · by_cases hva : v = a
    · subst v
      by_cases hux : u = x
      · subst u
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxr]
      · by_cases huq : u = q
        · subst u
          simp [threeSpokePuncture, SimpleGraph.edge_adj, haq, haq.symm,
            haq.ne, haq.ne.symm, hqr]
        · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hux, huq]
    · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hva]

/-- Restoring the `ax` and `ar` spokes after the literal three-spoke puncture
leaves exactly the one-edge puncture at `aq`. -/
theorem threeSpokePuncture_restore_ax_ar_eq_delete_aq (a x q r : V)
    (hax : G.Adj a x) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    threeSpokePuncture G a x q r ⊔
      ({x, r} : Finset V).sup (SimpleGraph.edge a) =
      G.deleteEdges {s(a, q)} := by
  ext u v
  by_cases hua : u = a
  · subst u
    by_cases hva : v = a
    · subst v
      simp [threeSpokePuncture, SimpleGraph.edge_adj]
    · by_cases hvx : v = x
      · subst v
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxq]
      · by_cases hvr : v = r
        · subst v
          simp [threeSpokePuncture, SimpleGraph.edge_adj, har, har.symm,
            har.ne, har.ne.symm, hqr, hqr.symm]
        · simp [threeSpokePuncture, SimpleGraph.edge_adj, hva, hvx, hvr]
  · by_cases hva : v = a
    · subst v
      by_cases hux : u = x
      · subst u
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxq]
      · by_cases hur : u = r
        · subst u
          simp [threeSpokePuncture, SimpleGraph.edge_adj, har, har.symm,
            har.ne, har.ne.symm, hqr, hqr.symm]
        · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hux, hur]
    · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hva]

/-- Restoring all three named spokes after the literal puncture recovers the
original graph exactly.  This is the no-pending-leaf branch of the prescribed
three-star restoration. -/
theorem threeSpokePuncture_restore_all_eq (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    threeSpokePuncture G a x q r ⊔
      ({x, q, r} : Finset V).sup (SimpleGraph.edge a) = G := by
  ext u v
  by_cases hua : u = a
  · subst u
    by_cases hva : v = a
    · subst v
      simp [threeSpokePuncture, SimpleGraph.edge_adj]
    · by_cases hvx : v = x
      · subst v
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxr]
      · by_cases hvq : v = q
        · subst v
          simp [threeSpokePuncture, SimpleGraph.edge_adj, haq, haq.symm,
            haq.ne, haq.ne.symm, hqr]
        · by_cases hvr : v = r
          · subst v
            simp [threeSpokePuncture, SimpleGraph.edge_adj, har, har.symm,
              har.ne, har.ne.symm]
          · simp [threeSpokePuncture, SimpleGraph.edge_adj, hva, hvx, hvq, hvr]
  · by_cases hva : v = a
    · subst v
      by_cases hux : u = x
      · subst u
        simp [threeSpokePuncture, SimpleGraph.edge_adj, hax, hax.symm,
          hax.ne, hax.ne.symm, hxr]
      · by_cases huq : u = q
        · subst u
          simp [threeSpokePuncture, SimpleGraph.edge_adj, haq, haq.symm,
            haq.ne, haq.ne.symm, hqr]
        · by_cases hur : u = r
          · subst u
            simp [threeSpokePuncture, SimpleGraph.edge_adj, har, har.symm,
              har.ne, har.ne.symm]
          · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hux, huq, hur]
    · simp [threeSpokePuncture, SimpleGraph.edge_adj, hua, hva]

/-- Deleting the three spokes lowers the centre degree by exactly three. -/
theorem threeSpokePuncture_degree_center_add_three (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    (threeSpokePuncture G a x q r).degree a + 3 = G.degree a := by
  have h₁ : (G.deleteEdges {s(a, x)}).degree a + 1 = G.degree a :=
    degree_delete_edge_add_one G a x hax
  have h₂adj : (G.deleteEdges {s(a, x)}).Adj a q :=
    threeSpoke_first_keeps_second G a x q hax haq hxq
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree a + 1 =
      (G.deleteEdges {s(a, x)}).degree a :=
    degree_delete_edge_add_one (G.deleteEdges {s(a, x)}) a q h₂adj
  have h₃adj : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj a r :=
    threeSpoke_first_two_keep_third G a x q r hax har hxr hqr
  have h₃ : (threeSpokePuncture G a x q r).degree a + 1 =
      ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree a :=
    degree_delete_edge_add_one ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}) a r h₃adj
  omega

/-- The hub is incident with exactly the first deleted spoke. -/
theorem threeSpokePuncture_degree_hub_add_one (a x q r : V)
    (hax : G.Adj a x) (hxq : x ≠ q) (hxr : x ≠ r) :
    (threeSpokePuncture G a x q r).degree x + 1 = G.degree x := by
  have h₁ : (G.deleteEdges {s(a, x)}).degree x + 1 = G.degree x :=
    degree_delete_edge_add_one_other G a x hax
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree x =
      (G.deleteEdges {s(a, x)}).degree x :=
    degree_delete_edge_of_ne (G.deleteEdges {s(a, x)}) a q x hax.ne.symm hxq
  have h₃ : (threeSpokePuncture G a x q r).degree x =
      ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree x :=
    degree_delete_edge_of_ne ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)})
      a r x hax.ne.symm hxr
  omega

/-- The first non-hub leaf is incident with exactly the second deleted spoke. -/
theorem threeSpokePuncture_degree_first_leaf_add_one (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q)
    (hxq : x ≠ q) (hqr : q ≠ r) :
    (threeSpokePuncture G a x q r).degree q + 1 = G.degree q := by
  have h₁ : (G.deleteEdges {s(a, x)}).degree q = G.degree q :=
    degree_delete_edge_of_ne G a x q haq.ne.symm hxq.symm
  have h₂adj : (G.deleteEdges {s(a, x)}).Adj a q :=
    threeSpoke_first_keeps_second G a x q hax haq hxq
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree q + 1 =
      (G.deleteEdges {s(a, x)}).degree q :=
    degree_delete_edge_add_one_other (G.deleteEdges {s(a, x)}) a q h₂adj
  have h₃ : (threeSpokePuncture G a x q r).degree q =
      ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree q :=
    degree_delete_edge_of_ne ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)})
      a r q haq.ne.symm hqr
  omega

/-- The second non-hub leaf is incident with exactly the third deleted spoke. -/
theorem threeSpokePuncture_degree_second_leaf_add_one (a x q r : V)
    (hax : G.Adj a x) (har : G.Adj a r)
    (hxr : x ≠ r) (hqr : q ≠ r) :
    (threeSpokePuncture G a x q r).degree r + 1 = G.degree r := by
  have h₁ : (G.deleteEdges {s(a, x)}).degree r = G.degree r :=
    degree_delete_edge_of_ne G a x r har.ne.symm hxr.symm
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree r =
      (G.deleteEdges {s(a, x)}).degree r :=
    degree_delete_edge_of_ne (G.deleteEdges {s(a, x)}) a q r har.ne.symm hqr.symm
  have h₃adj : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj a r :=
    threeSpoke_first_two_keep_third G a x q r hax har hxr hqr
  have h₃ : (threeSpokePuncture G a x q r).degree r + 1 =
      ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree r :=
    degree_delete_edge_add_one_other ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)})
      a r h₃adj
  omega

/-- A vertex distinct from every endpoint of the three deleted spokes keeps
its degree. This is the literal parity-preservation fact needed before the
pendant edge is attached at the bare prescribed vertex. -/
theorem threeSpokePuncture_degree_away (a x q r h : V)
    (ha : h ≠ a) (hx : h ≠ x) (hq : h ≠ q) (hr : h ≠ r) :
    (threeSpokePuncture G a x q r).degree h = G.degree h := by
  have h₁ : (G.deleteEdges {s(a, x)}).degree h = G.degree h :=
    degree_delete_edge_of_ne G a x h ha hx
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree h =
      (G.deleteEdges {s(a, x)}).degree h :=
    degree_delete_edge_of_ne (G.deleteEdges {s(a, x)}) a q h ha hq
  have h₃ : (threeSpokePuncture G a x q r).degree h =
      ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).degree h :=
    degree_delete_edge_of_ne ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)})
      a r h ha hr
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The literal three-spoke puncture is a subgraph of the original graph. -/
theorem threeSpokePuncture_le (a x q r : V) :
    threeSpokePuncture G a x q r ≤ G := by
  intro u v huv
  change ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).deleteEdges {s(a, r)} |>.Adj u v at huv
  exact (SimpleGraph.deleteEdges_adj.mp
    (SimpleGraph.deleteEdges_adj.mp (SimpleGraph.deleteEdges_adj.mp huv).1).1).1

/-- Subtracting one or three from an even degree leaves an odd degree. -/
private theorem odd_of_add_one_eq_even {u v : ℕ}
    (huv : u + 1 = v) (hv : Even v) : Odd u := by
  apply Nat.not_even_iff_odd.mp
  rintro ⟨k, hk⟩
  rcases hv with ⟨l, hl⟩
  omega

private theorem odd_of_add_three_eq_even {u v : ℕ}
    (huv : u + 3 = v) (hv : Even v) : Odd u := by
  apply Nat.not_even_iff_odd.mp
  rintro ⟨k, hk⟩
  rcases hv with ⟨l, hl⟩
  omega

/-- If all four named old vertices are even, the length-one puncture makes
the degree-three centre, hub, and two pending leaves odd. -/
theorem threeSpokePuncture_odd_affected (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r)) :
    Odd ((threeSpokePuncture G a x q r).degree a) ∧
      Odd ((threeSpokePuncture G a x q r).degree x) ∧
      Odd ((threeSpokePuncture G a x q r).degree q) ∧
      Odd ((threeSpokePuncture G a x q r).degree r) := by
  refine ⟨odd_of_add_three_eq_even
      (threeSpokePuncture_degree_center_add_three G a x q r hax haq har hxq hxr hqr) ha,
    odd_of_add_one_eq_even
      (threeSpokePuncture_degree_hub_add_one G a x q r hax hxq hxr) hx,
    odd_of_add_one_eq_even
      (threeSpokePuncture_degree_first_leaf_add_one G a x q r hax haq hxq hqr) hq,
    odd_of_add_one_eq_even
      (threeSpokePuncture_degree_second_leaf_add_one G a x q r hax har hxr hqr) hr⟩

/-- Every vertex that remains even after the literal three-spoke puncture was
already even in the original graph. The four vertices whose parities change
are explicitly excluded by the puncture oddness ledger. -/
theorem threeSpokePuncture_even_implies_original_even (a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r)) :
    ∀ v, Even ((threeSpokePuncture G a x q r).degree v) → Even (G.degree v) := by
  obtain ⟨oa, ox, oq, or⟩ :=
    threeSpokePuncture_odd_affected G a x q r hax haq har hxq hxr hqr ha hx hq hr
  intro v hv
  by_cases hva : v = a
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr oa) hv)
  by_cases hvx : v = x
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr ox) hv)
  by_cases hvq : v = q
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr oq) hv)
  by_cases hvr : v = r
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr or) hv)
  rwa [threeSpokePuncture_degree_away G a x q r v hva hvx hvq hvr] at hv

/-- The literal three-spoke puncture satisfies the subcubic E-degree cap used
by the bare-case auxiliary. The bare vertex is handled by its zero original
E-degree; every other surviving even vertex is an original nonexceptional
even vertex. -/
theorem threeSpokePuncture_cap_of_bare_data (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hbare : eDegree G h = 0)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((threeSpokePuncture G a x q r).degree v) →
      eDegree (threeSpokePuncture G a x q r) v ≤ 3 := by
  have hEvenPreserved := threeSpokePuncture_even_implies_original_even G a x q r
    hax haq har hxq hxr hqr ha hx hq hr
  obtain ⟨_, ox, _, _⟩ :=
    threeSpokePuncture_odd_affected G a x q r hax haq har hxq hxr hqr ha hx hq hr
  have hsub : threeSpokePuncture G a x q r ≤ G :=
    threeSpokePuncture_le G a x q r
  intro v hv
  have hle : eDegree (threeSpokePuncture G a x q r) v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation
      (G := G) (J := threeSpokePuncture G a x q r) hsub hEvenPreserved v
  by_cases hvh : v = h
  · subst v
    rw [hbare] at hle
    omega
  have hvx : v ≠ x := by
    intro e
    subst v
    exact (Nat.not_even_iff_odd.mpr ox) hv
  exact hle.trans (hcap v (hEvenPreserved v hv) hvh hvx)

end Gallai
