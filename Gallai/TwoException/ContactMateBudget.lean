/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactMateAssembly
public import Gallai.TwoException.ContactMateProfile

@[expose] public section

/-! # A bare-counterexample budget for mate-contact punctures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mateBudgetStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance mateBudgetDeleteAdj (u p q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(p,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Derive the floor budget from the literal deletions and original contacts,
without assuming a decomposition, component cap, or non-SET certificate. -/
theorem bare_contact_mate_floor
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u p q : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleavesEven : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∈ B) (hxp : x ≠ p) (hxq : x ≠ q)
    (hpu : p ≠ u) (hqu : q ≠ u) (hpB : p ∉ B) (hqB : q ∉ B)
    (hpq : G.Adj p q) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q))
    (hpx : G.Adj p x) (hp : eDegree G p = 2)
    (hqx : G.Adj q x) (hq : eDegree G q = 2)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) → t ∈ B ∨ t = p ∨ t = q)
    (hleaves : ∀ t ∈ B, t = x ∨ t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (r : V) (hxr : ((starPuncture G u B).deleteEdges {s(p,q)}).Adj x r)
    (hrx : G.Adj r x) (hr : eDegree G r = 2) :
    HasPathBudget ((starPuncture G u B).deleteEdges {s(p,q)})
      (Fintype.card V / 2) := by
  classical
  rcases H.counterexample.1 with ⟨hconn, _, _, _, hxEven, hhzero, hcapG⟩
  have hprof := contact_mate_puncture_profile u x p q B hu hadj huOdd hB
    hleavesEven hxB hxp hxq hpu hqu hpB hqB hpq hpEven hqEven
  have hsub : (starPuncture G u B).deleteEdges {s(p,q)} ≤ G :=
    fun _ _ ha => ha.1.1
  have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hprof.1
  have hcap : ∀ t,
      Even (((starPuncture G u B).deleteEdges {s(p,q)}).degree t) →
      eDegree ((starPuncture G u B).deleteEdges {s(p,q)}) t ≤ 3 := by
    intro t ht
    have htx : t ≠ x := by
      intro heq
      subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.1) ht
    by_cases hth : t = h
    · subst t
      have hm := hmono h
      rw [hhzero] at hm
      omega
    · exact (hmono t).trans (hcapG t (hprof.1 t ht) hth htx)
  have hcentre : eDegree ((starPuncture G u B).deleteEdges {s(p,q)}) u = 0 := by
    apply eDegree_eq_zero_of_no_even_neighbor
    intro t hut htEven
    rcases hcontacts t hut.1.1 (hprof.1 t htEven) with htB | htp | htq
    · exact (starPuncture_missing G u B hu t htB) hut.1
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.2.1) htEven
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.2.2) htEven
  exact contact_mate_floor_of_boundary_data hconn h u x p q B hprof.1 hcap
    hxEven hprof.2.1 hcentre hhzero hpx hp hqx hq hleaves r hxr hrx hr

end Gallai.TwoException
