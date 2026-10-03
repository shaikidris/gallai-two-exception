/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE5Profile
public import Gallai.TwoException.ContactE5Assembly

@[expose] public section

/-! # Derived floor budget for the E5 preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance E5BudgetStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance E5BudgetSpokeAdj (u x s : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E5BudgetMateAdj (u x s p q : V) (B : Finset V) :
    DecidableRel (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Literal E5 deletion data derives the complete auxiliary floor budget.
No decomposition, E-degree cap, or component non-SET premise is supplied. -/
theorem bare_contact_E5_floor
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u s p q : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleavesEven : ∀ t ∈ B, Even (G.degree t))
    (hxu : x ≠ u) (hsu : s ≠ u) (hxB : x ∉ B) (hsB : s ∉ B)
    (hxs : G.Adj x s) (hsEven : Even (G.degree s))
    (hpu : p ≠ u) (hqu : q ≠ u) (hpB : p ∉ B) (hqB : q ∉ B)
    (hpx : p ≠ x) (hps : p ≠ s) (hqx : q ≠ x) (hqs : q ≠ s)
    (hqp : G.Adj q p) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q))
    (hs : eDegree G s = 2) (hpxAdj : G.Adj p x) (hp : eDegree G p = 2)
    (hqxAdj : G.Adj q x) (hq : eDegree G q = 2)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ t = x ∨ t = s ∨ t = p ∨ t = q)
    (hleaves : ∀ t ∈ B, t = h ∨ (G.Adj t x ∧ eDegree G t = 2))
    (r : V)
    (hxr : (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).Adj x r)
    (hrx : G.Adj r x) (hr : eDegree G r = 2) :
    HasPathBudget (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)})
      (Fintype.card V / 2) := by
  classical
  rcases H.counterexample.1 with ⟨hconn, _, _, _, hxEven, hhzero, hcapG⟩
  have hprof := contact_E5_puncture_profile u x s p q B hu hadj huOdd hB hleavesEven
    hxu hsu hxB hsB hxs hxEven hsEven hpu hqu hpB hqB hpx hps hqx hqs
    hqp hpEven hqEven
  have hsub : ((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)} ≤ G :=
    fun _ _ ha => ha.1.1.1
  have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hprof.1
  have hcap : ∀ t,
      Even ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree t) →
      eDegree (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}) t ≤ 3 := by
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
  have hcentre : eDegree (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}) u = 0 := by
    apply eDegree_eq_zero_of_no_even_neighbor
    intro t hut htEven
    rcases hcontacts t hut.1.1.1 (hprof.1 t htEven) with htB | htx | hts | htp | htq
    · exact (starPuncture_missing G u B hu t htB) hut.1.1
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.1) htEven
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.2.1) htEven
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.2.2.1) htEven
    · subst t
      exact (Nat.not_even_iff_odd.mpr hprof.2.2.2.2) htEven
  exact contact_E5_floor_of_boundary_data hconn h u x s p q B hprof.1 hcap hxEven
    hprof.2.1 hcentre hhzero hxs.symm hs hpxAdj hp hqxAdj hq hleaves r hxr hrx hr

end Gallai.TwoException
