/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySingleSpokeProfile

@[expose] public section

/-! # Retained contact recipient in the early spoke profile -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance retainedSpokeGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- The unpaid spoke recipient may remain a centre neighbour: deletion
makes it odd, so it contributes no current even neighbour at the centre. -/
theorem bare_early_retained_spoke_mates_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (u q : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∉ B) (hqB : q ∉ B) (hxu : x ≠ u) (hqu : q ≠ u)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (hdis : O.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ O, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ O, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = q ∨ t = h) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1 ∧
      Odd (J.degree x) := by
  classical
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  let J := ordinaryMatePuncture K O
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → eDegree J t ≤ 3) ∧ eDegree J u ≤ 1 ∧
    Odd (J.degree x)
  rcases H.counterexample.1 with ⟨_,_,_,_,hxEven,hhzero,hcap⟩
  have hprofile := early_single_spoke_even_profile u x q B O hleaves hxEven hqEven
    (fun e he => (hedges e he).2)
  have hxOdd : Odd (J.degree x) := by
    have ho := early_single_spoke_recipient_odd u q x B O hqu hxu hxB hxq.symm
      hxEven (fun e he => ⟨(havoid e he).2.2.2.2.1.symm,
        (havoid e he).2.2.2.2.2.1.symm⟩)
    have he : s(q,x) = s(x,q) := Sym2.eq_swap
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rw [he] at ho
    exact ho
  have hqOdd : Odd (J.degree q) := by
    have ho := early_single_spoke_recipient_odd u x q B O hxu hqu hqB hxq
      hqEven (fun e he => ⟨(havoid e he).2.2.2.2.2.2.1.symm,
        (havoid e he).2.2.2.2.2.2.2.symm⟩)
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    exact ho
  have hmOdd := early_spoke_mates_endpoints_odd u x q B O hdis havoid hedges
  have hsub : J ≤ G := fun _ _ ha => ((ordinaryMatePuncture_le (G := K) O) ha).1.1
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hcentre : ∀ t, J.Adj u t → Even (J.degree t) → t = h := by
    intro t hut ht
    rcases hprofile t ht with he | rfl
    · rcases hcontacts t (hsub hut) he with htB | ⟨e,hem,hte⟩ | htx | htq | hth
      · exact False.elim (starPuncture_missing G u B huB t htB
          ((ordinaryMatePuncture_le (G := K) O) hut).1)
      · obtain ⟨h1,h2⟩ := hmOdd e hem
        rcases hte with hte | hte
        · exact False.elim ((Nat.not_even_iff_odd.mpr h1) (hte ▸ ht))
        · exact False.elim ((Nat.not_even_iff_odd.mpr h2) (hte ▸ ht))
      · exact False.elim ((Nat.not_even_iff_odd.mpr hxOdd) (htx ▸ ht))
      · exact False.elim ((Nat.not_even_iff_odd.mpr hqOdd) (htq ▸ ht))
      · exact hth
    · exact False.elim (J.irrefl hut)
  have hc : ∀ t, Even (G.degree t) → t ≠ x → eDegree G t ≤ 3 := by
    intro t ht htx
    by_cases hth : t = h
    · subst t
      omega
    · exact hcap t ht hth htx
  refine ⟨puncture_cap_of_one_new_even_center h x u hsub hprofile hxOdd hhzero hc hcentre,
    ?_,hxOdd⟩
  change #(evenNeighbors J u) ≤ 1
  apply (Finset.card_le_card (show evenNeighbors J u ⊆ {h} from ?_)).trans_eq
    (Finset.card_singleton h)
  intro t ht
  obtain ⟨hut,htEven⟩ := (mem_evenNeighbors (G := J) u t).mp ht
  exact Finset.mem_singleton.mpr (hcentre t hut htEven)

end Gallai.TwoException
