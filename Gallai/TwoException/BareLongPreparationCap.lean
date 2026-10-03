/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongPreparationTransport

@[expose] public section

/-! # E-degree control before the windmill-side puncture -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longCapAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Preparing every ordinary contact leaves only the original hub as a
possible E-degree exception. The possibly newly even second endpoint has
only h as an even neighbour; h itself has E-degree at most one.
No connectedness of the prepared graph is assumed. -/
theorem bare_long_ordinary_preparation_cap
    (h v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj v t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj v t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h) :
    let Q := ordinaryMatePuncture (starPuncture G v B) M
    (∀ t, Even (Q.degree t) → t ≠ (x : V) → eDegree Q t ≤ 3) ∧
      eDegree Q v ≤ 1 ∧ eDegree Q h ≤ 1 ∧
      (∀ t, Q.Adj v t → Even (Q.degree t) → t = h) := by
  classical
  let Q := ordinaryMatePuncture (starPuncture G v B) M
  have hsub : Q ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1)
  have hprofile := ordinary_star_mates_even_preserved v B M hadj hleaves hdis havoid hedges
  have hl := ordinary_star_mates_leaves_odd v B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have hm := ordinary_star_mates_endpoints_odd v B M hdis havoid hedges
  have hcenter : ∀ t, Q.Adj v t → Even (Q.degree t) → t = h := by
    intro t hvt ht
    rcases hprofile t ht with ho | htv
    · rcases hcontacts t (hsub hvt) ho with htB | ⟨e,he,hte⟩ | hth
      · exact False.elim ((Nat.not_even_iff_odd.mpr (hl t htB)) ht)
      · obtain ⟨ho1,ho2⟩ := hm e he
        rcases hte with hte | hte
        · subst t
          exact False.elim ((Nat.not_even_iff_odd.mpr ho1) ht)
        · subst t
          exact False.elim ((Nat.not_even_iff_odd.mpr ho2) ht)
      · exact hth
    · subst t
      exact False.elim (Q.irrefl hvt)
  have hvCap : eDegree Q v ≤ 1 :=
    ordinary_star_mates_centre_eDegree_le_one h v B M hadj hleaves hdis havoid hedges hcontacts
  obtain ⟨_,_,_,_,_,hhzero,hcap⟩ := H.counterexample.1
  have hhCap : eDegree Q h ≤ 1 := by
    have hsubset : evenNeighbors Q h ⊆ {v} := by
      intro t ht
      obtain ⟨hht,he⟩ := (mem_evenNeighbors (G := Q) h t).mp ht
      apply Finset.mem_singleton.mpr
      rcases hprofile t he with ho | htv
      · have hmem := (mem_evenNeighbors (G := G) h t).mpr ⟨hsub hht,ho⟩
        have hpos : 0 < eDegree G h := Finset.card_pos.mpr ⟨t,hmem⟩
        omega
      · exact htv
    exact (Finset.card_le_card hsubset).trans (by simp)
  refine ⟨?_,hvCap,hhCap,hcenter⟩
  intro t ht htx
  by_cases htv : t = v
  · subst t
    change eDegree Q v ≤ 3
    exact hvCap.trans (by decide)
  by_cases hth : t = h
  · subst t
    change eDegree Q h ≤ 3
    exact hhCap.trans (by decide)
  have htOriginal : Even (G.degree t) := (hprofile t ht).resolve_right htv
  have hsubset : evenNeighbors Q t ⊆ evenNeighbors G t := by
    intro w hw
    obtain ⟨htw,he⟩ := (mem_evenNeighbors (G := Q) t w).mp hw
    rcases hprofile w he with ho | hwv
    · exact (mem_evenNeighbors (G := G) t w).mpr ⟨hsub htw,ho⟩
    · subst w
      exact False.elim (hth (hcenter t htw.symm ht))
  exact (Finset.card_le_card hsubset).trans (hcap t htOriginal hth htx)

/-- Graph-native preparation at the second endpoint of the selected odd
edge. Neither a deletion family nor an auxiliary cap is supplied by the
caller. This is the input to the joint windmill-side component budget. -/
theorem bare_long_native_preparation
    (h u v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (huOdd : Odd (G.degree u)) (hvOdd : Odd (G.degree v)) (huv : G.Adj u v)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t) :
    ∃ B : Finset V, ∃ M : List (V × V),
      (∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
        t ∉ Subtype.val '' C.supp) ∧
      M.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
        e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
        e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp) ∧
      (∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
        t ∈ B ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) ∧
      let Q := ordinaryMatePuncture (starPuncture G v B) M
      Q.Adj u v ∧ Q.degree u = G.degree u ∧ Q.degree h = G.degree h ∧
      (∀ t, Even (Q.degree t) → t ≠ (x : V) → eDegree Q t ≤ 3) ∧
      eDegree Q v ≤ 1 ∧ eDegree Q h ≤ 1 ∧
      (∀ t, Q.Adj v t → Even (Q.degree t) → t = h) ∧
      (∀ w ∈ Subtype.val '' C.supp, Q.degree w = G.degree w ∧
        ∀ t, Q.Adj w t ↔ G.Adj w t) := by
  classical
  let S : Finset (evenVertices G) :=
    Finset.univ.filter (fun t => G.Adj v t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  obtain ⟨P,mates,_,_,_,_,_,hB,hdis,hM,hcontacts⟩ :=
    bare_long_ordinary_preparation_family h v x H C hxC hsep
  let B := (F.biUnion P).image Subtype.val
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  change ∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
    t ∉ Subtype.val '' C.supp at hB
  change M.Pairwise (fun e f =>
    e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) at hdis
  change ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
    e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
    e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp at hM
  change ∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
    t ∈ B ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2 at hcontacts
  have hadj := fun t ht => (hB t ht).1
  have hleaves := fun t ht => (hB t ht).2.1
  have hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) :=
    fun e he => ⟨(hM e he).1,(hM e he).2.1,(hM e he).2.2.1⟩
  have havoid : ∀ e ∈ M, e.1 ≠ v ∧ e.2 ≠ v ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have hn := Nat.not_even_iff_odd.mpr hvOdd
    exact ⟨fun hh => hn (hh ▸ (hedges e he).2.1),
      fun hh => hn (hh ▸ (hedges e he).2.2),
      (hM e he).2.2.2.1,(hM e he).2.2.2.2.1⟩
  have hc : ∀ t, G.Adj v t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hvt ht
    by_cases hth : t = h
    · exact Or.inr (Or.inr hth)
    · rcases hcontacts t hvt ht hth with hb | hm
      · exact Or.inl hb
      · exact Or.inr (Or.inl hm)
  obtain ⟨hcap,hvCap,hhCap,hcenter⟩ :=
    bare_long_ordinary_preparation_cap h v x H B M hadj hleaves hdis havoid hedges hc
  obtain ⟨hQ,hdu,_⟩ := long_ordinary_preparation_reserved_degree u v B M huOdd hvOdd huv
    (fun t ht => ⟨hadj t ht,hleaves t ht⟩) (fun e he => (hedges e he).2)
  have hhv : h ≠ v := by
    intro hh
    exact (Nat.not_even_iff_odd.mpr hvOdd) (hh ▸ H.counterexample.1.2.2.2.1)
  have hdh := (long_ordinary_preparation_unchanged (G := G) v h B M hhv
    (fun ht => (hB h ht).2.2.1 rfl)
    (fun e he => ⟨(hM e he).2.2.2.2.2.1,(hM e he).2.2.2.2.2.2.1⟩)).1
  have hwindmill := long_ordinary_preparation_windmill_unchanged v hvOdd C B M
    (fun t ht => (hB t ht).2.2.2)
    (fun e he => ⟨(hM e he).2.2.2.2.2.2.2.1,(hM e he).2.2.2.2.2.2.2.2⟩)
  exact ⟨B,M,hB,hdis,hM,hcontacts,hQ,hdu,hdh,hcap,hvCap,hhCap,hcenter,hwindmill⟩

end Gallai.TwoException
