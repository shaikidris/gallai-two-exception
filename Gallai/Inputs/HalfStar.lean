/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.InwardStar

@[expose] public section

/-!
# Prescribed-edge half-star addition

Fan's Lemma 3.6. Positive endpoints at every retained hub neighbour and every
missing-spoke leaf allow the prescribed edge to be restored first. Thereafter
at most one passing neighbour exists, so the inward-subset bound restores at
least half the original missing star. All counts refer to one output witness.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- Restore at least half a missing star inward, including any prescribed
spoke. Positivity covers the entire final hub neighbourhood, not just S. -/
theorem prescribed_half_star_addibility (D : Decomposition G) (a : V) (S : Finset V)
    (ha : a ∉ S) (hmissing : ∀ b ∈ S, ¬ G.Adj a b)
    (hpositive : ∀ v, G.Adj a v ∨ v ∈ S → 0 < D.endpointCount v)
    (b : V) (hb : b ∈ S) :
    ∃ B : Finset V, B ⊆ S ∧ b ∈ B ∧ #S ≤ 2 * #B ∧
      ∃ E : Decomposition (G ⊔ B.sup (SimpleGraph.edge a)), E.size = D.size ∧
        ∀ v, E.endpointCount v + (if v ∈ B then 1 else 0) =
          D.endpointCount v + if a = v then #B else 0 := by
  classical
  have hzero : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hadj, hz⟩ := Finset.mem_filter.mp hv
    have hp := hpositive v (Or.inl ((G.mem_neighborFinset a v).mp hadj))
    omega
  have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
  obtain ⟨E, hsize, hend⟩ := D.single_edge_addibility a b hab (hmissing b hb)
    (by rw [hzero]; exact hpositive b (Or.inr hb))
  have hrem : ∀ c ∈ S.erase b, ¬ (G ⊔ SimpleGraph.edge a b).Adj a c := by
    intro c hc h
    obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
    rcases h with h | h
    · exact hmissing c hcS h
    · rw [SimpleGraph.edge_adj] at h
      rcases h.1 with h | h
      · exact hcb h.2
      · exact hab h.1
  have hpos : ∀ c ∈ S.erase b, 0 < E.endpointCount c := by
    intro c hc
    obtain ⟨hcb, hcS⟩ := Finset.mem_erase.mp hc
    have hac : a ≠ c := fun h => ha (h.symm ▸ hcS)
    have he := hend c
    simp only [Ne.symm hcb, hac, if_false, Nat.add_zero] at he
    rw [he]
    exact hpositive c (Or.inr hcS)
  obtain ⟨A, hAS, hcount, Q, hQsize, hQend⟩ :=
    E.inward_star_addibility a (S.erase b)
      (fun h => ha (Finset.mem_of_mem_erase h)) hrem hpos
  have hbA : b ∉ A := fun h => (Finset.mem_erase.mp (hAS h)).1 rfl
  have hcard := Finset.card_erase_add_one hb
  have hpass := D.passing_neighbors_le_add_one a b E hend
  rw [hzero] at hpass
  refine ⟨insert b A, ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · exact Finset.insert_subset hb (fun c hc => Finset.mem_of_mem_erase (hAS hc))
  · rw [Finset.card_insert_of_notMem hbA]
    omega
  · have hgraph : (G ⊔ SimpleGraph.edge a b) ⊔ A.sup (SimpleGraph.edge a) =
        G ⊔ (insert b A).sup (SimpleGraph.edge a) := by
      rw [Finset.sup_insert]
      exact sup_assoc _ _ _
    rw [← hgraph]
    refine ⟨Q, hQsize.trans hsize, ?_⟩
    intro v
    have he := hend v
    have hq := hQend v
    rw [Finset.card_insert_of_notMem hbA]
    by_cases hbv : b = v
    · subst v
      simp only [if_true, hab, hbA, if_false, Finset.mem_insert_self,
        Nat.add_zero] at he hq ⊢
      omega
    · have hvb : v ≠ b := Ne.symm hbv
      simp only [hbv, if_false, Nat.add_zero] at he
      simp only [Finset.mem_insert, hvb, false_or]
      by_cases hav : a = v <;> by_cases hvA : v ∈ A <;>
        simp only [hav, hvA, if_true, if_false, Nat.add_zero] at he hq ⊢ <;> omega

/-- On a missing three-spoke star, prescribed half-star restoration selects at
least two spokes.  The centre is not a leaf, so its endpoint count rises by
exactly the selected cardinality.  This packages the arithmetic used by the
literal length-one corridor schedule. -/
theorem prescribed_three_star_addibility (D : Decomposition G) (a : V) (S : Finset V)
    (ha : a ∉ S) (hcard : #S = 3) (hmissing : ∀ b ∈ S, ¬ G.Adj a b)
    (hpositive : ∀ v, G.Adj a v ∨ v ∈ S → 0 < D.endpointCount v)
    (b : V) (hb : b ∈ S) :
    ∃ B : Finset V, B ⊆ S ∧ b ∈ B ∧ 2 ≤ #B ∧
      ∃ E : Decomposition (G ⊔ B.sup (SimpleGraph.edge a)), E.size = D.size ∧
        E.endpointCount a = D.endpointCount a + #B ∧
        ∀ v, E.endpointCount v + (if v ∈ B then 1 else 0) =
          D.endpointCount v + if a = v then #B else 0 := by
  obtain ⟨B, hBS, hbB, hhalf, E, hsize, hend⟩ :=
    D.prescribed_half_star_addibility a S ha hmissing hpositive b hb
  have hcardB : 2 ≤ #B := by omega
  have haB : a ∉ B := fun haB => ha (hBS haB)
  have hcentre := hend a
  simp [haB] at hcentre
  exact ⟨B, hBS, hbB, hcardB, E, hsize, hcentre, hend⟩

/-- The endpoint equation of a selected three-star gives the strict surplus
needed by the final pending-spoke restoration: one pre-existing centre end
plus two selected spokes yields at least three centre endpoints. -/
theorem prescribed_three_star_center_endpoints_ge_three
    {G₁ G₂ : SimpleGraph V} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (D : Decomposition G₁) (E : Decomposition G₂) (a : V) (B : Finset V)
    (hD : 1 ≤ D.endpointCount a) (hB : 2 ≤ #B)
    (hcentre : E.endpointCount a = D.endpointCount a + #B) :
    3 ≤ E.endpointCount a := by
  rw [hcentre]
  omega

/-- A selected subset of a three-spoke star with at least two spokes is either
the whole star or leaves exactly one pending spoke.  This separates the
no-final-restoration branch from the unique-pending-leaf branch. -/
theorem three_star_selected_all_or_single_pending (S B : Finset V)
    (hsub : B ⊆ S) (hcard : #S = 3) (hBcard : 2 ≤ #B) :
    B = S ∨ ∃ w, S \ B = {w} := by
  by_cases hBS : B = S
  · exact Or.inl hBS
  · right
    have hlt : #B < #S :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hBS⟩)
    have hBtwo : #B = 2 := by omega
    have hdiff : #(S \ B) = 1 := by
      rw [Finset.card_sdiff_of_subset hsub]
      omega
    exact Finset.card_eq_one.mp hdiff

/-- A prescribed selected subset of the literal three-spoke set has only the
three branches used by the corridor restoration: all three spokes, or the
hub spoke together with exactly one of the two non-hub spokes. -/
theorem literal_three_star_selected_cases (B : Finset V) (x q r : V)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (hsub : B ⊆ ({x, q, r} : Finset V)) (hxB : x ∈ B) (hBcard : 2 ≤ #B) :
    B = ({x, q, r} : Finset V) ∨
      B = ({x, q} : Finset V) ∨ B = ({x, r} : Finset V) := by
  have hS : #({x, q, r} : Finset V) = 3 := by
    simp [hxq, hxr, hqr]
  rcases three_star_selected_all_or_single_pending ({x, q, r} : Finset V) B
      hsub hS hBcard with hfull | ⟨w, hdiff⟩
  · exact Or.inl hfull
  · have hwS : w ∈ ({x, q, r} : Finset V) := by
      have hwDiff : w ∈ ({x, q, r} : Finset V) \ B := by
        rw [hdiff]
        simp
      exact (Finset.mem_sdiff.mp hwDiff).1
    have hwnB : w ∉ B := by
      have hwDiff : w ∈ ({x, q, r} : Finset V) \ B := by
        rw [hdiff]
        simp
      exact (Finset.mem_sdiff.mp hwDiff).2
    have hwx : w ≠ x := fun h => hwnB (h ▸ hxB)
    rcases (by simpa using hwS : w = x ∨ w = q ∨ w = r) with hw | hw | hw
    · exact (hwx hw).elim
    · right; right
      subst w
      apply Finset.ext
      intro v
      constructor
      · intro hv
        have hvS := hsub hv
        rcases (by simpa using hvS : v = x ∨ v = q ∨ v = r) with hvx | hvq | hvr
        · simp [hvx]
        · exfalso
          have hqDiff : q ∈ ({x, q, r} : Finset V) \ B := by
            rw [hdiff]
            simp
          exact (Finset.mem_sdiff.mp hqDiff).2 (hvq ▸ hv)
        · simp [hvr]
      · intro hv
        rcases (by simpa using hv : v = x ∨ v = r) with hvx | hvr
        · simpa [hvx] using hxB
        · subst v
          by_contra hrB
          have : r ∈ ({x, q, r} : Finset V) \ B :=
            Finset.mem_sdiff.mpr ⟨by simp, hrB⟩
          rw [hdiff] at this
          have hrq : r = q := by simpa using this
          exact hqr hrq.symm
    · right; left
      subst w
      apply Finset.ext
      intro v
      constructor
      · intro hv
        have hvS := hsub hv
        rcases (by simpa using hvS : v = x ∨ v = q ∨ v = r) with hvx | hvq | hvr
        · simp [hvx]
        · simp [hvq]
        · exfalso
          have hrDiff : r ∈ ({x, q, r} : Finset V) \ B := by
            rw [hdiff]
            simp
          exact (Finset.mem_sdiff.mp hrDiff).2 (hvr ▸ hv)
      · intro hv
        rcases (by simpa using hv : v = x ∨ v = q) with hvx | hvq
        · simpa [hvx] using hxB
        · subst v
          by_contra hqB
          have : q ∈ ({x, q, r} : Finset V) \ B :=
            Finset.mem_sdiff.mpr ⟨by simp, hqB⟩
          rw [hdiff] at this
          exact hqr (by simpa using this)

end Gallai.Decomposition
