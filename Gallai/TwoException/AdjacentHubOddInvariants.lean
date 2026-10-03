/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentHubOddAux
public import Gallai.TwoException.AdjacentCut
public import Gallai.TwoException.AdjacentHubCut

@[expose] public section

/-! # Pendant cap transport for Xie's odd/odd hub-cut branch

In the odd/odd hub-cut branch the shared hub is odd on a cut piece, but even
in the original graph.  Attaching a fresh pendant edge makes it even in the
auxiliary.  Consequently, the ordinary `pendantExtension_cap` lemma is not
the right interface: it compares to the cut piece, where the hub was not an
even neighbour.  The lemma below compares directly to the original one-vertex
union, where the hub is even.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {A B : SimpleGraph V} [DecidableRel A.Adj] [DecidableRel B.Adj]

/-- A pendant edge at an old vertex preserves connectedness.  This is stated
on the connected one-leaf auxiliary itself; after transport to the common
two-leaf carrier space, the unused leaf is isolated. -/
theorem pendantExtension_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (hconn : G.Connected) : (pendantExtension G h).Connected := by
  let f : G →g pendantExtension G h :=
    (SimpleGraph.Hom.ofLE le_sup_left).comp
      (SimpleGraph.Embedding.map (Function.Embedding.inl : V ↪ V ⊕ Unit) G)
  have hnew : (pendantExtension G h).Reachable (.inr ()) (.inl h) :=
    ((pendantExtension_adj_new G h (.inl h)).mpr rfl).reachable
  apply SimpleGraph.Connected.mk
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact (hconn.preconnected a b).map f
    | inr u =>
      cases u
      exact ((hconn.preconnected a h).map f).trans hnew.symm
  | inr u =>
    cases u
    cases b with
    | inl b =>
      exact hnew.trans ((hconn.preconnected h b).map f)
    | inr u =>
      cases u
      exact SimpleGraph.Reachable.refl _

/-- A pendant extension of an odd local hub inherits the global subcubic
E-degree cap away from the newly even hub and a second named exception. -/
theorem pendantExtension_cap_of_one_vertex_union
    (h y : V)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hh : Even ((A ⊔ B).degree h))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    ∀ v, Even ((pendantExtension A h).degree v) →
      v ≠ (.inl h : V ⊕ Unit) → v ≠ .inl y →
      eDegree (pendantExtension A h) v ≤ 3 := by
  intro v hv hvh hvy
  cases v with
  | inr u =>
    cases u
    exact False.elim ((Nat.not_even_iff_odd.mpr
      (pendantExtension_odd_new A h)) hv)
  | inl v =>
    have hvh' : v ≠ h := by
      intro e
      exact hvh (by simpa [e])
    have hvy' : v ≠ y := by
      intro e
      exact hvy (by simpa [e])
    have hvA : Even (A.degree v) :=
      (pendantExtension_even_old_ne A h v hvh').mp hv
    by_cases hp : ∃ w, A.Adj v w
    · obtain ⟨w, hvw⟩ := hp
      have hBiso : ∀ q, ¬ B.Adj v q := by
        intro q hvq
        exact hvh' (hmeet v ⟨w, hvw⟩ ⟨q, hvq⟩)
      have hzero : B.neighborFinset v = ∅ := by
        ext q
        simp [hBiso q]
      have hdeg : (A ⊔ B).degree v = A.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,
          SimpleGraph.neighborFinset_sup, hzero]
        simp
      have hvG : Even ((A ⊔ B).degree v) := by
        rw [hdeg]
        exact hvA
      have hsubset : evenNeighbors (pendantExtension A h) (.inl v) ⊆
          (evenNeighbors (A ⊔ B) v).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
        intro w hw
        obtain ⟨hvw', hwEven⟩ :=
          (mem_evenNeighbors (G := pendantExtension A h) (.inl v) w).mp hw
        cases w with
        | inr u =>
          cases u
          exact False.elim ((Nat.not_even_iff_odd.mpr
            (pendantExtension_odd_new A h)) hwEven)
        | inl w =>
          have hwAdj : A.Adj v w :=
            (pendantExtension_adj_old A h v w).mp hvw'
          by_cases hwh : w = h
          · subst w
            exact Finset.mem_map.mpr ⟨h,
              (mem_evenNeighbors (G := A ⊔ B) v h).mpr ⟨Or.inl hwAdj, hh⟩, rfl⟩
          · have hwA : Even (A.degree w) :=
              (pendantExtension_even_old_ne A h w hwh).mp hwEven
            exact Finset.mem_map.mpr ⟨w,
              (adjacent_evenNeighbors_subset_left (A := A) (B := B) h v hh hmeet)
                ((mem_evenNeighbors (G := A) v w).mpr ⟨hwAdj, hwA⟩), rfl⟩
      have hle : eDegree (pendantExtension A h) (.inl v) ≤
          eDegree (A ⊔ B) v := by
        change (evenNeighbors (pendantExtension A h) (.inl v)).card ≤
          (evenNeighbors (A ⊔ B) v).card
        rw [← Finset.card_map (Function.Embedding.inl : V ↪ V ⊕ Unit)]
        exact Finset.card_le_card hsubset
      exact hle.trans (hcap v hvG hvh' hvy')
    · have hzero : A.neighborFinset v = ∅ := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
        exact fun hw => hp ⟨w, hw⟩
      have hdeg : A.degree v = 0 := by
        rw [← A.card_neighborFinset_eq_degree, hzero, Finset.card_empty]
      have hdeg' : (pendantExtension A h).degree (.inl v) = 0 := by
        rw [pendantExtension_degree_old_ne A h v hvh', hdeg]
      have hle := eDegree_le_degree (G := pendantExtension A h) (.inl v)
      omega

/-- The source's odd/odd hub-cut repair turns the connected piece containing
the other hub into a valid adjacent two-exception instance before any common
carrier transport.  The attachment makes the locally odd shared hub even;
the other hub is an unchanged old even vertex. -/
theorem adjacentInstance_pendant_of_odd_hub_of_union
    (h y : V) (hconn : A.Connected) (hhy : A.Adj h y) (hneq : h ≠ y)
    (hhOdd : Odd (A.degree h)) (hyEven : Even (A.degree y))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hh : Even ((A ⊔ B).degree h))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    AdjacentInstance (pendantExtension A h) (.inl h) (.inl y) := by
  letI : DecidableRel (pendantExtension A h).Adj :=
    Gallai.instDecidableRelAdjPendantExtension A h
  refine ⟨pendantExtension_connected A h hconn, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun e => hneq (Sum.inl.inj e)
  · exact (pendantExtension_adj_old A h h y).mpr hhy
  · exact (pendantExtension_even_attach_iff A h).mpr hhOdd
  · exact (pendantExtension_even_old_ne A h y hneq.symm).mpr hyEven
  · exact pendantExtension_cap_of_one_vertex_union h y hmeet hh hcap

/-- The opposite odd hub-cut piece has no copy of the second exception.  After
attaching its pendant edge, the published one-exception endpoint theorem
therefore applies directly at the newly even shared hub. -/
theorem oneException_pendant_of_odd_hub_of_union
    (h y : V) (hconn : B.Connected) (hneq : h ≠ y)
    (hhOdd : Odd (B.degree h)) (hyabs : ∀ w, ¬ B.Adj y w)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hh : Even ((A ⊔ B).degree h))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    ∃ D : Decomposition (pendantExtension B h),
      D.size ≤ (Fintype.card (V ⊕ Unit) + 1) / 2 ∧
        2 ≤ D.endpointCount (.inl h) := by
  letI : DecidableRel (pendantExtension B h).Adj :=
    Gallai.instDecidableRelAdjPendantExtension B h
  apply one_exception_endpoint (pendantExtension B h) (.inl h)
    (pendantExtension_connected B h hconn)
  · rw [pendantExtension_degree_attach]
    omega
  · exact (pendantExtension_even_attach_iff B h).mpr hhOdd
  · intro v hv hvh
    by_cases hvy : v = (.inl y : V ⊕ Unit)
    · subst v
      have hzero : B.neighborFinset y = ∅ := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
        exact hyabs w
      have hdeg : B.degree y = 0 := by
        rw [← B.card_neighborFinset_eq_degree, hzero, Finset.card_empty]
      have hdeg' : (pendantExtension B h).degree (.inl y) = 0 := by
        rw [pendantExtension_degree_old_ne B h y hneq.symm, hdeg]
      have hle := eDegree_le_degree (G := pendantExtension B h) (.inl y)
      omega
    · have hhBA : Even ((B ⊔ A).degree h) := by
        have hgraph : A ⊔ B = B ⊔ A := by simpa only [sup_comm]
        exact adjacent_even_degree_congr h hgraph hh
      have hcapBA : ∀ q, Even ((B ⊔ A).degree q) → q ≠ h → q ≠ y →
          eDegree (B ⊔ A) q ≤ 3 := by
        simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card', sup_comm] using hcap
      exact pendantExtension_cap_of_one_vertex_union (A := B) (B := A)
        h y (fun w hB hA => hmeet w hA hB) hhBA hcapBA v hv hvh hvy

/-- Source-facing readiness bundle for Xie's odd/odd hub-cut branch.  The
piece containing `y` becomes an adjacent two-exception instance after its
pendant attachment; the opposite connected piece has no copy of `y`, and its
pendant attachment therefore admits the one-exception endpoint decomposition.
The odd parity of the second cut-side hub degree is derived from the literal
one-vertex union rather than assumed separately. -/
theorem adjacent_hub_odd_cut_pendant_invariants
    (h y : V) (hconnA : A.Connected) (hconnB : B.Connected)
    (hhy : A.Adj h y) (hneq : h ≠ y)
    (hhOddA : Odd (A.degree h))
    (hyEven : Even (A.degree y))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hh : Even ((A ⊔ B).degree h))
    (hcap : ∀ v, Even ((A ⊔ B).degree v) → v ≠ h → v ≠ y →
      eDegree (A ⊔ B) v ≤ 3) :
    AdjacentInstance (pendantExtension A h) (.inl h) (.inl y) ∧
      ∃ D : Decomposition (pendantExtension B h),
        D.size ≤ (Fintype.card (V ⊕ Unit) + 1) / 2 ∧
          2 ≤ D.endpointCount (.inl h) := by
  have hhOddB : Odd (B.degree h) :=
    hub_cut_odd_right_of_total_even h hmeet hh hhOddA
  have hyabs : ∀ w, ¬ B.Adj y w := by
    intro w hyw
    have hyh : y = h := hmeet y ⟨h, hhy.symm⟩ ⟨w, hyw⟩
    exact hneq hyh.symm
  refine ⟨?_, ?_⟩
  · exact adjacentInstance_pendant_of_odd_hub_of_union h y hconnA hhy hneq
      hhOddA hyEven hmeet hh hcap
  · exact oneException_pendant_of_odd_hub_of_union h y hconnB hneq hhOddB
      hyabs hmeet hh hcap

end Gallai.TwoException
