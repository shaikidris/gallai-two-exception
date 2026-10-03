/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.AdjacentCut
public import Gallai.TwoException.AdjacentHubOddNative
public import Gallai.TwoException.AdjacentHubOddSplice
public import Gallai.TwoException.AdjacentHubOddSingleton

@[expose] public section

/-! # Lifting returned odd/odd hub-cut pendant carriers

The recursive auxiliary in Xie's odd/odd hub-cut branch lives on the native
subtype of a cut side.  A pendant edge is returned on that native type before
the resulting decomposition is lifted to the ambient spanning cut piece.
This file isolates that transport, without selecting a source cut or proving
any global budget.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Returning a non-singleton pendant carrier on a native cut side and then
lifting it preserves its three-endpoint hub reserve in the ambient piece. -/
theorem return_lift_non_singleton_pendant_reserve
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (h : V) (hhS : h ∈ S)
    (hsupport : H.support ⊆ S)
    (D : Decomposition (pendantExtension (H.induce S) ⟨h, hhS⟩))
    (i : Fin D.size)
    (he : s((.inr () : S ⊕ Unit), .inl ⟨h, hhS⟩) ∈ (D.path i).walk.edges)
    (hnew : (D.path i).start = (.inr () : S ⊕ Unit) ∨
      (D.path i).finish = (.inr () : S ⊕ Unit))
    (hold : ¬ ((D.path i).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path i).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit)))
    (hreserve : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩)) :
    ∃ E : Decomposition H, E.size ≤ D.size ∧ 3 ≤ E.endpointCount h := by
  obtain ⟨D', hsD', hrD'⟩ := return_terminal_pendant_non_singleton_reserve
    (H.induce S) ⟨h, hhS⟩ D i he hnew hold hreserve
  obtain ⟨E, hsE, heE⟩ := adjacent_lift_cut_piece S hsupport D'
  refine ⟨E, ?_, ?_⟩
  · omega
  · rw [heE ⟨h, hhS⟩]
    exact hrD'

/-- Returning a singleton pendant carrier on a native cut side and then
lifting it saves one carrier while preserving a positive ambient hub endpoint. -/
theorem return_lift_singleton_pendant_saves_one
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] (h : V) (hhS : h ∈ S)
    (hsupport : H.support ⊆ S)
    (D : Decomposition (pendantExtension (H.induce S) ⟨h, hhS⟩))
    (i : Fin D.size)
    (he : s((.inr () : S ⊕ Unit), .inl ⟨h, hhS⟩) ∈ (D.path i).walk.edges)
    (hnew : (D.path i).start = (.inr () : S ⊕ Unit) ∨
      (D.path i).finish = (.inr () : S ⊕ Unit))
    (hold : (D.path i).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path i).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit))
    (hreserve : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩)) :
    ∃ E : Decomposition H, E.size + 1 = D.size ∧ 0 < E.endpointCount h := by
  obtain ⟨D', hsD', hpD'⟩ := return_terminal_pendant_singleton_saves_one
    (H.induce S) ⟨h, hhS⟩ D i he hnew hold hreserve
  obtain ⟨E, hsE, heE⟩ := adjacent_lift_cut_piece S hsupport D'
  refine ⟨E, ?_, ?_⟩
  · omega
  · rw [heE ⟨h, hhS⟩]
    exact hpD'

/-- The source's neither-singleton reconstruction after native return and
ambient lift. Two cross-side joins save two carriers in the common cut graph. -/
theorem assemble_non_singleton_native_pendants
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : S ⊕ Unit), .inl ⟨h, hhS⟩) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : T ⊕ Unit), .inl ⟨h, hhT⟩) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : S ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : S ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : T ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : T ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path iD).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit)))
    (holdE : ¬ ((E.path iE).start = (.inl ⟨h, hhT⟩ : T ⊕ Unit) ∨
      (E.path iE).finish = (.inl ⟨h, hhT⟩ : T ⊕ Unit)))
    (hD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩))
    (hE : 2 ≤ E.endpointCount (.inl ⟨h, hhT⟩))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD', hrD'⟩ := return_lift_non_singleton_pendant_reserve
    A S h hhS hAsupport D iD heD hnewD holdD hD
  obtain ⟨E', hsE', hrE'⟩ := return_lift_non_singleton_pendant_reserve
    B T h hhT hBsupport E iE heE hnewE holdE hE
  obtain ⟨F, hsF, hhF⟩ := double_merge_hub_reserve A B h D' E' hrD' hrE' hmeet
  refine ⟨F, ?_, hhF⟩
  omega

/-- Two pieces meeting only at `h` have edge-disjoint edge sets. -/
theorem disjoint_edgeSet_of_one_vertex_meet
    (A B : SimpleGraph V) (h : V)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h) :
    Disjoint A.edgeSet B.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e
  induction e using Sym2.inductionOn with
  | hf a b =>
    intro hA hB
    have ha : A.Adj a b := hA
    have hb : B.Adj a b := hB
    exact ha.ne ((hmeet a ⟨b, ha⟩ ⟨b, hb⟩).trans
      (hmeet b ⟨a, ha.symm⟩ ⟨a, hb.symm⟩).symm)

/-- The source's mixed terminality reconstruction after native return and
ambient lift. The singleton deletion and one cross-side merge save two
carriers in total. -/
theorem assemble_mixed_native_pendants
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : S ⊕ Unit), .inl ⟨h, hhS⟩) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : T ⊕ Unit), .inl ⟨h, hhT⟩) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : S ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : S ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : T ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : T ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path iD).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit)))
    (holdE : (E.path iE).start = (.inl ⟨h, hhT⟩ : T ⊕ Unit) ∨
      (E.path iE).finish = (.inl ⟨h, hhT⟩ : T ⊕ Unit))
    (hD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩))
    (hE : 2 ≤ E.endpointCount (.inl ⟨h, hhT⟩))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD', hrD'⟩ := return_lift_non_singleton_pendant_reserve
    A S h hhS hAsupport D iD heD hnewD holdD hD
  obtain ⟨E', hsE', hpE'⟩ := return_lift_singleton_pendant_saves_one
    B T h hhT hBsupport E iE heE hnewE holdE hE
  obtain ⟨F, hsF, heF⟩ := D'.single_merge_endpoints E' h (by omega) hpE' hmeet
  have hhub : F.endpointCount h + 2 = D'.endpointCount h + E'.endpointCount h := by
    simpa using heF h
  refine ⟨F, ?_, ?_⟩
  · omega
  · omega

/-- The source's both-singleton reconstruction after native return and
ambient lift. The two erased singleton carriers provide the two savings. -/
theorem assemble_singleton_native_pendants
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : S ⊕ Unit), .inl ⟨h, hhS⟩) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : T ⊕ Unit), .inl ⟨h, hhT⟩) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : S ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : S ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : T ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : T ⊕ Unit))
    (holdD : (D.path iD).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path iD).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit))
    (holdE : (E.path iE).start = (.inl ⟨h, hhT⟩ : T ⊕ Unit) ∨
      (E.path iE).finish = (.inl ⟨h, hhT⟩ : T ⊕ Unit))
    (hD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩))
    (hE : 2 ≤ E.endpointCount (.inl ⟨h, hhT⟩))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD', hpD'⟩ := return_lift_singleton_pendant_saves_one
    A S h hhS hAsupport D iD heD hnewD holdD hD
  obtain ⟨E', hsE', hpE'⟩ := return_lift_singleton_pendant_saves_one
    B T h hhT hBsupport E iE heE hnewE holdE hE
  obtain ⟨F, hsF, heF⟩ := D'.union_disjoint_endpoints E'
    (disjoint_edgeSet_of_one_vertex_meet A B h hmeet)
  have hhub : F.endpointCount h = D'.endpointCount h + E'.endpointCount h := heF h
  refine ⟨F, ?_, ?_⟩
  · omega
  · omega

/-- Given the two native pendant auxiliary decompositions on a one-vertex cut,
select their terminal pendant carriers and reconstruct the ambient cut graph
within its ceiling budget. This is independent of the mechanism which supplies
the two auxiliary decompositions. -/
theorem assemble_native_pendants_at_ceiling
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h : V) (hhS : h ∈ S) (hhT : h ∈ T)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩))
    (hDsize : D.size ≤ (Fintype.card (S ⊕ Unit) + 1) / 2)
    (hEsize : E.size ≤ (Fintype.card (T ⊕ Unit) + 1) / 2)
    (hD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩))
    (hE : 2 ≤ E.endpointCount (.inl ⟨h, hhT⟩)) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨iD, heD, hnewD⟩ :=
    D.exists_terminal_pendant_carrier (A.induce S) ⟨h, hhS⟩
  obtain ⟨iE, heE, hnewE⟩ :=
    E.exists_terminal_pendant_carrier (B.induce T) ⟨h, hhT⟩
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w hAw hBw
    rcases hAw with ⟨a, ha⟩
    rcases hBw with ⟨b, hb⟩
    have hwS : w ∈ S := hAsupport ⟨a, ha⟩
    have hwT : w ∈ T := hBsupport ⟨b, hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using (show w ∈ S ∩ T from ⟨hwS, hwT⟩)
  have hcard := card_cover_single_inter S T h hcover hinter
  have hDcard : Fintype.card (S ⊕ Unit) = Fintype.card S + 1 := by simp
  have hEcard : Fintype.card (T ⊕ Unit) = Fintype.card T + 1 := by simp
  have hDsize' : D.size ≤ Fintype.card S / 2 + 1 := by omega
  have hEsize' : E.size ≤ Fintype.card T / 2 + 1 := by omega
  have finish (F : Decomposition (A ⊔ B))
      (hsF : F.size ≤ D.size + E.size - 2) (hhF : 2 ≤ F.endpointCount h) :
      ∃ R : Decomposition (A ⊔ B),
        R.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ R.endpointCount h := by
    refine ⟨F, ?_, hhF⟩
    omega
  by_cases holdD : (D.path iD).start = (.inl ⟨h, hhS⟩ : S ⊕ Unit) ∨
      (D.path iD).finish = (.inl ⟨h, hhS⟩ : S ⊕ Unit)
  · by_cases holdE : (E.path iE).start = (.inl ⟨h, hhT⟩ : T ⊕ Unit) ∨
        (E.path iE).finish = (.inl ⟨h, hhT⟩ : T ⊕ Unit)
    · obtain ⟨F, hsF, hhF⟩ := assemble_singleton_native_pendants
        A B S T h hhS hhT hAsupport hBsupport D E iD iE heD heE hnewD hnewE
        holdD holdE hD hE hmeet
      exact finish F hsF hhF
    · obtain ⟨F0, hsF0, hhF0⟩ := assemble_mixed_native_pendants
        B A T S h hhT hhS hBsupport hAsupport E D iE iD heE heD hnewE hnewD
        holdE holdD hE hD (fun w hBw hAw => hmeet w hAw hBw)
      let e : B ⊔ A = A ⊔ B := by simp only [sup_comm]
      let F : Decomposition (A ⊔ B) := e ▸ F0
      have castSize {L M : SimpleGraph V} (e : L = M)
          (P : Decomposition L) : (e ▸ P).size = P.size := by
        subst M
        rfl
      have castEnds {L M : SimpleGraph V} (e : L = M)
          (P : Decomposition L) (v : V) :
          (e ▸ P).endpointCount v = P.endpointCount v := by
        subst M
        rfl
      have hsF : F.size = F0.size := castSize e F0
      have hhF : F.endpointCount h = F0.endpointCount h := castEnds e F0 h
      apply finish F
      · rw [hsF]
        omega
      · rw [hhF]
        exact hhF0
  · by_cases holdE : (E.path iE).start = (.inl ⟨h, hhT⟩ : T ⊕ Unit) ∨
        (E.path iE).finish = (.inl ⟨h, hhT⟩ : T ⊕ Unit)
    · obtain ⟨F, hsF, hhF⟩ := assemble_mixed_native_pendants
        A B S T h hhS hhT hAsupport hBsupport D E iD iE heD heE hnewD hnewE
        holdD holdE hD hE hmeet
      exact finish F hsF hhF
    · obtain ⟨F, hsF, hhF⟩ := assemble_non_singleton_native_pendants
        A B S T h hhS hhT hAsupport hBsupport D E iD iE heD heE hnewD hnewE
        holdD holdE hD hE hmeet
      exact finish F hsF hhF

/-- The shared-hub endpoint output in Xie's non-singleton odd/odd cut branch.
The two native recursive consumers provide pendant auxiliary decompositions;
the checked carrier assembler returns a ceiling-budget decomposition of the
original graph exposing the shared hub twice. -/
theorem adjacent_native_odd_cut_hub_output
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hcover : S ∪ T = Set.univ)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card) :
    ∃ F : Decomposition G,
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount h := by
  have hhT : h ∈ T := by
    have : h ∈ S ∩ T := by rw [hinter]; simp
    exact this.2
  obtain ⟨D0, hD0size, hD0⟩ :=
    (adjacent_native_odd_cut_non_singleton_conclusion_of_global_y_even
      S T h y M hhS hyS hgraph hSsupport hTsupport hinter hconnS hhOdd hTcount).1
  obtain ⟨E0, hE0size, hE0⟩ :=
    oneException_pendant_induce_opposite_of_one_vertex_union
      S T h y hhS hyS hconnT M.counterexample.1.2.1 hgraph hSsupport hTsupport
      hinter M.counterexample.1.2.2.2.1 hhOdd M.counterexample.1.2.2.2.2.2
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hAS : A.induce S = G.induce S := by simp [A]
  have hBT : B.induce T = G.induce T := by simp [B]
  have hpendAS : pendantExtension (G.induce S) ⟨h, hhS⟩ =
      pendantExtension (A.induce S) ⟨h, hhS⟩ :=
    congrArg (fun K => pendantExtension K ⟨h, hhS⟩) hAS.symm
  have hpendBT : pendantExtension (G.induce T) ⟨h, hhT⟩ =
      pendantExtension (B.induce T) ⟨h, hhT⟩ :=
    congrArg (fun K => pendantExtension K ⟨h, hhT⟩) hBT.symm
  let D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩) :=
    hpendAS ▸ D0
  let E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩) :=
    hpendBT ▸ E0
  have castSizeS {L M : SimpleGraph (S ⊕ Unit)} (q : L = M)
      (P : Decomposition L) : (q ▸ P).size = P.size := by
    subst M
    rfl
  have castEndsS {L M : SimpleGraph (S ⊕ Unit)} (q : L = M)
      (P : Decomposition L) (v : S ⊕ Unit) :
      (q ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have castSizeT {L M : SimpleGraph (T ⊕ Unit)} (q : L = M)
      (P : Decomposition L) : (q ▸ P).size = P.size := by
    subst M
    rfl
  have castEndsT {L M : SimpleGraph (T ⊕ Unit)} (q : L = M)
      (P : Decomposition L) (v : T ⊕ Unit) :
      (q ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hDsize : D.size ≤ (Fintype.card (S ⊕ Unit) + 1) / 2 := by
    rw [show D.size = D0.size by exact castSizeS hpendAS D0]
    exact hD0size
  have hEsize : E.size ≤ (Fintype.card (T ⊕ Unit) + 1) / 2 := by
    rw [show E.size = E0.size by exact castSizeT hpendBT E0]
    exact hE0size
  have hD : 2 ≤ D.endpointCount (.inl ⟨h, hhS⟩) := by
    rw [show D.endpointCount (.inl ⟨h, hhS⟩) =
      D0.endpointCount (.inl ⟨h, hhS⟩) by exact castEndsS hpendAS D0 _]
    exact hD0
  have hE : 2 ≤ E.endpointCount (.inl ⟨h, hhT⟩) := by
    rw [show E.endpointCount (.inl ⟨h, hhT⟩) =
      E0.endpointCount (.inl ⟨h, hhT⟩) by exact castEndsT hpendBT E0 _]
    exact hE0
  obtain ⟨F0, hF0size, hF0⟩ := assemble_native_pendants_at_ceiling
    A B S T h hhS hhT (by simpa [A] using hSsupport) (by simpa [B] using hTsupport)
    hcover hinter D E hDsize hEsize hD hE
  let e : A ⊔ B = G := by simpa [A, B] using hgraph
  let F : Decomposition G := e ▸ F0
  have castSize {L M : SimpleGraph V} (q : L = M)
      (P : Decomposition L) : (q ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph V} (q : L = M)
      (P : Decomposition L) (v : V) : (q ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  refine ⟨F, ?_, ?_⟩
  · rw [show F.size = F0.size by exact castSize e F0]
    exact hF0size
  · rw [show F.endpointCount h = F0.endpointCount h by exact castEnds e F0 h]
    exact hF0

/-- The complementary one-merge interface for Xie's odd/odd hub-cut branch.
Unlike the native-pendant reconstruction used for the shared hub, this keeps a
prescribed endpoint reserve on the left cut piece while a terminal carrier at
the separator is supplied by each piece.  It is intentionally independent of
how the two component decompositions are obtained. -/
theorem adjacent_odd_cut_other_endpoint_output
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (h y : V) (hyh : y ≠ h)
    (D : Decomposition A) (E : Decomposition B)
    (hD : 0 < D.endpointCount h) (hE : 0 < E.endpointCount h)
    (hyD : 2 ≤ D.endpointCount y)
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hbudget : D.size + E.size - 1 ≤ (Fintype.card V + 1) / 2) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount y := by
  obtain ⟨F, hsF, heF⟩ := D.single_merge_endpoints E h hD hE hmeet
  refine ⟨F, ?_, ?_⟩
  · omega
  · have hy := heF y
    simp only [hyh.symm, if_false, mul_zero, Nat.add_zero] at hy
    omega

/-- Returning the fresh pendant edge from the nonshared-endpoint output
preserves that endpoint reserve.  The old attachment is odd after return, so
endpoint parity supplies the terminal carrier required for the subsequent
cross-cut merge. -/
theorem return_pendant_preserves_other_endpoint_and_odd_hub
    (A : SimpleGraph V) [DecidableRel A.Adj] (h y : V) (hyh : y ≠ h)
    (D : Decomposition (pendantExtension A h))
    (hhOdd : Odd (A.degree h))
    (hyD : 2 ≤ D.endpointCount (.inl y)) :
    ∃ E : Decomposition A,
      E.size ≤ D.size ∧ 0 < E.endpointCount h ∧ 2 ≤ E.endpointCount y := by
  obtain ⟨i, he, hnew⟩ := D.exists_terminal_pendant_carrier A h
  obtain ⟨E, hsE, _, hother⟩ := D.return_terminal_pendant A h i he hnew
  refine ⟨E, hsE, E.endpointCount_pos_of_odd_degree h hhOdd, ?_⟩
  rw [hother y hyh]
  exact hyD

/-- The nonshared-endpoint pendant return also survives the native-to-ambient
cut-piece lift.  This is the exact left-hand input needed by Xie's one-merge
other-endpoint reconstruction: the old attachment has a terminal carrier by
odd parity, while the prescribed reserve is unchanged. -/
theorem return_lift_pendant_preserves_other_endpoint_and_odd_hub
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    (h y : V) (hhS : h ∈ S) (hyS : y ∈ S) (hyh : y ≠ h)
    (hsupport : H.support ⊆ S)
    (D : Decomposition (pendantExtension (H.induce S) ⟨h, hhS⟩))
    (hhOdd : Odd ((H.induce S).degree ⟨h, hhS⟩))
    (hyD : 2 ≤ D.endpointCount (.inl ⟨y, hyS⟩)) :
    ∃ E : Decomposition H,
      E.size ≤ D.size ∧ 0 < E.endpointCount h ∧ 2 ≤ E.endpointCount y := by
  have hyh' : (⟨y, hyS⟩ : S) ≠ ⟨h, hhS⟩ := by
    intro e
    exact hyh (congrArg Subtype.val e)
  obtain ⟨D', hsD', hhD', hyD'⟩ :=
    return_pendant_preserves_other_endpoint_and_odd_hub
      (H.induce S) ⟨h, hhS⟩ ⟨y, hyS⟩ hyh' D hhOdd hyD
  obtain ⟨E, hsE, hends⟩ := adjacent_lift_cut_piece S hsupport D'
  refine ⟨E, by omega, ?_, ?_⟩
  · rw [hends ⟨h, hhS⟩]
    exact hhD'
  · rw [hends ⟨y, hyS⟩]
    exact hyD'

/-- Returning a fresh pendant from either odd-hub native cut side yields an
ambient decomposition with a usable terminal carrier at the old attachment.
Unlike the shared-hub reconstruction, no terminality case split is needed
when only one cross-side merge is to be made. -/
theorem return_lift_pendant_odd_hub
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Set V) [DecidablePred (· ∈ S)]
    (h : V) (hhS : h ∈ S)
    (hsupport : H.support ⊆ S)
    (D : Decomposition (pendantExtension (H.induce S) ⟨h, hhS⟩))
    (hhOdd : Odd ((H.induce S).degree ⟨h, hhS⟩)) :
    ∃ E : Decomposition H, E.size ≤ D.size ∧ 0 < E.endpointCount h := by
  obtain ⟨i, he, hnew⟩ := D.exists_terminal_pendant_carrier (H.induce S) ⟨h, hhS⟩
  obtain ⟨D', hsD', _, _⟩ :=
    D.return_terminal_pendant (H.induce S) ⟨h, hhS⟩ i he hnew
  obtain ⟨E, hsE, hends⟩ := adjacent_lift_cut_piece S hsupport D'
  refine ⟨E, by omega, ?_⟩
  rw [hends ⟨h, hhS⟩]
  exact D'.endpointCount_pos_of_odd_degree ⟨h, hhS⟩ hhOdd

/-- The complete carrier assembly for Xie's complementary odd/odd endpoint
output.  Once each pendant auxiliary has been returned and lifted, a single
merge at the shared odd hub saves the required carrier while preserving the
reserve at the other adjacent exception. -/
theorem adjacent_odd_cut_other_endpoint_returned_pendants
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hhS : h ∈ S) (hhT : h ∈ T) (hyS : y ∈ S) (hyh : y ≠ h)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (D : Decomposition (pendantExtension (A.induce S) ⟨h, hhS⟩))
    (E : Decomposition (pendantExtension (B.induce T) ⟨h, hhT⟩))
    (hhOddS : Odd ((A.induce S).degree ⟨h, hhS⟩))
    (hhOddT : Odd ((B.induce T).degree ⟨h, hhT⟩))
    (hyD : 2 ≤ D.endpointCount (.inl ⟨y, hyS⟩))
    (hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h)
    (hbudget : D.size + E.size - 1 ≤ (Fintype.card V + 1) / 2) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount y := by
  obtain ⟨D', hsD', hhD', hyD'⟩ :=
    return_lift_pendant_preserves_other_endpoint_and_odd_hub
      A S h y hhS hyS hyh hAsupport D hhOddS hyD
  obtain ⟨E', hsE', hhE'⟩ :=
    return_lift_pendant_odd_hub B T h hhT hBsupport E hhOddT
  exact adjacent_odd_cut_other_endpoint_output A B h y hyh D' E'
    hhD' hhE' hyD' hmeet (by omega)

/-- The direct (non-pendant) assembly used for the other endpoint in Xie's
odd/odd hub-cut case.  A one-exception decomposition on the side containing
`y` and a floor-or-SET decomposition on the opposite side each expose the
odd shared hub.  Their one merge has exactly the ceiling budget supplied by a
one-vertex cover. -/
theorem adjacent_odd_cut_other_endpoint_at_ceiling
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (hyh : y ≠ h)
    (hAsupport : A.support ⊆ S) (hBsupport : B.support ⊆ T)
    (hcover : S ∪ T = Set.univ) (hinter : S ∩ T = {h})
    (D : Decomposition A) (E : Decomposition B)
    (hDsize : D.size ≤ (Fintype.card S + 1) / 2)
    (hEsize : E.size ≤ (Fintype.card T + 1) / 2)
    (hhD : 0 < D.endpointCount h) (hhE : 0 < E.endpointCount h)
    (hyD : 2 ≤ D.endpointCount y) :
    ∃ F : Decomposition (A ⊔ B),
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount y := by
  have hmeet : ∀ w, (∃ a, A.Adj w a) → (∃ b, B.Adj w b) → w = h := by
    intro w hAw hBw
    rcases hAw with ⟨a, ha⟩
    rcases hBw with ⟨b, hb⟩
    have hwS : w ∈ S := hAsupport ⟨a, ha⟩
    have hwT : w ∈ T := hBsupport ⟨b, hb⟩
    simpa only [hinter, Set.mem_singleton_iff] using
      (show w ∈ S ∩ T from ⟨hwS, hwT⟩)
  have hcard := card_cover_single_inter S T h hcover hinter
  exact adjacent_odd_cut_other_endpoint_output A B h y hyh D E hhD hhE hyD hmeet (by omega)

set_option maxHeartbeats 800000 in
/-- The nonshared endpoint output in Xie's non-singleton odd/odd hub-cut
branch, following the source's direct construction.  The side containing the
other hub receives the one-exception endpoint theorem; the opposite side
receives floor-or-SET; their odd shared-hub carriers are merged after native
decompositions are lifted to the ambient cut pieces. -/
theorem adjacent_native_odd_cut_other_endpoint_output
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hcover : S ∪ T = Set.univ)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩)) :
    ∃ F : Decomposition G,
      F.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ F.endpointCount y := by
  have hhT : h ∈ T := by
    have : h ∈ S ∩ T := by rw [hinter]; simp
    exact this.2
  have hyT : y ∉ T := by
    intro hyT
    have hyh : y = h := by
      simpa only [hinter, Set.mem_singleton_iff] using
        (show y ∈ S ∩ T from ⟨hyS, hyT⟩)
    exact M.counterexample.1.2.1 hyh.symm
  have hyEven : Even ((G.induce S).degree ⟨y, hyS⟩) :=
    induce_even_other_hub_of_one_vertex_union S T h y hyS M.counterexample.1.2.1.symm
      hinter hgraph M.counterexample.1.2.2.2.2.1
  obtain ⟨D0, hD0size, hhD0, hyD0⟩ :=
    oneException_induce_left_other_endpoint_of_odd_hub S T h y hhS hyS
      M.counterexample.1.2.1.symm hconnS M.counterexample.1.2.2.1 hinter hgraph
      hhOdd hyEven M.counterexample.1.2.2.2.2.2
  have hhOddT : Odd ((G.induce T).degree ⟨h, hhT⟩) :=
    induce_odd_shared_hub_other_of_one_vertex_union S T h hhS hhT hgraph
      hSsupport hTsupport hinter M.counterexample.1.2.2.2.1 hhOdd
  obtain ⟨E0, hE0size, hhE0⟩ :=
    floor_or_set_induce_right_endpoint_of_odd_hub S T h y hhT hyT hconnT
      hinter hgraph hhOddT M.counterexample.1.2.2.2.2.2
  let A : SimpleGraph V := (G.induce S).spanningCoe
  let B : SimpleGraph V := (G.induce T).spanningCoe
  have hAS : A.induce S = G.induce S := by simp [A]
  have hBT : B.induce T = G.induce T := by simp [B]
  let D : Decomposition (A.induce S) := hAS.symm ▸ D0
  let E : Decomposition (B.induce T) := hBT.symm ▸ E0
  have castSizeS {L K : SimpleGraph S} (e : L = K) (P : Decomposition L) :
      (e ▸ P).size = P.size := by subst K; rfl
  have castEndsS {L K : SimpleGraph S} (e : L = K) (P : Decomposition L) (v : S) :
      (e ▸ P).endpointCount v = P.endpointCount v := by subst K; rfl
  have castSizeT {L K : SimpleGraph T} (e : L = K) (P : Decomposition L) :
      (e ▸ P).size = P.size := by subst K; rfl
  have castEndsT {L K : SimpleGraph T} (e : L = K) (P : Decomposition L) (v : T) :
      (e ▸ P).endpointCount v = P.endpointCount v := by subst K; rfl
  have hDsize : D.size ≤ (Fintype.card S + 1) / 2 := by
    rw [show D.size = D0.size by exact castSizeS hAS.symm D0]
    exact hD0size
  have hEsize : E.size ≤ (Fintype.card T + 1) / 2 := by
    rw [show E.size = E0.size by exact castSizeT hBT.symm E0]
    exact hE0size
  have hhD : 0 < D.endpointCount ⟨h, hhS⟩ := by
    rw [show D.endpointCount ⟨h, hhS⟩ = D0.endpointCount ⟨h, hhS⟩ by
      exact castEndsS hAS.symm D0 _]
    exact hhD0
  have hyD : 2 ≤ D.endpointCount ⟨y, hyS⟩ := by
    rw [show D.endpointCount ⟨y, hyS⟩ = D0.endpointCount ⟨y, hyS⟩ by
      exact castEndsS hAS.symm D0 _]
    exact hyD0
  have hhE : 0 < E.endpointCount ⟨h, hhT⟩ := by
    rw [show E.endpointCount ⟨h, hhT⟩ = E0.endpointCount ⟨h, hhT⟩ by
      exact castEndsT hBT.symm E0 _]
    exact hhE0
  obtain ⟨D', hsD', hendsD'⟩ :=
    adjacent_lift_cut_piece S (by simpa [A] using hSsupport) D
  obtain ⟨E', hsE', hendsE'⟩ :=
    adjacent_lift_cut_piece T (by simpa [B] using hTsupport) E
  obtain ⟨F0, hF0size, hyF0⟩ := adjacent_odd_cut_other_endpoint_at_ceiling
    A B S T h y M.counterexample.1.2.1.symm
    (by simpa [A] using hSsupport) (by simpa [B] using hTsupport)
    hcover hinter D' E'
    (by omega) (by omega)
    (by rw [hendsD' ⟨h, hhS⟩]; exact hhD)
    (by rw [hendsE' ⟨h, hhT⟩]; exact hhE)
    (by rw [hendsD' ⟨y, hyS⟩]; exact hyD)
  let e : A ⊔ B = G := by simpa [A, B] using hgraph
  let F : Decomposition G := e ▸ F0
  have castSize {L K : SimpleGraph V} (q : L = K) (P : Decomposition L) :
      (q ▸ P).size = P.size := by subst K; rfl
  have castEnds {L K : SimpleGraph V} (q : L = K) (P : Decomposition L) (v : V) :
      (q ▸ P).endpointCount v = P.endpointCount v := by subst K; rfl
  refine ⟨F, ?_, ?_⟩
  · rw [show F.size = F0.size by exact castSize e F0]
    exact hF0size
  · rw [show F.endpointCount y = F0.endpointCount y by exact castEnds e F0 y]
    exact hyF0

/-- The complete non-singleton odd/odd hub-cut contradiction from Xie's
Claim 1, Case 2.2(i).  The shared-hub output uses the paired-pendant return
assembly, while the nonshared output uses the direct one-exception plus
floor-or-SET assembly above. -/
theorem adjacent_hub_odd_cut_pendant_splice
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hcover : S ∪ T = Set.univ)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hSsupport : ((G.induce S).spanningCoe).support ⊆ S)
    (hTsupport : ((G.induce T).spanningCoe).support ⊆ T)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩))
    (hTcount : 2 ≤ (G.induce T).edgeFinset.card) : False := by
  obtain ⟨DX, hsDX, hxDX⟩ := adjacent_native_odd_cut_hub_output
    S T h y M hhS hyS hcover hgraph hSsupport hTsupport hinter hconnS hconnT
    hhOdd hTcount
  obtain ⟨DY, hsDY, hyDY⟩ := adjacent_native_odd_cut_other_endpoint_output
    S T h y M hhS hyS hcover hgraph hSsupport hTsupport hinter hconnS hconnT hhOdd
  apply M.counterexample.2
  exact ⟨⟨DX, hsDX, hxDX⟩, ⟨DY, hsDY, hyDY⟩⟩

/-- A connected induced cut side containing the shared hub and another vertex
has either one edge or at least two.  This is the exact finite split used by
the singleton/non-singleton source dispatcher. -/
theorem induced_connected_edge_count_one_or_two
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (T : Set V) [DecidablePred (· ∈ T)] (h : V) (hhT : h ∈ T)
    (hother : ∃ b ∈ T, b ≠ h) (hconn : (G.induce T).Connected) :
    (G.induce T).edgeFinset.card = 1 ∨ 2 ≤ (G.induce T).edgeFinset.card := by
  classical
  let K : SimpleGraph T := G.induce T
  obtain ⟨b, hbT, hbh⟩ := hother
  letI : Nontrivial T := ⟨⟨h, hhT⟩, ⟨b, hbT⟩,
    fun e => hbh (congrArg Subtype.val e).symm⟩
  have hhdeg : 0 < K.degree ⟨h, hhT⟩ := by
    exact hconn.preconnected.degree_pos_of_nontrivial ⟨h, hhT⟩
  obtain ⟨u, hhu⟩ := (K.degree_pos_iff_exists_adj ⟨h, hhT⟩).mp hhdeg
  have hmem : s(⟨h, hhT⟩, u) ∈ K.edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr hhu
  have hposK : 0 < K.edgeFinset.card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hpos : 0 < (G.induce T).edgeFinset.card := by
    simpa [K] using hposK
  by_cases hone : (G.induce T).edgeFinset.card = 1
  · exact Or.inl hone
  · exact Or.inr (by omega)

/-- The selected odd/odd hub-cut dispatcher has exactly two source cases.  A
one-edge opposite side is the checked singleton reconstruction; otherwise the
at-least-two-edge side is the checked paired-pendant reconstruction.  The
cut-selection theorem remains a separate global obligation. -/
theorem adjacent_hub_odd_cut_selected_dispatch
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (h y : V) (M : AdjacentEdgeMinimalCounterexample G h y)
    (hhS : h ∈ S) (hyS : y ∈ S)
    (hother : ∃ b ∈ T, b ≠ h)
    (hcover : S ∪ T = Set.univ)
    (hgraph : (G.induce S).spanningCoe ⊔ (G.induce T).spanningCoe = G)
    (hinter : S ∩ T = {h})
    (hconnS : (G.induce S).Connected) (hconnT : (G.induce T).Connected)
    (hcore : (G.induce {v | v ∈ S ∧ v ≠ h}).Connected)
    (hhOdd : Odd ((G.induce S).degree ⟨h, hhS⟩)) : False := by
  have hhT : h ∈ T := by
    have hhST : h ∈ S ∩ T := by
      rw [hinter]
      simp
    exact hhST.2
  have hSsupport : ((G.induce S).spanningCoe).support ⊆ S := by
    intro v hv
    rw [SimpleGraph.mem_support] at hv
    obtain ⟨u, huv⟩ := hv
    exact ((spanning_induce_adj_iff G S v u).mp huv).2.1
  have hTsupport : ((G.induce T).spanningCoe).support ⊆ T := by
    intro v hv
    rw [SimpleGraph.mem_support] at hv
    obtain ⟨u, huv⟩ := hv
    exact ((spanning_induce_adj_iff G T v u).mp huv).2.1
  rcases induced_connected_edge_count_one_or_two T h hhT hother hconnT with hsingle | hnon
  · exact singleton_one_edge_not_edge_minimal G h y M S T hhT hother hconnT
      hsingle hcover hinter hgraph hcore
  · exact adjacent_hub_odd_cut_pendant_splice S T h y M hhS hyS hcover hgraph
      hSsupport hTsupport hinter hconnS hconnT hhOdd hnon

/-- In Xie's adjacent minimum-counterexample argument, deletion of the first
hub cannot disconnect the graph.  The checked cut topology supplies the
selected partition; its local hub degree is even or odd, and the two checked
source dispatchers close the respective alternatives. -/
theorem adjacent_hub_delete_connected
    {G : SimpleGraph V} [DecidableRel G.Adj] (x y : V)
    (M : AdjacentEdgeMinimalCounterexample G x y) :
    (G.induce {v | v ≠ x}).Connected := by
  classical
  by_contra hdisc
  have H := M.counterexample.1
  obtain ⟨S, T, instS, instT, hyS, hxS, hxT, hother, hcover, hinter, hgraph,
      hconnS, hconnT, hcore⟩ :=
    adjacent_hub_cut_partition_with_selected_core_of_disconnected x y H.1 H.2.1 hdisc
  letI : DecidablePred (· ∈ S) := instS
  letI : DecidablePred (· ∈ T) := instT
  obtain hEven | hOdd := Nat.even_or_odd ((G.induce S).spanningCoe.degree x)
  · obtain ⟨b, hbT, hbx⟩ := hother
    exact adjacent_hub_even_even_cut_not_edge_minimal S T x y b M hcover hinter
      hxS hyS hxT hbT H.2.1 hbx hgraph hconnS hconnT hEven
  · have hdegree : (G.induce S).spanningCoe.degree (⟨x, hxS⟩ : S) =
        (G.induce S).degree ⟨x, hxS⟩ :=
      degree_spanningCoe (G.induce S) ⟨x, hxS⟩
    rw [hdegree] at hOdd
    exact adjacent_hub_odd_cut_selected_dispatch S T x y M hxS hyS hother
      hcover hgraph hinter hconnS hconnT hcore hOdd

/-- The same hub-cut exclusion holds for the second designated exception by
the checked symmetry of Xie's edge-minimal resource. -/
theorem adjacent_other_hub_delete_connected
    {G : SimpleGraph V} [DecidableRel G.Adj] (x y : V)
    (M : AdjacentEdgeMinimalCounterexample G x y) :
    (G.induce {v | v ≠ y}).Connected := by
  simpa using adjacent_hub_delete_connected y x
    (adjacentEdgeMinimalCounterexample_swap M)

/-- Xie's full Claim 1 for the adjacent source instance: every even vertex is
non-cut in an edge-minimal counterexample.  The three cases are genuinely
different in the source proof: the two designated hubs use the selected
hub-cut reconstructions, while all other even vertices use the ordinary
cut-piece reconstruction. -/
theorem adjacent_even_vertex_noncut_edge
    {G : SimpleGraph V} [DecidableRel G.Adj] (z x y : V)
    (M : AdjacentEdgeMinimalCounterexample G x y)
    (hz : Even (G.degree z)) :
    (G.induce {v | v ≠ z}).Connected := by
  by_cases hzx : z = x
  · subst z
    exact adjacent_hub_delete_connected x y M
  by_cases hzy : z = y
  · subst z
    exact adjacent_other_hub_delete_connected x y M
  exact adjacent_nonhub_even_vertex_noncut_edge G z x y M hz (Ne.symm hzx) (Ne.symm hzy)

end Gallai.TwoException
