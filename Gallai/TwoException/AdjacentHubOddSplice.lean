/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.PendantReturn
public import Gallai.Operations.SingleMerge
public import Gallai.Operations.DoubleMerge

@[expose] public section

/-! # A native splice for the odd/odd hub-cut auxiliaries

When both cut sides carry a fresh pendant at their common hub, each pendant
can be returned to its native cut graph.  A two-endpoint certificate at the
hub is enough to leave a positive endpoint on each returned side; one ordinary
single-vertex merge then saves a carrier.  This is the reconstruction identity
used before any source-specific budget arithmetic or singleton-carrier case
analysis.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Two endpoint-rich pendant auxiliaries over graph pieces meeting only at a
shared hub can be returned and glued.  The output saves one carrier relative
to the two auxiliary decompositions. -/
theorem splice_returned_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ D' : Decomposition G, ∃ E' : Decomposition H,
      ∃ F : Decomposition (G ⊔ H),
        D'.size ≤ D.size ∧ E'.size ≤ E.size ∧
        0 < D'.endpointCount h ∧ 0 < E'.endpointCount h ∧
        F.size + 1 = D'.size + E'.size ∧
        F.size + 1 ≤ D.size + E.size ∧
        ∀ w, F.endpointCount w + 2 * (if h = w then 1 else 0) =
          D'.endpointCount w + E'.endpointCount w := by
  classical
  obtain ⟨D', hsD, iD, hhD, _⟩ := D.return_pendant G h
  obtain ⟨E', hsE, iE, hhE, _⟩ := E.return_pendant H h
  have hpD : 0 < D'.endpointCount h := by
    split_ifs at hhD
    · omega
    · omega
  have hpE : 0 < E'.endpointCount h := by
    split_ifs at hhE
    · omega
    · omega
  obtain ⟨F, hsF, heF⟩ := D'.single_merge_endpoints E' h hpD hpE hmeet
  refine ⟨D', E', F, hsD, hsE, hpD, hpE, hsF, ?_, heF⟩
  omega

/-- Returning a pendant whose carrier is not also terminal at the attachment
increases a two-endpoint hub reserve to three.  This is the exact
non-singleton carrier interface used in the first source splice case. -/
theorem return_terminal_pendant_non_singleton_reserve
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) (i : Fin D.size)
    (he : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path i).walk.edges)
    (hnew : (D.path i).start = (.inr () : V ⊕ Unit) ∨
      (D.path i).finish = (.inr () : V ⊕ Unit))
    (hold : ¬ ((D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit)) )
    (hreserve : 2 ≤ D.endpointCount (.inl h)) :
    ∃ E : Decomposition G, E.size ≤ D.size ∧ 3 ≤ E.endpointCount h := by
  obtain ⟨E, hsE, hhE, _⟩ := D.return_terminal_pendant G h i he hnew
  refine ⟨E, hsE, ?_⟩
  simp only [hold, ↓reduceIte] at hhE
  omega

/-- The source's case in which neither pendant carrier is singleton: each
return leaves three hub endpoints, so one merge still leaves four. -/
theorem splice_non_singleton_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : V ⊕ Unit), .inl h) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : V ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : V ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : V ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : V ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl h : V ⊕ Unit) ∨
      (D.path iD).finish = (.inl h : V ⊕ Unit)))
    (holdE : ¬ ((E.path iE).start = (.inl h : V ⊕ Unit) ∨
      (E.path iE).finish = (.inl h : V ⊕ Unit)))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ D' : Decomposition G, ∃ E' : Decomposition H,
      ∃ F : Decomposition (G ⊔ H),
        D'.size ≤ D.size ∧ E'.size ≤ E.size ∧
        3 ≤ D'.endpointCount h ∧ 3 ≤ E'.endpointCount h ∧
        F.size + 1 = D'.size + E'.size ∧
        F.size + 1 ≤ D.size + E.size ∧ 4 ≤ F.endpointCount h := by
  obtain ⟨D', hsD, hrD⟩ := return_terminal_pendant_non_singleton_reserve
    G h D iD heD hnewD holdD hD
  obtain ⟨E', hsE, hrE⟩ := return_terminal_pendant_non_singleton_reserve
    H h E iE heE hnewE holdE hE
  obtain ⟨F, hsF, heF⟩ := D'.single_merge_endpoints E' h (by omega) (by omega) hmeet
  have hsize : F.size + 1 ≤ D.size + E.size := by
    omega
  have hhub : F.endpointCount h + 2 = D'.endpointCount h + E'.endpointCount h := by
    simpa using heF h
  refine ⟨D', E', F, hsD, hsE, hrD, hrE, hsF, hsize, ?_⟩
  omega

/-- Returning a pendant carried by the single edge from its fresh leaf to the
hub removes one carrier and leaves a positive hub endpoint. -/
theorem return_terminal_pendant_singleton_saves_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) (i : Fin D.size)
    (he : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path i).walk.edges)
    (hnew : (D.path i).start = (.inr () : V ⊕ Unit) ∨
      (D.path i).finish = (.inr () : V ⊕ Unit))
    (hold : (D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit))
    (hreserve : 2 ≤ D.endpointCount (.inl h)) :
    ∃ E : Decomposition G,
      E.size + 1 = D.size ∧ 0 < E.endpointCount h := by
  obtain ⟨R, hsR, _, hhR, _⟩ :=
    D.exists_delete_terminal i (.inr ()) (.inl h) he hnew
  have hedge : s((.inr () : V ⊕ Unit), .inl h) =
      s((.inl h : V ⊕ Unit), .inr ()) := Sym2.eq_swap
  have hgraph : (pendantExtension G h).deleteEdges
      {s((.inr () : V ⊕ Unit), .inl h)} =
      G.map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
    rw [hedge, pendantExtension_delete_pendant]
  let R' : Decomposition (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)) :=
    hgraph ▸ R
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) (v : V ⊕ Unit) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  have hsR' : R'.size + 1 = D.size := by
    have hcast : R'.size = R.size := castSize hgraph R
    rw [hcast]
    simpa only [hold, ↓reduceIte] using hsR
  have hhR' : R'.endpointCount (.inl h) + 2 = D.endpointCount (.inl h) + 1 := by
    have hcast : R'.endpointCount (.inl h) = R.endpointCount (.inl h) :=
      castEnds hgraph R (.inl h)
    rw [hcast]
    simpa only [hold, ↓reduceIte] using hhR
  obtain ⟨E, hsE, heE⟩ := R'.remove_new_vertex G
  refine ⟨E, ?_, ?_⟩
  · rw [hsE]
    exact hsR'
  · rw [heE h]
    omega

/-- The source's both-singleton-carrier case: each trim saves one carrier,
and the returned families can be retained without a hub merge. -/
theorem union_singleton_returned_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : V ⊕ Unit), .inl h) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : V ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : V ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : V ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : V ⊕ Unit))
    (holdD : (D.path iD).start = (.inl h : V ⊕ Unit) ∨
      (D.path iD).finish = (.inl h : V ⊕ Unit))
    (holdE : (E.path iE).start = (.inl h : V ⊕ Unit) ∨
      (E.path iE).finish = (.inl h : V ⊕ Unit))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ D' : Decomposition G, ∃ E' : Decomposition H,
      ∃ F : Decomposition (G ⊔ H),
        D'.size + 1 = D.size ∧ E'.size + 1 = E.size ∧
        0 < D'.endpointCount h ∧ 0 < E'.endpointCount h ∧
        F.size = D'.size + E'.size ∧
        F.size + 2 = D.size + E.size ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD, hpD⟩ := return_terminal_pendant_singleton_saves_one
    G h D iD heD hnewD holdD hD
  obtain ⟨E', hsE, hpE⟩ := return_terminal_pendant_singleton_saves_one
    H h E iE heE hnewE holdE hE
  have hdis : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have ha : G.Adj a b := hg
      have hb : H.Adj a b := hh
      exact ha.ne ((hmeet a ⟨b, ha⟩ ⟨b, hb⟩).trans
        (hmeet b ⟨a, ha.symm⟩ ⟨a, hb.symm⟩).symm)
  obtain ⟨F, hsF, heF⟩ := D'.union_disjoint_endpoints E' hdis
  have hsize : F.size + 2 = D.size + E.size := by
    omega
  have hhub : F.endpointCount h = D'.endpointCount h + E'.endpointCount h := heF h
  refine ⟨D', E', F, hsD, hsE, hpD, hpE, hsF, hsize, ?_⟩
  omega

/-- The source's exactly-one-singleton carrier case: the singleton return
saves one carrier, while the other return retains a three-endpoint hub
reserve. Keeping the two returned families disjoint leaves four hub ends. -/
theorem union_mixed_returned_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : V ⊕ Unit), .inl h) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : V ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : V ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : V ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : V ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl h : V ⊕ Unit) ∨
      (D.path iD).finish = (.inl h : V ⊕ Unit)))
    (holdE : (E.path iE).start = (.inl h : V ⊕ Unit) ∨
      (E.path iE).finish = (.inl h : V ⊕ Unit))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ D' : Decomposition G, ∃ E' : Decomposition H,
      ∃ F : Decomposition (G ⊔ H),
        D'.size ≤ D.size ∧ E'.size + 1 = E.size ∧
        3 ≤ D'.endpointCount h ∧ 0 < E'.endpointCount h ∧
        F.size = D'.size + E'.size ∧
        F.size + 1 ≤ D.size + E.size ∧ 4 ≤ F.endpointCount h := by
  obtain ⟨D', hsD, hrD⟩ := return_terminal_pendant_non_singleton_reserve
    G h D iD heD hnewD holdD hD
  obtain ⟨E', hsE, hpE⟩ := return_terminal_pendant_singleton_saves_one
    H h E iE heE hnewE holdE hE
  have hdis : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have ha : G.Adj a b := hg
      have hb : H.Adj a b := hh
      exact ha.ne ((hmeet a ⟨b, ha⟩ ⟨b, hb⟩).trans
        (hmeet b ⟨a, ha.symm⟩ ⟨a, hb.symm⟩).symm)
  obtain ⟨F, hsF, heF⟩ := D'.union_disjoint_endpoints E' hdis
  have hsize : F.size + 1 ≤ D.size + E.size := by
    omega
  have hhub : F.endpointCount h = D'.endpointCount h + E'.endpointCount h := heF h
  refine ⟨D', E', F, hsD, hsE, hrD, hpE, hsF, hsize, ?_⟩
  omega

/-- The exact carrier count for the mixed pendant profile: the singleton
return saves one carrier and one cross-side join saves the second. -/
theorem splice_mixed_returned_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : V ⊕ Unit), .inl h) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : V ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : V ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : V ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : V ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl h : V ⊕ Unit) ∨
      (D.path iD).finish = (.inl h : V ⊕ Unit)))
    (holdE : (E.path iE).start = (.inl h : V ⊕ Unit) ∨
      (E.path iE).finish = (.inl h : V ⊕ Unit))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ F : Decomposition (G ⊔ H),
      F.size ≤ D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD, hrD⟩ := return_terminal_pendant_non_singleton_reserve
    G h D iD heD hnewD holdD hD
  obtain ⟨E', hsE, hpE⟩ := return_terminal_pendant_singleton_saves_one
    H h E iE heE hnewE holdE hE
  obtain ⟨F, hsF, heF⟩ := D'.single_merge_endpoints E' h (by omega) hpE hmeet
  have hhub : F.endpointCount h + 2 = D'.endpointCount h + E'.endpointCount h := by
    simpa using heF h
  refine ⟨F, ?_, ?_⟩
  · omega
  · omega

/-- Two three-endpoint reserves at a common hub support two cross-side joins.
The two joins save two carriers and still leave two hub endpoints. -/
theorem double_merge_hub_reserve
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V) (D : Decomposition G) (E : Decomposition H)
    (hD : 3 ≤ D.endpointCount h) (hE : 3 ≤ E.endpointCount h)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ F : Decomposition (G ⊔ H),
      F.size = D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨i, j, k, l, hij, hkl, P, Q, hi, hj, hk, hl,
    hPs, hPf, hQs, hQf, hP, hQ, hPQ⟩ :=
    D.two_exposed_joins E h (by omega) (by omega) hmeet
  have hdis : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have ha : G.Adj a b := hg
      have hb : H.Adj a b := hh
      exact ha.ne ((hmeet a ⟨b, ha⟩ ⟨b, hb⟩).trans
        (hmeet b ⟨a, ha.symm⟩ ⟨a, hb.symm⟩).symm)
  obtain ⟨F, hsF, heF⟩ := (D.orientToward h).repack_two_pairs
    (E.orientToward h) i j k l hij hkl P Q hP hQ hPQ hdis
  have hiStart : ((D.orientToward h).path i).start ≠ h := by
    intro hs
    exact ((D.orientToward h).path i).start_ne_finish _ (hs.trans hi.symm)
  have hjStart : ((D.orientToward h).path j).start ≠ h := by
    intro hs
    exact ((D.orientToward h).path j).start_ne_finish _ (hs.trans hj.symm)
  have hkStart : ((E.orientToward h).path k).start ≠ h := by
    intro hs
    exact ((E.orientToward h).path k).start_ne_finish _ (hs.trans hk.symm)
  have hlStart : ((E.orientToward h).path l).start ≠ h := by
    intro hs
    exact ((E.orientToward h).path l).start_ne_finish _ (hs.trans hl.symm)
  have hPstart : P.start ≠ h := by simpa [hPs] using hiStart
  have hPfinish : P.finish ≠ h := by simpa [hPf] using hkStart
  have hQstart : Q.start ≠ h := by simpa [hQs] using hjStart
  have hQfinish : Q.finish ≠ h := by simpa [hQf] using hlStart
  have hhub := heF h
  rw [D.orientToward_endpointCount, E.orientToward_endpointCount] at hhub
  simp [hi, hj, hk, hl, hiStart, hjStart, hkStart, hlStart,
    hPstart, hPfinish, hQstart, hQfinish] at hhub
  refine ⟨F, hsF, ?_⟩
  omega

/-- The exact pendant-level reconstruction for two non-singleton carriers:
return both, then make two cross-side joins. -/
theorem double_merge_non_singleton_returned_pendants_at_hub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : V)
    (D : Decomposition (pendantExtension G h))
    (E : Decomposition (pendantExtension H h))
    (iD : Fin D.size) (iE : Fin E.size)
    (heD : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path iD).walk.edges)
    (heE : s((.inr () : V ⊕ Unit), .inl h) ∈ (E.path iE).walk.edges)
    (hnewD : (D.path iD).start = (.inr () : V ⊕ Unit) ∨
      (D.path iD).finish = (.inr () : V ⊕ Unit))
    (hnewE : (E.path iE).start = (.inr () : V ⊕ Unit) ∨
      (E.path iE).finish = (.inr () : V ⊕ Unit))
    (holdD : ¬ ((D.path iD).start = (.inl h : V ⊕ Unit) ∨
      (D.path iD).finish = (.inl h : V ⊕ Unit)))
    (holdE : ¬ ((E.path iE).start = (.inl h : V ⊕ Unit) ∨
      (E.path iE).finish = (.inl h : V ⊕ Unit)))
    (hD : 2 ≤ D.endpointCount (.inl h))
    (hE : 2 ≤ E.endpointCount (.inl h))
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = h) :
    ∃ F : Decomposition (G ⊔ H),
      F.size ≤ D.size + E.size - 2 ∧ 2 ≤ F.endpointCount h := by
  obtain ⟨D', hsD, hrD⟩ := return_terminal_pendant_non_singleton_reserve
    G h D iD heD hnewD holdD hD
  obtain ⟨E', hsE, hrE⟩ := return_terminal_pendant_non_singleton_reserve
    H h E iE heE hnewE holdE hE
  obtain ⟨F, hsF, hhF⟩ := double_merge_hub_reserve G H h D' E' hrD hrE hmeet
  refine ⟨F, ?_, hhF⟩
  omega

end Gallai.TwoException
