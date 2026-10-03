/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.PendantExtension
public import Gallai.Repair.TerminalEdge
public import Gallai.Repair.Exposure
public import Gallai.Operations.RemoveNewVertex
public import Gallai.Operations.SingleMerge

@[expose] public section

/-! # Returning across a terminal pendant edge

The fresh pendant edge can be deleted at no path-count cost when its carrier
is terminal at the new leaf.  The result is first the old graph image with an
isolated sum vertex, then the exact original graph after removing that vertex.
The terminality premise is intentionally explicit: source-specific restoration
arguments must establish it on their actual returned decomposition.
-/

namespace Gallai

universe u

variable {V : Type u} [DecidableEq V]

/-- In every decomposition of the pendant extension, the unique fresh-leaf
edge lies terminally on one of its carriers.  Endpoint positivity supplies a
terminal carrier at the odd fresh leaf; its unique graph neighbour identifies
the edge on that carrier. -/
theorem Decomposition.exists_terminal_pendant_carrier [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) :
    ∃ i : Fin D.size,
      s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path i).walk.edges ∧
      ((D.path i).start = (.inr () : V ⊕ Unit) ∨
        (D.path i).finish = (.inr () : V ⊕ Unit)) := by
  have hpos : 0 < D.endpointCount (.inr () : V ⊕ Unit) :=
    D.endpointCount_pos_of_odd_degree (.inr ()) (pendantExtension_odd_new G h)
  obtain ⟨i, hi⟩ := D.exists_terminal_of_pos (.inr ()) hpos
  refine ⟨i, ?_, hi⟩
  rcases hi with hs | hf
  · have hadj : (pendantExtension G h).Adj (.inr ()) (D.path i).walk.snd := by
      simpa only [hs] using (D.path i).walk.adj_snd (D.path i).nonempty
    have hsnd : (D.path i).walk.snd = (.inl h : V ⊕ Unit) :=
      (pendantExtension_adj_new G h _).mp hadj
    have hmem : s((D.path i).start, (.inl h : V ⊕ Unit)) ∈ (D.path i).walk.edges :=
      ((D.path i).first_spoke_iff (.inl h)).mpr hsnd.symm
    simpa only [hs] using hmem
  · have hadj : (pendantExtension G h).Adj (.inr ())
      ((D.path i).reverse.walk.snd) := by
      simpa only [NonemptyPath.reverse, hf] using
        (D.path i).reverse.walk.adj_snd (D.path i).reverse.nonempty
    have hsnd : (D.path i).reverse.walk.snd = (.inl h : V ⊕ Unit) :=
      (pendantExtension_adj_new G h _).mp hadj
    have hmem : s((D.path i).finish, (.inl h : V ⊕ Unit)) ∈ (D.path i).walk.edges :=
      ((D.path i).last_spoke_iff (.inl h)).mpr hsnd.symm
    simpa only [hf] using hmem

/-- A decomposition of a pendant extension returns to the old graph at no
path-count cost whenever the pendant edge is terminal at its fresh leaf.
The endpoint formula records the only possible loss at the old attachment;
all other old endpoint counts are preserved. -/
theorem Decomposition.return_terminal_pendant
    (G : SimpleGraph V) (h : V)
    (D : Decomposition (pendantExtension G h)) (i : Fin D.size)
    (he : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path i).walk.edges)
    (hterminal : (D.path i).start = (.inr () : V ⊕ Unit) ∨
      (D.path i).finish = (.inr () : V ⊕ Unit)) :
    ∃ E : Decomposition G,
      E.size ≤ D.size ∧
      E.endpointCount h +
          (if (D.path i).start = (.inl h : V ⊕ Unit) ∨
              (D.path i).finish = (.inl h : V ⊕ Unit) then 2 else 0) =
        D.endpointCount (.inl h) + 1 ∧
      ∀ v, v ≠ h → E.endpointCount v = D.endpointCount (.inl v) := by
  obtain ⟨R, hsize, _, hh, hother⟩ :=
    D.exists_delete_terminal i (.inr ()) (.inl h) he hterminal
  have hedge : s((.inr () : V ⊕ Unit), .inl h) =
      s((.inl h : V ⊕ Unit), .inr ()) := Sym2.eq_swap
  have hgraph : (pendantExtension G h).deleteEdges
      {s((.inr () : V ⊕ Unit), .inl h)} =
      G.map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
    rw [hedge, pendantExtension_delete_pendant]
  have castSize {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) : (e ▸ P).size = P.size := by
    subst M
    rfl
  have castEnds {L M : SimpleGraph (V ⊕ Unit)} (e : L = M)
      (P : Decomposition L) (v : V ⊕ Unit) :
      (e ▸ P).endpointCount v = P.endpointCount v := by
    subst M
    rfl
  let R' : Decomposition (G.map (Function.Embedding.inl : V ↪ V ⊕ Unit)) := hgraph ▸ R
  have hsize' : R'.size +
      (if (D.path i).start = (.inl h : V ⊕ Unit) ∨
          (D.path i).finish = (.inl h : V ⊕ Unit) then 1 else 0) = D.size := by
    rw [show R'.size = R.size by exact castSize hgraph R]
    exact hsize
  have hh' : R'.endpointCount (.inl h) +
      (if (D.path i).start = (.inl h : V ⊕ Unit) ∨
          (D.path i).finish = (.inl h : V ⊕ Unit) then 2 else 0) =
        D.endpointCount (.inl h) + 1 := by
    rw [show R'.endpointCount (.inl h) = R.endpointCount (.inl h) by
      exact castEnds hgraph R (.inl h)]
    exact hh
  have hother' : ∀ w : V ⊕ Unit, w ≠ .inr () → w ≠ .inl h →
      R'.endpointCount w = D.endpointCount w := by
    intro w hwNew hwH
    rw [show R'.endpointCount w = R.endpointCount w by exact castEnds hgraph R w]
    exact hother w hwNew hwH
  obtain ⟨E, hEsize, hEends⟩ := R'.remove_new_vertex G
  refine ⟨E, ?_, ?_, ?_⟩
  · rw [hEsize]
    exact Nat.le_of_add_right_le hsize'.le
  · rw [hEends h]
    exact hh'
  · intro v hv
    rw [hEends v]
    exact hother' (.inl v) (by simp) (by simpa using hv)

/-- The fresh pendant can always be removed from a decomposition of its own
extension.  This merely combines degree-one terminality with the exact return
accounting above; reconstruction schedules may use it after any operation
that restores the old graph while retaining the fresh leaf. -/
theorem Decomposition.return_pendant [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) :
    ∃ E : Decomposition G,
      E.size ≤ D.size ∧
      ∃ i : Fin D.size,
        E.endpointCount h +
            (if (D.path i).start = (.inl h : V ⊕ Unit) ∨
                (D.path i).finish = (.inl h : V ⊕ Unit) then 2 else 0) =
          D.endpointCount (.inl h) + 1 ∧
        ∀ v, v ≠ h → E.endpointCount v = D.endpointCount (.inl v) := by
  obtain ⟨i, he, hterminal⟩ := D.exists_terminal_pendant_carrier G h
  obtain ⟨E, hsize, hh, hother⟩ := D.return_terminal_pendant G h i he hterminal
  exact ⟨E, hsize, i, hh, hother⟩

/-- Returning a pendant attached to an even-degree vertex preserves a double
endpoint reserve, except in one literal terminal-carrier profile.  The bad
profile is exact: the returned hub has no endpoints, the auxiliary had exactly
one, and the pendant carrier also ended at the old hub.  This separates the
genuine endpoint-selection obstruction from ordinary pendant bookkeeping. -/
theorem Decomposition.return_pendant_even_endpoint_dichotomy [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) (heven : Even (G.degree h)) :
    ∃ E : Decomposition G, E.size ≤ D.size ∧
      (2 ≤ E.endpointCount h ∨
        E.endpointCount h = 0 ∧ D.endpointCount (.inl h) = 1 ∧
          ∃ i : Fin D.size,
            (D.path i).start = (.inl h : V ⊕ Unit) ∨
              (D.path i).finish = (.inl h : V ⊕ Unit)) := by
  obtain ⟨E, hsize, i, hends, _⟩ := D.return_pendant G h
  by_cases hterminal : (D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit)
  · by_cases htwo : 2 ≤ E.endpointCount h
    · exact ⟨E, hsize, Or.inl htwo⟩
    · have hEzero : E.endpointCount h = 0 := by
        have hparity := E.endpointCount_mod_two h
        rw [Nat.even_iff] at heven
        omega
      refine ⟨E, hsize, Or.inr ⟨hEzero, ?_, i, hterminal⟩⟩
      · simp only [if_pos hterminal] at hends
        omega
  · refine ⟨E, hsize, Or.inl ?_⟩
    have hodd : Odd ((pendantExtension G h).degree (.inl h)) := by
      rw [pendantExtension_degree_attach]
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    have hpos := D.endpointCount_pos_of_odd_degree (.inl h) hodd
    simp only [if_neg hterminal] at hends
    omega

/-- If the pendant carrier also ends at its old attachment, deleting that
carrier saves exactly one path.  The endpoint equation is retained explicitly
so a later split at the old attachment can spend precisely this saving. -/
theorem Decomposition.return_terminal_pendant_at_old_end_saves_one [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h)) (i : Fin D.size)
    (he : s((.inr () : V ⊕ Unit), .inl h) ∈ (D.path i).walk.edges)
    (hnew : (D.path i).start = (.inr () : V ⊕ Unit) ∨
      (D.path i).finish = (.inr () : V ⊕ Unit))
    (hold : (D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit)) :
    ∃ E : Decomposition G,
      E.size + 1 = D.size ∧
      E.endpointCount h + 2 = D.endpointCount (.inl h) + 1 ∧
      ∀ v, v ≠ h → E.endpointCount v = D.endpointCount (.inl v) := by
  obtain ⟨R, hsR, _, hhR, hotherR⟩ :=
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
  have hotherR' : ∀ w : V ⊕ Unit, w ≠ .inr () → w ≠ .inl h →
      R'.endpointCount w = D.endpointCount w := by
    intro w hwNew hwH
    rw [show R'.endpointCount w = R.endpointCount w by exact castEnds hgraph R w]
    exact hotherR w hwNew hwH
  obtain ⟨E, hsE, heE⟩ := R'.remove_new_vertex G
  refine ⟨E, ?_, ?_, ?_⟩
  · rw [hsE]
    exact hsR'
  · rw [heE h]
    exact hhR'
  · intro v hv
    rw [heE v]
    exact hotherR' (.inl v) (by simp) (by simpa using hv)

/-- A pendant attached to a positive even old vertex can always be returned
within the original budget while exposing that vertex twice.  A non-singleton
carrier creates the reserve directly.  If the carrier is the pendant edge
itself, its exact one-path saving pays for `exists_expose_even`. -/
theorem Decomposition.return_pendant_even_exposes [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : V)
    (D : Decomposition (pendantExtension G h))
    (hpositive : 0 < G.degree h) (heven : Even (G.degree h)) :
    ∃ E : Decomposition G, E.size ≤ D.size ∧ 2 ≤ E.endpointCount h ∧
      ∀ v, v ≠ h → E.endpointCount v = D.endpointCount (.inl v) := by
  obtain ⟨i, hi, hnew⟩ := D.exists_terminal_pendant_carrier G h
  by_cases hold : (D.path i).start = (.inl h : V ⊕ Unit) ∨
      (D.path i).finish = (.inl h : V ⊕ Unit)
  · obtain ⟨E, hEsize, _, hEother⟩ :=
      D.return_terminal_pendant_at_old_end_saves_one G h i hi hnew hold
    obtain ⟨F, hFsize, hFends, hFother⟩ := E.exists_expose_even h hpositive heven
    refine ⟨F, ?_, hFends, ?_⟩
    · rw [hFsize]
      split_ifs <;> omega
    · intro v hv
      rw [hFother v hv, hEother v hv]
  · obtain ⟨E, hEsize, hEends, hEother⟩ := D.return_terminal_pendant G h i hi hnew
    refine ⟨E, hEsize, ?_, hEother⟩
    have hodd : Odd ((pendantExtension G h).degree (.inl h)) := by
      rw [pendantExtension_degree_attach]
      rcases heven with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    have hpos := D.endpointCount_pos_of_odd_degree (.inl h) hodd
    simp only [hold, ↓reduceIte] at hEends
    omega

end Gallai
