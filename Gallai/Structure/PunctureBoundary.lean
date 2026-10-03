/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-! # Actual boundary interfaces of edge punctures

A nonempty closed part of a proper edge puncture meets a removed edge.
The complementary graph touches that part only at removed-edge endpoints.
These statements provide the graph interface, not a supplied decomposition.
-/

namespace Gallai

variable {V : Type*} {G H : SimpleGraph V}

/-- Every nonempty closed part of a proper puncture of a connected graph
contains an endpoint of a removed edge, even if the part is all vertices. -/
theorem puncture_closed_boundary_nonempty (hconn : G.Connected) (hlt : H < G)
    (S : Set V) (hne : S.Nonempty)
    (hclosed : ∀ v ∈ S, H.neighborSet v ⊆ S) :
    ∃ v ∈ S, ∃ w, G.Adj v w ∧ ¬ H.Adj v w := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨a, ha⟩ := hne
  have step : ∀ {v w : V}, G.Walk v w → v ∈ S → w ∈ S := by
    intro v w p
    induction p with
    | nil => exact id
    | @cons v w t hvw p ih =>
      intro hv
      exact ih (hclosed v hv (hn v hv w hvw))
  have hall (v : V) : v ∈ S := by
    obtain ⟨p⟩ := hconn a v
    exact step p ha
  have hge : G ≤ H := fun v w hvw => hn v (hall v) w hvw
  exact (not_le_of_gt hlt) hge

/-- The edge complement of a mapped puncture part can meet the part only
where an original edge was removed. -/
theorem puncture_closed_complement_support (S B : Set V)
    (hclosed : ∀ v ∈ S, H.neighborSet v ⊆ S)
    (hboundary : ∀ v ∈ S, ∀ w, G.Adj v w → ¬ H.Adj v w → v ∈ B) :
    (G \ (H.induce S).spanningCoe).support ⊆ Sᶜ ∪ B := by
  classical
  rintro v ⟨w, hvw⟩
  by_cases hv : v ∈ S
  · right
    apply hboundary v hv w hvw.1
    intro hh
    have hw := hclosed v hv hh
    exact hvw.2 ((SimpleGraph.map_adj (Function.Embedding.subtype _)
      (H.induce S) v w).mpr ⟨⟨v, hv⟩, ⟨w, hw⟩, hh, rfl, rfl⟩)
  · exact Or.inl hv

/-- A singleton removed-edge boundary forbids removed edges internal to
the closed part; this identifies its induced graph in the original graph. -/
theorem induce_eq_of_singleton_puncture_boundary (hle : H ≤ G) (S : Set V) (z : V)
    (hboundary : ∀ v ∈ S, ∀ w, G.Adj v w → ¬ H.Adj v w → v = z) :
    H.induce S = G.induce S := by
  ext a b
  constructor
  · exact fun h => hle h
  · intro h
    by_contra hn
    have ha := hboundary a a.property b h hn
    have hb := hboundary b b.property a h.symm (fun hh => hn hh.symm)
    exact h.ne (Subtype.ext (ha.trans hb.symm))

end Gallai
