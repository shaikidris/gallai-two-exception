/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareLongContactCoverage
public import Gallai.TwoException.BareAmbientCorridor
public import Gallai.TwoException.BareRelabel

@[expose] public section

/-! # The bare prescribed-even-vertex endpoint theorem -/
namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The shortest odd corridor and exhaustive native contact reconstruction
exclude a relative minimum counterexample to the bare endpoint theorem. -/
theorem bare_minimal_counterexample_false
    (h x : V) (H : BareMinimalCounterexample G h x) : False := by
  classical
  let xe : evenVertices G := ⟨x,H.counterexample.1.2.2.2.2.1⟩
  let C := (evenSubgraph G).connectedComponentMk xe
  have hxC : xe ∈ C.supp := by simp [C]
  obtain ⟨a,b,ha,hb,hab,hcontact,hcontacts,hsep,_,_⟩ :=
    bare_exists_reserved_odd_edge h xe H C hxC
  obtain ⟨D,hsize,hh⟩ := bare_long_contact_endpoint h a b xe H C hxC
    ha hb hab hsep hcontact hcontacts
  exact H.counterexample.2 ⟨D,hsize,hh⟩

/-- A connected finite simple graph with a positive even vertex h having
no even neighbour, and at most one further E-degree exception x, has a
ceiling-budget path decomposition exposing h at least twice. Neither
designated vertex is assumed to be non-cut. -/
theorem bare_endpoint (h x : V) (hG : BareInstance G h x) : BareConclusion G h := by
  classical
  have hall := lexicographic_finite_graph_induction
    (fun {W} _ _ (J : SimpleGraph W) _ =>
      ∀ a b : W, BareInstance J a b → BareConclusion J a)
    (by
      intro n W _ _ J _ hW hvertex hedge a b hJ
      by_contra hf
      have H : BareMinimalCounterexample J a b :=
        bareMinimalCounterexample_of_fixed_type a b ⟨hJ,hf⟩
          (by
            intro U _ _ K _ c d hsmall hK
            exact hvertex (Fintype.card U) (by omega) U K rfl c d hK)
          (by
            intro K _ c d hsmall hK
            exact hedge K hsmall c d hK)
      exact bare_minimal_counterexample_false a b H)
  exact hall V G h x hG

end Gallai.TwoException
