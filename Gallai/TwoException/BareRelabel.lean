/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareMinimality
public import Gallai.Operations.DecompositionMap

@[expose] public section

/-! # Relabelling the bare two-exception endpoint target

The relative minimal-counterexample argument compares a smaller graph on an
arbitrary finite vertex type with one on the current type.  At equal order an
equivalence of vertex types turns that comparison into an edge comparison on
one type.  This file records the endpoint part of that transport explicitly.
-/

namespace Gallai.TwoException

universe u v

variable {V : Type u} {W : Type v}

/-- The literal bare-instance hypotheses are invariant under relabelling the
vertex type. -/
theorem bareInstance_map [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (e : V ≃ W) (h x : V) :
    BareInstance G h x → BareInstance (G.map e.toEmbedding) (e h) (e x) := by
  intro hG
  let f : G ≃g G.map e.toEmbedding := SimpleGraph.Iso.map e G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.connected_iff.mp hG.1
  · exact fun hEq => hG.2.1 (e.injective hEq)
  · change 0 < (G.map e.toEmbedding).degree (f h)
    rw [← SimpleGraph.Iso.degree_eq f h]
    exact hG.2.2.1
  · change Even ((G.map e.toEmbedding).degree (f h))
    rw [← SimpleGraph.Iso.degree_eq f h]
    exact hG.2.2.2.1
  · change Even ((G.map e.toEmbedding).degree (f x))
    rw [← SimpleGraph.Iso.degree_eq f x]
    exact hG.2.2.2.2.1
  · change eDegree (G.map e.toEmbedding) (f h) = 0
    rw [← SimpleGraph.Iso.eDegree_eq f h]
    exact hG.2.2.2.2.2.1
  · intro w hwEven hwh hwx
    obtain ⟨v, rfl⟩ := e.surjective w
    have hvEven : Even (G.degree v) := by
      change Even ((G.map e.toEmbedding).degree (f v)) at hwEven
      rw [← SimpleGraph.Iso.degree_eq f v] at hwEven
      exact hwEven
    have hvh : v ≠ h := fun hvh => hwh (by simp [hvh])
    have hvx : v ≠ x := fun hvx => hwx (by simp [hvx])
    change eDegree (G.map e.toEmbedding) (f v) ≤ 3
    rw [← SimpleGraph.Iso.eDegree_eq f v]
    exact hG.2.2.2.2.2.2 v hvEven hvh hvx

/-- Relabelling a decomposition along a vertex equivalence preserves the bare
endpoint conclusion. -/
theorem bareConclusion_map [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] (e : V ≃ W) (h : V) :
    BareConclusion G h → BareConclusion (G.map e.toEmbedding) (e h) := by
  intro hG
  rcases hG with ⟨D, hsize, hend⟩
  refine ⟨D.map e.toEmbedding, ?_, ?_⟩
  · rw [Decomposition.map_size]
    have hcard : Fintype.card V = Fintype.card W := (SimpleGraph.Iso.map e G).card_eq
    omega
  · change 2 ≤ (D.map e.toEmbedding).endpointCount (e.toEmbedding h)
    rw [Decomposition.map_endpointCount]
    exact hend

/-- The bare endpoint conclusion is invariant under a relabelling of the
vertex type. -/
theorem bareConclusion_map_iff [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    (e : V ≃ W) (h : V) :
    BareConclusion (G.map e.toEmbedding) (e h) ↔ BareConclusion G h := by
  constructor
  · intro hmap
    have hback := bareConclusion_map e.symm (e h) hmap
    have hgraph : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
      rw [SimpleGraph.map_map]
      ext a b
      simp
    have hback' : BareConclusion ((G.map e.toEmbedding).map e.symm.toEmbedding) h := by
      simpa using hback
    exact bareConclusion_congr h hgraph hback'
  · exact bareConclusion_map e h

/-- Build the cross-type relative-minimality resource from a fixed-vertex-type
edge induction.  Equal-order competitors are relabelled before their edge
count is compared; smaller-order competitors are consumed directly. -/
theorem bareMinimalCounterexample_of_fixed_type
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h x : V) (hfail : BareCounterexample G h x)
    (hvertex : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj] (u v : W),
      Fintype.card W < Fintype.card V → BareInstance J u v → BareConclusion J u)
    (hedge : ∀ (J : SimpleGraph V) [DecidableRel J.Adj] (u v : V),
      J.edgeFinset.card < G.edgeFinset.card → BareInstance J u v → BareConclusion J u) :
    BareMinimalCounterexample G h x := by
  refine ⟨hfail, ?_⟩
  intro W _ _ J _ u v hsmaller hJ
  rcases hsmaller with hvertexSmaller | ⟨hcard, hedgeSmaller⟩
  · exact hvertex W J u v hvertexSmaller hJ
  · let e : W ≃ V := Fintype.equivOfCardEq hcard
    apply (bareConclusion_map_iff e u).mp
    apply hedge (J.map e.toEmbedding) (e u) (e v)
    · calc
        (J.map e.toEmbedding).edgeFinset.card = J.edgeFinset.card :=
          SimpleGraph.card_edgeFinset_map e.toEmbedding J
        _ < G.edgeFinset.card := hedgeSmaller
    · exact bareInstance_map e u v hJ

end Gallai.TwoException
