/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3ReservedPositivity

@[expose] public section

/-! # Reserved T3 positivity survives a separated private-mate deletion -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance twoMatePositiveGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- The extra private mate avoids every retained neighbour of the reserved
triangle vertex, so their odd parity and positive endpoints survive. -/
theorem t3_two_mate_reserved_positive
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c)
    (p q : V) (hap : ¬ G.Adj a p) (haq : ¬ G.Adj a q)
    (D : Decomposition (((starPuncture G u B).deleteEdges
      {s((b : V),(c : V))}).deleteEdges {s(p,q)})) :
    ∀ t, ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).Adj a t →
      0 < D.endpointCount t := by
  intro t ht
  have htp : t ≠ p := fun he => hap (he ▸ ht.1.1)
  have htq : t ≠ q := fun he => haq (he ▸ ht.1.1)
  have ho := t3_reserved_neighbours_odd Z a b c hsupp u B hadj hleaves haB
    hbu hcu hbB hcB hbc t ht
  have hd := degree_delete_edge_of_ne
    ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}) p q t htp htq
  apply D.endpointCount_pos_of_odd_degree t
  simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
  rwa [hd]

end Gallai.TwoException
