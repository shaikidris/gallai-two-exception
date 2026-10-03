/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyT3TwoMatePositivity

@[expose] public section

/-! # Reserved T3 positivity after the E5 spoke and private mate -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance e5PositiveGraph (Q : SimpleGraph V) :
    DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _

/-- Both E5 private deletions avoid the retained neighbours of the
reserved triangle vertex. Their original odd parity supplies positivity. -/
theorem t3_E5_reserved_positive
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (u : V) (B : Finset V)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (haB : (a : V) ∈ B) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hbB : (b : V) ∉ B) (hcB : (c : V) ∉ B) (hbc : G.Adj b c)
    (x s p q : V) (hax : ¬ G.Adj a x) (has : ¬ G.Adj a s)
    (hap : ¬ G.Adj a p) (haq : ¬ G.Adj a q)
    (D : Decomposition ((((starPuncture G u B).deleteEdges
      {s((b : V),(c : V))}).deleteEdges {s(x,s)}).deleteEdges {s(q,p)})) :
    ∀ t, ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).Adj a t →
      0 < D.endpointCount t := by
  intro t ht
  have htx : t ≠ x := fun he => hax (he ▸ ht.1.1)
  have hts : t ≠ s := fun he => has (he ▸ ht.1.1)
  have htp : t ≠ p := fun he => hap (he ▸ ht.1.1)
  have htq : t ≠ q := fun he => haq (he ▸ ht.1.1)
  have ho := t3_reserved_neighbours_odd Z a b c hsupp u B hadj hleaves haB
    hbu hcu hbB hcB hbc t ht
  have hd1 := degree_delete_edge_of_ne
    ((starPuncture G u B).deleteEdges {s((b : V),(c : V))}) x s t htx hts
  have hd2 := degree_delete_edge_of_ne
    (((starPuncture G u B).deleteEdges {s((b : V),(c : V))}).deleteEdges {s(x,s)})
    q p t htq htp
  apply D.endpointCount_pos_of_odd_degree t
  simp only [← SimpleGraph.ncard_neighborSet] at hd1 hd2 ho ⊢
  rw [hd2,hd1]
  exact ho

end Gallai.TwoException
