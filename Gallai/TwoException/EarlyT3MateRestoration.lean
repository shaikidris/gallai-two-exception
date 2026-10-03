/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryTriangleComponent
public import Gallai.Structure.EdgeDeletion

@[expose] public section

/-! # Final mate restoration after the T3 reserved edge -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3FinalMateAdj (b c : V) :
    DecidableRel (G.deleteEdges {s(b,c)}).Adj := fun _ _ => Classical.propDecidable _

/-- After reserved-edge restoration exposes the third triangle vertex,
the opposite mate restores freely. All endpoint counts outside its two ends
are preserved, in particular the prescribed vertex's reserve. -/
theorem restore_t3_opposite_mate
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c)
    (D : Decomposition (G.deleteEdges {s((b : V),(c : V))}))
    (ha : 0 < D.endpointCount a) :
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount b ∧
      ∀ t, t ≠ (b : V) → t ≠ (c : V) → E.endpointCount t = D.endpointCount t := by
  classical
  let J := G.deleteEdges {s((b : V),(c : V))}
  have hbOdd : Odd (J.degree b) := by
    have hd := degree_delete_edge_add_one G b c hbc
    have he : Even (G.degree b) := b.property
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    change Odd ((G.deleteEdges {s((b : V),(c : V))}).neighborSet b).ncard
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at he
    omega
  have hcOdd : Odd (J.degree c) := by
    have hd := degree_delete_edge_add_one_other G b c hbc
    have he : Even (G.degree c) := c.property
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    change Odd ((G.deleteEdges {s((b : V),(c : V))}).neighborSet c).ncard
    rw [Nat.odd_iff]
    rw [Nat.even_iff] at he
    omega
  have hmissing : ¬ J.Adj b c := by simp [J]
  have hpositive : ∀ t, J.Adj b t → 0 < D.endpointCount t := by
    intro t hbt
    by_cases htOdd : Odd (J.degree t)
    · exact D.endpointCount_pos_of_odd_degree t htOdd
    have htb : t ≠ (b : V) := hbt.ne.symm
    have htc : t ≠ (c : V) := by
      intro he
      exact hmissing (he ▸ hbt)
    have hd := degree_delete_edge_of_ne G b c t htb htc
    have htEven : Even (J.degree t) := (Nat.even_or_odd _).resolve_right htOdd
    have he : Even (G.degree t) := by
      simp only [← SimpleGraph.ncard_neighborSet] at hd htEven ⊢
      change Even ((G.deleteEdges {s((b : V),(c : V))}).neighborSet t).ncard at htEven
      rw [hd] at htEven
      exact htEven
    rcases triangle_component_even_neighbors Z a b c hsupp t hbt.1 he with ht | ht
    · exact ht ▸ ha
    · exact False.elim (htc ht)
  have hout := restore_ordinary_triangle_mate D b c hbc.ne hmissing hbOdd hcOdd hpositive
  rw [delete_edge_sup_edge G b c hbc] at hout
  obtain ⟨E,hs,hb,hvec⟩ := hout
  refine ⟨E,hs,hb,?_⟩
  intro t htb htc
  simpa only [htb.symm,htc.symm,ite_false,Nat.add_zero] using hvec t

end Gallai.TwoException
