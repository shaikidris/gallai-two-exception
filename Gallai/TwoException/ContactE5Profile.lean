/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactPunctureWitness

@[expose] public section

/-! # Parity preservation across the two E5 preparation edges -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance E5ProfileStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance E5ProfileSpokeAdj (u x s : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance E5ProfileMateAdj (u x s p q : V) (B : Finset V) :
    DecidableRel (((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Separate spoke and mate deletions flip four distinct even vertices.
The even star at the odd centre introduces no new even vertex. -/
theorem contact_E5_puncture_profile
    (u x s p q : V) (B : Finset V) (hu : u ∉ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxu : x ≠ u) (hsu : s ≠ u) (hxB : x ∉ B) (hsB : s ∉ B)
    (hxs : G.Adj x s) (hxEven : Even (G.degree x)) (hsEven : Even (G.degree s))
    (hpu : p ≠ u) (hqu : q ≠ u) (hpB : p ∉ B) (hqB : q ∉ B)
    (hpx : p ≠ x) (hps : p ≠ s) (hqx : q ≠ x) (hqs : q ≠ s)
    (hqp : G.Adj q p) (hpEven : Even (G.degree p)) (hqEven : Even (G.degree q)) :
    (∀ t, Even ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).degree t) → Even (G.degree t)) ∧
    Odd ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree x) ∧
    Odd ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree s) ∧
    Odd ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree p) ∧
    Odd ((((starPuncture G u B).deleteEdges {s(x,s)}).deleteEdges {s(q,p)}).degree q) := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(x,s)}
  let J := K.deleteEdges {s(q,p)}
  letI : DecidableRel Q.Adj := E5ProfileStarAdj u B
  letI : DecidableRel K.Adj := E5ProfileSpokeAdj u x s B
  letI : DecidableRel J.Adj := E5ProfileMateAdj u x s p q B
  change (∀ t, Even (J.degree t) → Even (G.degree t)) ∧
    Odd (J.degree x) ∧ Odd (J.degree s) ∧ Odd (J.degree p) ∧ Odd (J.degree q)
  have hfirst := contact_spoke_puncture_profile u x s B hu hadj huOdd hB hleaves
    hxu hsu hxB hsB hxs hxEven hsEven
  have hpd : K.degree p = G.degree p := by
    have hd := degree_delete_edge_of_ne Q x s p hpx hps
    have hj := starPuncture_degree_other (G := G) u B p hpu hpB
    dsimp only [K, Q] at hd ⊢
    simp only [← SimpleGraph.ncard_neighborSet] at hd hj ⊢
    exact hd.trans hj
  have hqd : K.degree q = G.degree q := by
    have hd := degree_delete_edge_of_ne Q x s q hqx hqs
    have hj := starPuncture_degree_other (G := G) u B q hqu hqB
    dsimp only [K, Q] at hd ⊢
    simp only [← SimpleGraph.ncard_neighborSet] at hd hj ⊢
    exact hd.trans hj
  have hpK : Even (K.degree p) := hpd ▸ hpEven
  have hqK : Even (K.degree q) := hqd ▸ hqEven
  have hqpQ : Q.Adj q p := by
    refine ⟨hqp, ?_⟩
    intro ha
    exact hpu ((star_sup_adj_off_center u B q p hqu).mp ha).2
  have hqpK : K.Adj q p := by
    simpa [K, SimpleGraph.deleteEdges_adj, hqx, hqs] using hqpQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    apply hfirst.1 t
    have hk := even_edge_deletion_even_preserved (G := K) q p hqpK hqK hpK t
    simp only [← SimpleGraph.ncard_neighborSet] at hk ht ⊢
    exact hk ht
  · have hd := degree_delete_edge_of_ne K q p x hqx.symm hpx.symm
    simp only [← SimpleGraph.ncard_neighborSet] at hd hfirst ⊢
    exact hd ▸ hfirst.2.1
  · have hd := degree_delete_edge_of_ne K q p s hqs.symm hps.symm
    simp only [← SimpleGraph.ncard_neighborSet] at hd hfirst ⊢
    exact hd ▸ hfirst.2.2
  · have hd := degree_delete_edge_add_one_other K q p hqpK
    dsimp only [J]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hpK ⊢
    rw [Nat.even_iff] at hpK
    rw [Nat.odd_iff]
    omega
  · have hd := degree_delete_edge_add_one K q p hqpK
    dsimp only [J]
    simp only [← SimpleGraph.ncard_neighborSet] at hd hqK ⊢
    rw [Nat.even_iff] at hqK
    rw [Nat.odd_iff]
    omega

end Gallai.TwoException
