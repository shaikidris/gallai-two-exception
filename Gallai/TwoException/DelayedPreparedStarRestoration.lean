/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPendingBound
public import Gallai.TwoException.OrdinaryPreparedHalfStarGain
public import Gallai.TwoException.PacketGainStarRestoration

@[expose] public section

/-! # Delayed star restoration from original packet labels -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R J : SimpleGraph V} [DecidableRel R.Adj] [DecidableRel J.Adj]
noncomputable local instance delayedPreparedEq :
    DecidableEq (evenSubgraph R).ConnectedComponent := Classical.decEq _
noncomputable local instance delayedPreparedHalfAdj (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Original private labels and ordinary packet reserves discharge every
passing-bound and gain interface of the delayed odd-star restoration.
The hub remains unpaid and exposed throughout this operation. -/
theorem restore_delayed_prepared_star
    (D : Decomposition J) (u x b : V) (K L : Finset V)
    (F special : Finset (evenSubgraph R).ConnectedComponent)
    (P : (evenSubgraph R).ConnectedComponent → Finset (evenVertices R))
    (hL : L = (F.biUnion P).image Subtype.val)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hPS : ∀ C ∈ F, (P C).image Subtype.val ⊆ K ∪ L)
    (hdis : Disjoint K L) (hu : u ∉ K ∪ L) (hxS : x ∉ K ∪ L)
    (hxu : x ≠ u) (hb : b ∈ K ∪ L) (hodd : Odd #(K ∪ L))
    (hstrict : #special + 1 < #K + #F)
    (hsub : J ≤ R) (hadj : ∀ t ∈ K ∪ L, R.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (R.degree t))
    (hprofile : ∀ t, Even (J.degree t) → Even (R.degree t) ∨ t = u)
    (hmissing : ∀ t ∈ K ∪ L, ¬ J.Adj u t)
    (hpositive : ∀ t, J.Adj u t ∨ t ∈ K ∪ L → 0 < D.endpointCount t)
    (hx : 0 < D.endpointCount x)
    (hprivate : ∀ w ∈ K, ∃ p, ∀ t, R.Adj w t → Even (R.degree t) → t = x ∨ t = p)
    (hcap : ∀ w ∈ L, eDegree R w ≤ 2)
    (hregular : ∀ C ∈ F, C ∉ special →
      (∃ a : evenVertices R, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, R.Adj a t → ¬ Even (R.degree t)) ∨
      (∃ a b c : evenVertices R, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices R, C.supp = {a,b,c} ∧
        R.Adj a b ∧ R.Adj b c ∧ R.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)}))
    (hspecial : ∀ C ∈ F, C ∈ special →
      ∃ a b c : evenVertices R, C.supp = {a,b,c} ∧ R.Adj a b ∧
        (P C).image Subtype.val = {(a : V),(b : V)}) :
    ∃ E : Decomposition (J ⊔ (K ∪ L).sup (SimpleGraph.edge u)),
      E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → E.endpointCount t = D.endpointCount t := by
  classical
  have hpriv : ∀ A : Finset V, A ⊆ K ∪ L →
      ∀ E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ w ∈ K \ A, passingNeighborCount E w ≤ 1 := by
    intro A hA E hvec w hw
    obtain ⟨p,hpair⟩ := hprivate w (Finset.mem_sdiff.mp hw).1
    exact delayed_half_star_private_bound R D u x w p (K ∪ L) A hA hu hxS hxu
      hsub hadj hleaves hprofile hmissing
      (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left L (Finset.mem_sdiff.mp hw).1,
        (Finset.mem_sdiff.mp hw).2⟩) hpair hx E hvec
  apply restore_delayed_odd_star_of_packet_gain D u b K L #F #special
    hdis hu hb hodd hstrict hmissing hpositive
  · intro A hA _ E hvec w hw
    obtain ⟨hwS,hwA⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp hwS with hwK | hwL
    · exact (hpriv A hA E hvec w (Finset.mem_sdiff.mpr ⟨hwK,hwA⟩)).trans (by omega)
    · exact ordinary_prepared_half_star_pending_le_two D u w (K ∪ L) A hA hu
        hsub hadj hleaves hprofile hmissing hw (hcap w hwL) E hvec
  · intro A hA _ E hvec
    exact hpriv A hA E hvec
  · intro A hA _ E hvec htight
    have huA : u ∉ A := fun ht => hu (hA ht)
    have hsE : J ⊔ A.sup (SimpleGraph.edge u) ≤ R := by
      apply sup_le hsub
      apply Finset.sup_le
      intro t ht v z hvz
      rw [SimpleGraph.edge_adj] at hvz
      rcases hvz.1 with ⟨hv,hz⟩ | ⟨hv,hz⟩
      · rw [hv,hz]
        exact hadj t (hA ht)
      · rw [hv,hz]
        exact (hadj t (hA ht)).symm
    have hmE : ∀ t ∈ (K ∪ L) \ A,
        ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj t u := by
      intro t ht
      rintro (hj | ha)
      · exact hmissing t (Finset.mem_sdiff.mp ht).1 hj.symm
      · exact (Finset.mem_sdiff.mp ht).2
          ((star_sup_adj_center u A huA t).mp ha.symm)
    rw [hL]
    exact ordinary_prepared_graph_half_star_gain u (K ∪ L) A hu F special P hsupp hPS
      D E hsE (contact_half_star_even_profile R D u (K ∪ L) A hA hleaves hprofile E hvec)
      (fun t ht => hpositive t (Or.inr ht))
      (fun t ht ha => hmissing t ht ha.symm) hmE hvec htight hregular hspecial

end Gallai.TwoException
