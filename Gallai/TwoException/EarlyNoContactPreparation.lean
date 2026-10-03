/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySingleSpokePreparation

@[expose] public section

/-! # Early spoke preparation with noncontact ordinary recipients -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance noContactPreparationStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance noContactPreparationAux (u x q : V)
    (B : Finset V) (O : List (V × V)) : DecidableRel
      (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) O).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Noncontact ordinary recipients replace the positive-centre requirement.
Spoke and mate preparation therefore works without even cardinality of the
deletion star. This produces the reserves needed for the odd-star branch. -/
theorem prepare_early_single_spoke_noncontact
    (u x q h : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∉ B) (hxu : x ≠ u) (hqu : q ≠ u) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hqEven : Even (G.degree q))
    (hdis : (O ++ []).Pairwise (fun (e f : V × V) =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (O ++ []),
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ (O ++ []), G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hxAvoid : ∀ e ∈ (O ++ []), x ≠ e.1 ∧ x ≠ e.2)
    (hqAvoid : ∀ e ∈ (O ++ []), q ≠ e.1 ∧ q ≠ e.2)
    (hhAvoid : ∀ e ∈ (O ++ []), h ≠ e.1 ∧ h ≠ e.2)
    (hhx : x ≠ h) (hhq : q ≠ h)
    (hpacket : ∀ e ∈ (O ++ []), ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (hnoncontact : ∀ e ∈ (O ++ []), ¬ G.Adj e.1 u)
    (D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])))
    (hxOdd : Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])).degree x))
    (hzero : eDegree (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ [])) q = 0)
    (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition (starPuncture G u B), E.size = D.size ∧
      2 ≤ E.endpointCount h ∧ 2 ≤ E.endpointCount q ∧
      (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ (O ++ []), 2 ≤ E.endpointCount e.1) := by
  classical
  have hgraph := early_spoke_restored_graph u x q B (O ++ []) hxu hqu hxq hxAvoid
  have hspoke := restore_early_double_spoke u x q B (O ++ []) hadj hleaves hxB
    hxq.ne.symm (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
    D hxOdd hzero
  rw [hgraph] at hspoke
  obtain ⟨D1,hs1,hpos1,htransfer⟩ := hspoke
  obtain ⟨E,hs,_,hrec,hkeep⟩ := restore_ordinary_mate_family u B hadj hleaves
    (O ++ []) hdis havoid hedges hpacket D1 (Or.inr hnoncontact)
  have hqh : 2 ≤ E.endpointCount q := by
    apply early_single_prefix_recipient_surplus u x q B (O ++ [])
      hxu hqu hqB hxq hqEven hqAvoid D E
    rw [hkeep q hqAvoid]
    exact htransfer q
  have hhh := htransfer h
  simp only [hhx,hhq,ite_false,Nat.add_zero] at hhh
  refine ⟨E,hs.trans hs1,?_,hqh,?_,hrec⟩
  · rw [hkeep h hhAvoid,hhh]
    exact hh
  · intro t ht
    rw [hkeep t (fun e he => ?_)]
    · exact hpos1 t ht
    · have ha := havoid e he
      exact ⟨fun heq => ha.2.2.1 (heq ▸ ht),
        fun heq => ha.2.2.2 (heq ▸ ht)⟩

end Gallai.TwoException
