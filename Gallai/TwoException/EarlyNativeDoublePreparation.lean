/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyNativeDoubleSpokeBudget
public import Gallai.TwoException.EarlyDoubleSpokePreparation

@[expose] public section

/-! # Actual native double-spoke budget followed by preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeDoublePreparationComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance nativeDoublePreparationStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- Construct the protected auxiliary decomposition and pay its spoke and
ordinary prefix, deriving the odd donor and zero-E-degree recipient guards for a double petal. -/
theorem bare_native_early_double_spoke_preparation
    (h u x p q : V) (H : BareMinimalCounterexample G h x)
    (B privates : Finset V) (O : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∈ B) (hxB : x ∉ B)
    (hqu : q ≠ u)
    (hxu : x ≠ u) (hpx : p ≠ x) (hpqne : p ≠ q)
    (hxq : G.Adj x q) (hxp : G.Adj x p) (hpq : G.Adj p q)
    (hpdegree : eDegree G p = 2)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (hdis : (O ++ []).Pairwise (fun (e f : V × V) =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (O ++ []),
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ (O ++ []), G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ (O ++ []), t = e.1 ∨ t = e.2) ∨ t = x ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ (O ++ []), ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (huOdd : Odd (G.degree u)) (S : Finset (evenVertices G))
    (special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hMdef : (O ++ []) = ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V))))
    (hxComponents : ∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp → (t : V) ≠ x)
    (hselected : ∀ C ∈ F, ∀ t ∈ Q C, (t : V) ∈ B)
    (hfull : ∀ C ∈ special, Q C = ordinaryComponentPacket G S C)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ Q C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hmates : ∀ C ∈ F, C ∉ special → ∀ e ∈ mates C,
      e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hspecial : ∀ C ∈ special, ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S C = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ x) (hhq : h ≠ q)
    (hhM : ∀ e ∈ (O ++ []), h ≠ e.1 ∧ h ≠ e.2)
    (hEvenB : Even #B)
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B) :
    ∃ E : Decomposition (starPuncture G u B),
      E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
      0 < E.endpointCount u ∧
      (∀ t ∈ B, 0 < E.endpointCount t) ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) := by
  classical
  obtain ⟨D,hs,hh⟩ :=
    bare_native_early_double_spoke_auxiliary_endpoint h u x p q H B privates
      (O ++ []) F hadj hleaves hpB hqB hxB hxu hpx hpqne
      hxq hxp hpq hpdegree hpair hdis havoid hedges hcontacts hB hM
      hprivates hprivateContacts huOdd S special Q mates hMdef hxComponents
      hselected hfull hregular hmates hspecial hhu hhB hhx hhq hhM
  rcases H.counterexample.1 with ⟨_,_,_,_,hxEven,_,_⟩
  have hpProfile := early_double_spoke_mates_profile u x p q B (O ++ [])
    hadj hleaves hpB hqB hxB hxu hpx hpqne hxq hxEven hpair hdis havoid hedges
  have havO : ∀ e ∈ O,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B := by
    intro e he
    have ha := havoid e (List.mem_append_left [] he)
    exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1⟩
  have hxO : ∀ e ∈ O, x ≠ e.1 ∧ x ≠ e.2 := by
    intro e he
    have ha := havoid e (List.mem_append_left [] he)
    exact ⟨ha.2.2.2.2.1.symm,ha.2.2.2.2.2.1.symm⟩
  obtain ⟨E,he,hhE,huE,hpos,hrec⟩ :=
    prepare_early_double_spoke u x q h B O hadj hleaves huOdd hEvenB
      hxB hxu hqu hxq (by simpa using hdis) havO
      (fun e he => hedges e (List.mem_append_left [] he)) hxO
      (fun e he => hhM e (List.mem_append_left [] he)) hhx.symm hhq.symm
      hpacket D hpProfile.2.1 hpProfile.2.2.2.2 hh
  exact ⟨E,he.symm ▸ hs,hhE,huE,hpos,hrec⟩

end Gallai.TwoException
