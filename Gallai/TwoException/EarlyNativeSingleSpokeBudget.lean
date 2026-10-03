/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyMixedComponentCoverage

@[expose] public section

/-! # Actual single-spoke budget from native mixed component data -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeBudgetComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance nativeBudgetStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance nativeBudgetAux (u x q : V) (B : Finset V)
    (M : List (V × V)) : DecidableRel
      (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Native mixed packets supply the auxiliary component alternatives;
no component-floor or auxiliary decomposition certificate is assumed. -/
theorem bare_native_early_single_spoke_auxiliary_endpoint
    (h u x p q : V) (H : BareMinimalCounterexample G h x)
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∉ B) (hxB : x ∉ B)
    (hqu : q ≠ u) (hqEven : Even (G.degree q))
    (hxu : x ≠ u) (hpx : p ≠ x) (hpqne : p ≠ q)
    (hxq : G.Adj x q) (hxp : G.Adj x p) (hpq : G.Adj p q)
    (hpdegree : eDegree G p = 2)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (huOdd : Odd (G.degree u)) (S : Finset (evenVertices G))
    (special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hMdef : M = ((F \ special).toList.flatMap mates).map
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
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∃ D : Decomposition J, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  rcases H.counterexample.1 with ⟨_,_,_,_,hxEven,_,_⟩
  let xe : evenVertices G := ⟨x,hxEven⟩
  let qe : evenVertices G := ⟨q,hqEven⟩
  have hxC : ∀ C ∈ F, xe ∉ C.supp := by
    intro C hC hx
    exact hxComponents C hC xe hx rfl
  obtain ⟨hseparated,hcomponents⟩ :=
    early_mixed_auxiliary_component_guards u huOdd xe qe hxq B S F special Q mates M
      hMdef hxC hselected hfull hregular hmates hspecial
  exact bare_early_single_spoke_auxiliary_endpoint h u x p q H B privates M F
    hadj hleaves hpB hqB hxB hqu hqEven hxu hpx hpqne hxq hxp hpq hpdegree
    hpair hdis havoid hedges hcontacts hB hM hprivates hprivateContacts
    hseparated hcomponents hhu hhB hhx hhq hhM

end Gallai.TwoException
