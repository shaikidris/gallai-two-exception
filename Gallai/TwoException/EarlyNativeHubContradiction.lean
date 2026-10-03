/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyNativeHubPreparation
public import Gallai.TwoException.EarlyHubRestoration

@[expose] public section

/-! # Native mixed hub/private minimum-counterexample contradiction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeHubContradictionComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Native original packet labels construct a budgeted preparation and
restore G, contradicting bare minimality. No decomposition is an input. -/
theorem bare_native_early_hub_impossible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (K L privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hxB : (x : V) ∈ (K ∪ L)) (hadj : ∀ t ∈ (K ∪ L), G.Adj u t)
    (hleaves : ∀ t ∈ (K ∪ L), Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ (K ∪ L) ∧ e.2 ∉ (K ∪ L))
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ (K ∪ L) ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ (K ∪ L), t = (x : V) ∨ t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 →
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivateNonempty : privates.Nonempty)
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ (K ∪ L))
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ (K ∪ L) ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ (K ∪ L) ∧ (b : V) ∈ (K ∪ L) ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ (K ∪ L))
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2)
    (huOdd : Odd (G.degree u)) (hEvenB : Even #(K ∪ L))
    (hpacket : ∀ e ∈ M, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ (K ∪ L))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a}) (hpC : p ∈ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p)
    (hK : K = insert (x : V) (windmillPrivateSet x C))
    (special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion Q).image Subtype.val) (hdisKL : Disjoint K L)
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ M, t = e.1)
    (hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp)
    (hN : 2 ≤ #F) (hepsilon : #special ≤ 1)
    (hregular : ∀ Z ∈ F, Z ∉ special →
      (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        (Q Z).image Subtype.val = {(a : V)} ∧ ∃ e ∈ M, e.1 = (b : V)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)}))
    (hspecial : ∀ Z ∈ F, Z ∈ special →
      ∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧ G.Adj a b ∧
        (Q Z).image Subtype.val = {(a : V),(b : V)}) : False := by
  classical
  obtain ⟨D,hs,hh,hu,_,hrec⟩ := bare_native_early_hub_preparation h u x H
    (K ∪ L) privates M F hxB hadj hleaves hdis havoid hedges hcontacts hB hM
    hprivateNonempty hprivateCentre hprivates hprivateContacts hordinary
    hhu hhB hhM huOdd hEvenB hpacket
  have hregularD : ∀ Z ∈ F, Z ∉ special →
      (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        (Q Z).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)}) := by
    intro Z hZ hn
    rcases hregular Z hZ hn with hi | ht | ht
    · exact Or.inl hi
    · obtain ⟨a,b,c,hc,ha,e,he,hb⟩ := ht
      exact Or.inr (Or.inl ⟨a,b,c,hc,ha,hb ▸ hrec e he⟩)
    · exact Or.inr (Or.inr ht)
  obtain ⟨E,he,_,hkeep⟩ := bare_prepared_early_hub_restoration h x H f hedge P C
    hindex p hpC hsingle u K L M hK F special Q hL hdisKL hadj hleaves
    hcover hsupp D (by omega) hrec (Or.inl hu) hN (by omega) hregularD hspecial
  apply H.counterexample.2
  refine ⟨E,?_,?_⟩
  · rw [he]; exact hs
  · rw [hkeep h hhu hhB]; exact hh

end Gallai.TwoException
