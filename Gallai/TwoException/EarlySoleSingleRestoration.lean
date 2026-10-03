/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyWindmillAggregate
public import Gallai.TwoException.EarlyNativeGuards
public import Gallai.TwoException.OrdinaryPreparedHalfStarGain

@[expose] public section

/-! # Complete prepared sole-single early restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _
noncomputable local instance (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- Original packet shapes and restored endpoint reserves suffice to
complete the sole-single early star. Neither numerical packet gains nor
passing-neighbour callbacks are assumptions. -/
theorem bare_prepared_early_sole_single_restoration
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ C) (hfpC : f p ∉ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p)
    (u : V) (K L : Finset V) (O : List (V × V))
    (hK : K = windmillPrivateSet x C)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion Q).image Subtype.val)
    (hdis : Disjoint K L) (hxB : (x : V) ∉ K ∪ L)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hfpB : (f p).val.val ∉ K ∪ L)
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ O, t = e.1)
    (hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp)
    (D : Decomposition (starPuncture G u (K ∪ L)))
    (hh : 0 < D.endpointCount h) (hrec : ∀ e ∈ O, 2 ≤ D.endpointCount e.1)
    (hq : 2 ≤ D.endpointCount (f p).val.val)
    (hround : 0 < D.endpointCount u ∨ Odd #(K ∪ L))
    (hN : 2 ≤ #F) (hepsilon : #special ≤ D.endpointCount u)
    (hregular : ∀ Z ∈ F, Z ∉ special →
      (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        (Q Z).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)}))
    (hspecial : ∀ Z ∈ F, Z ∈ special →
      ∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧ G.Adj a b ∧
        (Q Z).image Subtype.val = {(a : V),(b : V)}) :
    ∃ E : Decomposition G, E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → E.endpointCount t = D.endpointCount t := by
  classical
  have hCB : ∀ r ∈ C, r.val.val ∈ K ∪ L := by
    intro r hr
    apply Finset.mem_union_left
    rw [hK]
    exact (mem_windmillPrivateSet x C _).mpr ⟨r,hr,rfl⟩
  have hpositive := early_prefix_full_neighbourhood_positive u h (K ∪ L) O
    hadj hleaves hcover D hh hrec
  have hcap : ∀ t ∈ K ∪ L, eDegree G t ≤ 2 := by
    intro t ht
    exact bare_nonhub_eDegree_le_two h x ⟨t,hleaves t ht⟩ H
      (fun he => hxB (he ▸ ht))
  apply restore_actual_early_star_of_partition_gains u h p.val.val K L O 1 #F #special
    hdis (hCB p hpC) hadj hleaves hcap hcover D hh hrec hround (by omega)
  intro A hA _ E hvec htight
  have hw := bare_actual_early_sole_single_windmill_gain h x H f hinv hedge
    P C hindex p hpC hfpC hsingle u (K ∪ L) A hA hadj hleaves hCB hfpB D
    (fun r hr => hpositive r.val.val (Or.inr (hCB r hr))) hq E hvec htight
  have ho := ordinary_prepared_half_star_gain u (K ∪ L) A hA hadj hleaves
    F special Q hsupp (by
      intro Z hZ t ht
      apply Finset.mem_union_right
      rw [hL]
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨Z,hZ,ha⟩,rfl⟩)
    D E hvec htight hregular hspecial
  exact ⟨by simpa only [← hK] using hw,by simpa only [← hL] using ho⟩

end Gallai.TwoException
