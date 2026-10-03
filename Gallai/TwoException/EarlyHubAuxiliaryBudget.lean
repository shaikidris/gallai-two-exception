/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateBudget
public import Gallai.TwoException.OrdinaryStarMateBoundary
public import Gallai.TwoException.OrdinarySpecialPacket
public import Gallai.TwoException.ComponentWitnessAssembly

@[expose] public section

/-! # Actual auxiliary budget for mixed hub/private contacts -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubBudgetStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance hubBudgetAux (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Original private and regular/special component labels give the ceiling
auxiliary decomposition exposing h twice. No auxiliary floor is assumed. -/
theorem bare_early_hub_auxiliary_endpoint_of_private_reserves
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hxB : (x : V) ∈ B) (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ B, t = (x : V) ∨ t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 →
      (∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t) ∨ t ∈ privates)
    (hprivateNonempty : privates.Nonempty)
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u →
      t ∈ B ∨ Odd ((ordinaryMatePuncture (starPuncture G u B) M).degree u))
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u B) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  rcases H.counterexample.1 with ⟨hconn,_,hhpos,hhEven,_,_,_⟩
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1)
  have hprofile := ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges
  have hxOdd := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩) x hxB
  have hcap := bare_ordinary_star_mates_cap h x H u B M hxB hadj hleaves
    hdis havoid hedges hcontacts
  have hcentre := ordinary_star_mates_centre_eDegree_le_one h u B M
    hadj hleaves hdis havoid hedges hcontacts
  have hprivate : ∀ t ∈ privates, eDegree J t ≤ 1 := by
    intro t ht
    by_cases htu : J.Adj t u
    · have huOdd := (hprivateContacts t ht (hsub htu)).resolve_left (by
        intro htB
        exact starPuncture_missing G u B huB t htB ((ordinaryMatePuncture_le M) htu).symm)
      apply private_eDegree_le_one_of_odd_hub hsub ?_ x t
        x.property hxOdd (hprivates t ht).1 (hprivates t ht).2
      intro v hv
      rcases hprofile v hv with hv | hv
      · exact hv
      · subst v
        exact False.elim ((Nat.not_even_iff_odd.mpr huOdd) hv)
    · exact private_eDegree_le_one_of_odd_hub_except_centre u x t hsub hprofile
        x.property hxOdd (hprivates t ht).1 (hprivates t ht).2 htu
  have hhub : ∀ K : J.ConnectedComponent, (x : V) ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
    intro K hxK
    obtain ⟨p,hp⟩ := hprivateNonempty
    have hxp := (hprivates p hp).1.symm
    have hxu : (x : V) ≠ u := fun he => huB (he ▸ hxB)
    have hpu : p ≠ u := fun he => hprivateCentre (he ▸ hp)
    have hstar : (starPuncture G u B).Adj x p := by
      refine ⟨hxp,?_⟩
      intro ha
      exact hpu ((star_sup_adj_off_center u B x p hxu).mp ha).2
    have hxpJ := (ordinaryMatePuncture_adj_of_avoids (G := starPuncture G u B)
      M x p (fun e he => ⟨fun eq => (havoid e he).2.2.1 (eq ▸ hxB),
        fun eq => (havoid e he).2.2.2 (eq ▸ hxB)⟩)).mpr hstar
    exact contact_component_floor_of_eDegree_le_one hcap K p
      (K.mem_supp_of_adj_mem_supp hxK hxpJ) (hprivate p hp)
  have hfloor : ∀ K : J.ConnectedComponent,
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
    intro K
    have hordinaryFloor : ∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp →
        (t : V) ∈ K.supp → HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
      intro C hC t htC htK
      rcases hordinary C hC with hc | ⟨a,b,c,hs,ha,hb,hac,hbc,hau,hbu,hcu,hav,hcn⟩
      · exact bare_ordinary_star_mates_component_floor h x H u B M hxB hadj hleaves
          hdis havoid hedges hcontacts C t htC hc K htK
      · have ht : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp := by
          rw [hs] at htC
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
          rcases htC with rfl | rfl | rfl
          · exact Or.inl htK
          · exact Or.inr (Or.inl htK)
          · exact Or.inr (Or.inr htK)
        exact ordinary_special_star_mates_floor u B M hadj hleaves hdis havoid hedges
          C a b c hs ha hb hcn hcap K
          (ordinary_special_witness_in_component u B M a b c hac hbc hau hbu hcu hav K ht)
    obtain ⟨t,htK,ht⟩ := ordinary_star_mates_component_meets_boundary hconn u B M K
    rcases ht with htu | htB | ⟨e,he,hte⟩
    · exact contact_component_floor_of_eDegree_le_one hcap K u (htu ▸ htK) hcentre
    · rcases hB t htB with rfl | hp | ⟨C,hC,v,hv,rfl⟩
      · exact hhub K htK
      · exact contact_component_floor_of_eDegree_le_one hcap K t htK (hprivate t hp)
      · exact hordinaryFloor C hC v hv htK
    · rcases hM e he t hte with ho | hp
      · obtain ⟨C,hC,v,hv,rfl⟩ := ho
        exact hordinaryFloor C hC v hv htK
      · exact contact_component_floor_of_eDegree_le_one hcap K t htK (hprivate t hp)
  have hd : J.degree h = G.degree h := by
    have hm := ordinaryMatePuncture_degree_of_avoids (G := starPuncture G u B) M h hhM
    have hs := starPuncture_degree_other (G := G) u B h hhu hhB
    simp only [← SimpleGraph.ncard_neighborSet] at hm hs ⊢
    exact hm.trans hs
  apply assemble_one_ceiling_of_component_floors J h
  · rw [hd]; exact hhpos
  · rw [hd]; exact hhEven
  · exact hcap
  · intro K _; exact hfloor K

/-- The regular-mate budget is the special case where every contacted
private is deleted in the star and all mate endpoints are ordinary. -/
theorem bare_early_hub_auxiliary_endpoint
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hxB : (x : V) ∈ B) (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ B, t = (x : V) ∨ t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 →
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivateNonempty : privates.Nonempty)
    (hprivateCentre : u ∉ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  exact bare_early_hub_auxiliary_endpoint_of_private_reserves h u x H B privates M F
    hxB hadj hleaves hdis havoid hedges hcontacts hB
    (fun e he t ht => Or.inl (hM e he t ht))
    hprivateNonempty hprivateCentre hprivates
    (fun t ht hadj => Or.inl (hprivateContacts t ht hadj))
    hordinary hhu hhB hhM

end Gallai.TwoException
