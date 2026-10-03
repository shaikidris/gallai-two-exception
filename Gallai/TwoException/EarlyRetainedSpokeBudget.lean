/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySingleSpokeBudget
public import Gallai.TwoException.EarlyRetainedSpokeProfile

@[expose] public section

/-! # Component budget with a retained spoke recipient -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Packet coverage and component witnesses supply a protected endpoint
budget when the unpaid private mate is outside the deleted contact star,
including when its contact to the centre remains present. -/
theorem bare_early_retained_spoke_auxiliary_endpoint
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
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = q ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B ∨ t = q)
    (hordinarySeparated : ∀ C ∈ F, ∀ t : evenVertices G,
      t ∈ C.supp → (t : V) ≠ x ∧ (t : V) ≠ q)
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ x) (hhq : h ≠ q)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∃ D : Decomposition J, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  rcases H.counterexample.1 with ⟨hconn, _, hhpos, hhEven, hxEven, _, _⟩
  have hprofile := early_single_spoke_even_profile u x q B M hleaves hxEven
    hqEven (fun e he => ⟨(hedges e he).2.1, (hedges e he).2.2⟩)
  have hc := bare_early_retained_spoke_mates_cap h x H u q B M
    hadj hleaves hxB hqB hxu hqu hxq hqEven hdis havoid hedges hcontacts
  have hcap := hc.1
  have hcentre := hc.2.1
  have hxOdd := hc.2.2
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1.1)
  have hd := delayed_auxiliary_protected_degree (G := G) u x q h B M hhu hhB hhx hhq hhM
  have hpetal : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2 ∧
      p ≠ e.1 ∧ p ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2 := by
    intro e he
    have ha := havoid e he
    exact ⟨ha.2.2.2.2.1.symm, ha.2.2.2.2.2.1.symm,
      fun ht => ha.2.2.1 (ht ▸ hpB), fun ht => ha.2.2.2.1 (ht ▸ hpB),
      ha.2.2.2.2.2.2.1.symm, ha.2.2.2.2.2.2.2.symm⟩
  apply assemble_one_ceiling_of_component_floors J h
  · rw [hd]; exact hhpos
  · rw [hd]; exact hhEven
  · exact hcap
  · intro K _
    rcases delayed_auxiliary_component_contact hconn u x q B privates M F hB hM K with
      huK | hspoke | ⟨t, ht, htK⟩ | ⟨C, hC, t, htC, htK⟩
    · exact contact_component_floor_of_eDegree_le_one hcap K u huK hcentre
    · exact early_spoke_petal_component_floor u x p q B M huB hpB hxu
        (fun ht => huB (ht ▸ hpB)) hqu
        hxp hpq hpqne hxEven hpdegree hpetal hprofile hxOdd hcap K
        (hspoke.elim Or.inl (fun hqK => Or.inr (Or.inl hqK)))
    · by_cases htq : t = q
      · subst t
        exact early_spoke_petal_component_floor u x p q B M huB hpB hxu
          (fun ht => huB (ht ▸ hpB)) hqu
          hxp hpq hpqne hxEven hpdegree hpetal hprofile hxOdd hcap K
          (Or.inr (Or.inl htK))
      · have htu : ¬ J.Adj t u := by
          intro ha
          rcases hprivateContacts t ht (hsub ha) with htB | he
          · have haD := (ordinaryMatePuncture_le M) ha
            exact starPuncture_missing G u B huB t htB haD.1.symm
          · exact htq he
        apply contact_component_floor_of_eDegree_le_one hcap K t htK
        exact private_eDegree_le_one_of_odd_hub_except_centre u x t hsub hprofile
          hxEven hxOdd (hprivates t ht).1 (hprivates t ht).2 htu
    · have hxsep := fun v hv => (hordinarySeparated C hC v hv).1
      have hqsep := fun v hv => (hordinarySeparated C hC v hv).2
      rcases hordinary C hC with hregular | ⟨a, b, c, hs, ha, hb, hac, hbc,
        hau, hbu, hcu, hcAvoid, hcNonadj⟩
      · exact early_regular_packet_component_floor u x q B M hadj hleaves hdis
          havoid hedges C t htC hxsep hqsep hregular hprofile hcap K htK
      · have haC : a ∈ C.supp := by rw [hs]; simp
        have hbC : b ∈ C.supp := by rw [hs]; simp
        have hcC : c ∈ C.supp := by rw [hs]; simp
        have hcontact : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp := by
          rw [hs] at htC
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htC
          rcases htC with rfl | rfl | rfl
          · exact Or.inl htK
          · exact Or.inr (Or.inl htK)
          · exact Or.inr (Or.inr htK)
        exact early_special_packet_component_floor u x q B M hadj
          (fun e he => ⟨(havoid e he).2.2.1, (havoid e he).2.2.2.1⟩)
          C a b c hs ha hb hac hbc hau hbu hcu (hxsep a haC) (hxsep b hbC)
          (hqsep a haC) (hqsep b hbC) (hxsep c hcC) (hqsep c hcC)
          hcAvoid hcNonadj hprofile hcap K hcontact


end Gallai.TwoException
