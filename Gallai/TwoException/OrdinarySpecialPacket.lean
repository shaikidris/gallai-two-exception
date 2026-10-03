/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPacketCoverage
public import Gallai.TwoException.OrdinaryStarMateProfile

@[expose] public section

/-! # Boundary witness for the special two-contact triangle -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
noncomputable local instance specialCombinedAdj (u : V) (B : Finset V)
    (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- In the special T2 packet, the two contact vertices are odd and the
third vertex is not adjacent to the newly even centre. Thus its E-degree
is zero, although it need not become odd itself. -/
theorem ordinary_special_triangle_eDegree_zero
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (u : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (haOdd : Odd (J.degree a)) (hbOdd : Odd (J.degree b))
    (hcu : ¬ J.Adj c u) : eDegree J c = 0 := by
  classical
  have hcC : c ∈ C.supp := by rw [hsupp]; simp
  have hempty : evenNeighbors J c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨hct, htEven⟩ := (mem_evenNeighbors (G := J) c t).mp ht
    rcases hprofile t htEven with htOriginal | htu
    · let te : evenVertices G := ⟨t, htOriginal⟩
      have htC : te ∈ C.supp := C.mem_supp_of_adj_mem_supp hcC (hsub hct)
      rw [hsupp] at htC
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htC
      rcases htC with hta | htb | htc
      · have he : t = (a : V) := congrArg Subtype.val hta
        rw [he] at htEven
        rw [Nat.even_iff] at htEven
        rw [Nat.odd_iff] at haOdd
        omega
      · have he : t = (b : V) := congrArg Subtype.val htb
        rw [he] at htEven
        rw [Nat.even_iff] at htEven
        rw [Nat.odd_iff] at hbOdd
        omega
      · have he : t = (c : V) := congrArg Subtype.val htc
        rw [he] at hct
        exact J.irrefl hct
    · subst t
      exact hcu hct
  simp only [eDegree, hempty, Finset.card_empty]

/-- The special packet supplies the same component floor as regular
packets, through its retained isolated even vertex instead of all-odd parity. -/
theorem ordinary_special_triangle_component_floor
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a, b, c}) (u : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (haOdd : Odd (J.degree a)) (hbOdd : Odd (J.degree b))
    (hcu : ¬ J.Adj c u)
    (hcap : ∀ t, Even (J.degree t) → eDegree J t ≤ 3)
    (K : J.ConnectedComponent) (hcK : (c : V) ∈ K.supp) :
    HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  apply contact_component_floor_of_eDegree_le_one hcap K c hcK
  rw [ordinary_special_triangle_eDegree_zero C a b c hsupp u hsub hprofile
    haOdd hbOdd hcu]
  omega

/-- The special triangle's witness is derived in the simultaneous puncture,
not assumed as an auxiliary parity profile. Its two selected contacts become
odd, while the third vertex cannot see the only newly even vertex. -/
theorem ordinary_special_star_mates_floor
    (u : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c}) (ha : (a : V) ∈ B) (hb : (b : V) ∈ B)
    (hcu : ¬ G.Adj c u)
    (hcap : ∀ t, Even ((ordinaryMatePuncture (starPuncture G u B) M).degree t) →
      eDegree (ordinaryMatePuncture (starPuncture G u B) M) t ≤ 3)
    (K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent)
    (hcK : (c : V) ∈ K.supp) :
    HasPathBudget ((ordinaryMatePuncture (starPuncture G u B) M).induce K.supp)
      (Fintype.card K.supp / 2) := by
  classical
  have hsubM : ∀ L : List (V × V), ordinaryMatePuncture (starPuncture G u B) L ≤ G := by
    intro L
    induction L with
    | nil => exact fun _ _ ha => ha.1
    | cons e L ih => exact fun _ _ ha => ih ha.1
  have hp := ordinary_star_mates_even_preserved u B M hadj hleaves hdis havoid hedges
  have hl := ordinary_star_mates_leaves_odd u B M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  exact ordinary_special_triangle_component_floor C a b c hsupp u (hsubM M) hp
    (hl a ha) (hl b hb) (fun hc => hcu (hsubM M hc)) hcap K hcK

/-- A special triangle is not split by the preparation: star deletion
touches only the centre, and the triangle has no deleted mate. Thus a
component meeting either contact also contains the third-vertex witness. -/
theorem ordinary_special_witness_in_component
    (u : V) (B : Finset V) (M : List (V × V)) (a b c : V)
    (hac : G.Adj a c) (hbc : G.Adj b c)
    (hau : a ≠ u) (hbu : b ≠ u) (hcu : c ≠ u)
    (havoid : ∀ e ∈ M, c ≠ e.1 ∧ c ≠ e.2)
    (K : (ordinaryMatePuncture (starPuncture G u B) M).ConnectedComponent)
    (hcontact : a ∈ K.supp ∨ b ∈ K.supp ∨ c ∈ K.supp) : c ∈ K.supp := by
  classical
  have hca : (starPuncture G u B).Adj c a := by
    refine ⟨hac.symm,?_⟩
    intro ha
    have he := (star_sup_adj_off_center u B c a hcu).mp ha
    exact hau he.2
  have hcb : (starPuncture G u B).Adj c b := by
    refine ⟨hbc.symm,?_⟩
    intro hb
    have he := (star_sup_adj_off_center u B c b hcu).mp hb
    exact hbu he.2
  have hcaJ := (ordinaryMatePuncture_adj_of_avoids
    (G := starPuncture G u B) M c a havoid).mpr hca
  have hcbJ := (ordinaryMatePuncture_adj_of_avoids
    (G := starPuncture G u B) M c b havoid).mpr hcb
  rcases hcontact with ha | hb | hc
  · exact K.mem_supp_of_adj_mem_supp ha hcaJ.symm
  · exact K.mem_supp_of_adj_mem_supp hb hcbJ.symm
  · exact hc

end Gallai.TwoException
