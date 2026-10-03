/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryHalfStarProfile
public import Gallai.TwoException.BareOrdinaryDegreeThree
public import Gallai.TwoException.ContactHalfStar

@[expose] public section

/-! # Passing-neighbour bounds for actual pending ordinary spokes -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]

/-- A missing centre edge excludes the sole possible new even vertex.
Every passing neighbour is therefore an original even neighbour. -/
theorem ordinary_pending_passing_le_eDegree
    (D : Decomposition J) (u w : V) (hsub : J ≤ G)
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hmissing : ¬ J.Adj w u) : passingNeighborCount D w ≤ eDegree G w := by
  classical
  apply Finset.card_le_card
  intro t ht
  obtain ⟨hat,hzero⟩ := Finset.mem_filter.mp ht
  have hat' : J.Adj w t := (J.mem_neighborFinset w t).mp hat
  have he : Even (J.degree t) := by
    rw [Nat.even_iff]
    have hm := D.endpointCount_mod_two t
    rw [hzero] at hm
    omega
  rcases hprofile t he with he | rfl
  · exact (mem_evenNeighbors (G := G) w t).mpr ⟨hsub hat',he⟩
  · exact False.elim (hmissing hat')

/-- Ordinary components in the bare kernel have E-degree at most two.
The degree-three exclusion strengthens the original nonexceptional cap. -/
theorem bare_ordinary_eDegree_le_two
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hw : w ∈ C.supp) (hwh : (w : V) ≠ h) :
    eDegree G (w : V) ≤ 2 := by
  have hwx : (w : V) ≠ (x : V) := by
    intro he
    have he' : w = x := Subtype.ext he
    exact hx (he' ▸ hw)
  have hcap := H.counterexample.1.2.2.2.2.2.2 w w.property hwh hwx
  have hthree := bare_ordinary_no_degree_three x w h H C hx hw
  omega

noncomputable local instance pendingBoundHalfAdj (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The actual half-star has at most two passing neighbours at every
pending ordinary leaf, without an assumed intermediate counting bound. -/
theorem bare_ordinary_half_star_pending_le_two
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hw : w ∈ C.supp) (hwh : (w : V) ≠ h)
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpending : (w : V) ∈ B \ A)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u))) :
    passingNeighborCount E w ≤ 2 := by
  classical
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    intro a b hab
    rw [heq] at hab
    exact hab.1
  have hwu : (w : V) ≠ u := by
    intro he
    exact G.irrefl (he ▸ hadj w (Finset.mem_sdiff.mp hpending).1)
  have hmissing : ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj w u := by
    intro ha
    rw [heq] at ha
    exact ha.2 ((star_sup_adj_off_center u (B \ A) w u hwu).mpr ⟨hpending,rfl⟩)
  exact (ordinary_pending_passing_le_eDegree E u w hsub
    (ordinary_half_star_even_preserved u B A hAB hadj hleaves) hmissing).trans
    (bare_ordinary_eDegree_le_two h x w H C hx hw hwh)

noncomputable local instance preparedPendingHalfAdj (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Mate deletions and a restored prefix may precede the half-star.
The original-even profile suffices to bound every pending ordinary leaf;
no exact star-puncture representation of the prepared graph is required. -/
theorem ordinary_prepared_half_star_pending_le_two
    (D : Decomposition J) (u w : V) (S A : Finset V)
    (hAS : A ⊆ S) (huS : u ∉ S)
    (hsub : J ≤ G) (hadj : ∀ t ∈ S, G.Adj u t)
    (hleaves : ∀ t ∈ S, Even (G.degree t))
    (hprofile : ∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u)
    (hmissing : ∀ t ∈ S, ¬ J.Adj u t)
    (hw : w ∈ S \ A) (hcap : eDegree G w ≤ 2)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0) :
    passingNeighborCount E w ≤ 2 := by
  classical
  have huA : u ∉ A := fun ht => huS (hAS ht)
  have hsubE : J ⊔ A.sup (SimpleGraph.edge u) ≤ G := by
    apply sup_le hsub
    apply Finset.sup_le
    intro t ht v z hvz
    rw [SimpleGraph.edge_adj] at hvz
    rcases hvz.1 with ⟨hv,hz⟩ | ⟨hv,hz⟩
    · rw [hv,hz]
      exact hadj t (hAS ht)
    · rw [hv,hz]
      exact (hadj t (hAS ht)).symm
  have hmissingE : ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj w u := by
    rintro (hJ | hA)
    · exact hmissing w (Finset.mem_sdiff.mp hw).1 hJ.symm
    · exact (Finset.mem_sdiff.mp hw).2
        ((star_sup_adj_center u A huA w).mp hA.symm)
  exact (ordinary_pending_passing_le_eDegree E u w hsubE
    (contact_half_star_even_profile G D u S A hAS hleaves hprofile E hvec)
    hmissingE).trans hcap

/-- After the early spoke and ordinary mates have been restored, the graph
is the literal contact-star puncture. Every partial restoration therefore
inherits its pending-leaf bound without endpoint-vector assumptions. -/
theorem actual_contact_half_star_pending_le_two
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hcap : ∀ t ∈ B, eDegree G t ≤ 2)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u))) :
    ∀ w ∈ B \ A, passingNeighborCount E w ≤ 2 := by
  classical
  intro w hw
  have heq := ordinary_half_star_graph u B A hAB hadj
  have hsub : (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)) ≤ G := by
    intro a b hab
    rw [heq] at hab
    exact hab.1
  have hwu : w ≠ u := by
    intro he
    exact G.irrefl (he ▸ hadj w (Finset.mem_sdiff.mp hw).1)
  have hmissing : ¬ (starPuncture G u B ⊔ A.sup (SimpleGraph.edge u)).Adj w u := by
    intro ha
    rw [heq] at ha
    exact ha.2 ((star_sup_adj_off_center u (B \ A) w u hwu).mpr ⟨hw,rfl⟩)
  exact (ordinary_pending_passing_le_eDegree E u w hsub
    (ordinary_half_star_even_preserved u B A hAB hadj hleaves) hmissing).trans
    (hcap w (Finset.mem_sdiff.mp hw).1)

end Gallai.TwoException
