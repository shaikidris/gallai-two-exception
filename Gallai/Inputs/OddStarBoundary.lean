/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddStarPuncture

@[expose] public section

/-! # The second odd-leaf boundary is a centre spoke

The retained even pair determines all original even neighbours of a promoted
boundary vertex. Neither retained vertex can be incident with a deleted edge.
Thus the boundary cannot belong to a separate deleted matching edge.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Every removed edge at a nondistinguished vertex of the odd-leaf SET
component is a spoke to the centre. No attachment edge is assumed. -/
theorem odd_star_puncture_boundary_spoke_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y t : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hyt : F.Adj y t) : t = u := by
  classical
  obtain ⟨hu, hi⟩ := odd_star_puncture_set_interface_of_weak_centre
    hle u z hmatch heven hz hdz hcentre ht C hC
  obtain ⟨_, ho, hk⟩ := odd_star_puncture_parity hle u z hmatch heven hz hdz
  have hyu : y ≠ u := fun he => hu (he ▸ hyC)
  have hd (v : C.supp) : ((G \ F).induce C.supp).degree v = (G \ F).degree v := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    exact fun _ hw => C.mem_supp_of_adj_mem_supp v.property hw
  have hkeep (v : C.supp) (hvz : v ≠ ⟨z, hzC⟩)
      (hv : Even (((G \ F).induce C.supp).degree v)) : Even (G.degree v) :=
    hk v (fun he => hu (he ▸ v.property))
      (fun he => hvz (Subtype.ext he)) (by rwa [hd] at hv)
  obtain ⟨a, b, hab, haz, hbz, ha, hb, hcover⟩ := hC.even_pair_away ⟨z, hzC⟩ (hi hzC).1
  have hpair := hC.promoted_odd_completes_pair (G := G) (Function.Embedding.subtype _)
    (fun {_ _} hh => hh.1) ht ⟨z, hzC⟩ a b ha hb hab hcover
    (hkeep a haz ha) (hkeep b hbz hb) ⟨y, hyC⟩
    (by rw [hd]; exact ho y hyu hyz hyt.degree_pos_left)
    (heven y hyu hyz hyt.degree_pos_left)
  by_contra htu
  have htz : t ≠ z := by
    intro he
    subst t
    obtain ⟨v, _, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdz
    exact hyu ((huniq y hyt.symm).trans (huniq u huz.symm).symm)
  have hgt := heven t htu htz hyt.degree_pos_right
  have het : Even ((G \ F).degree t) := by
    rcases hpair.2.2 t hgt (hle hyt) with he | he
    · rw [he]
      change Even ((G \ F).degree a.val)
      rwa [← hd a]
    · rw [he]
      change Even ((G \ F).degree b.val)
      rwa [← hd b]
  exact (Nat.not_even_iff_odd.mpr (ho t htu htz hyt.degree_pos_right)) het

/-- The original neighbourhood of this puncture component meets its exterior
only at the centre. This includes the distinguished leaf's deleted edge. -/
theorem odd_star_puncture_neighborhood_subset_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp) :
    ∀ v ∈ C.supp, G.neighborSet v ⊆ insert u C.supp := by
  intro v hv w hw
  by_cases hf : F.Adj v w
  · apply Set.mem_insert_iff.mpr
    left
    by_cases hvz : v = z
    · subst v
      obtain ⟨a, _, ha⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdz
      exact (ha w hf).trans (ha u huz.symm).symm
    · exact odd_star_puncture_boundary_spoke_of_weak_centre hle u z hmatch heven hz hdz huz
        hcentre ht C hC hzC v w hv hvz hf
  · exact Set.mem_insert_of_mem u (C.mem_supp_of_adj_mem_supp hv ⟨hw, hf⟩)

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_boundary_spoke (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y t : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hyt : F.Adj y t) : t = u := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_boundary_spoke_of_weak_centre hle u z hmatch heven hz hdz huz hc ht C
    hC hzC y t hyC hyz hyt

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_neighborhood_subset (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp) :
    ∀ v ∈ C.supp, G.neighborSet v ⊆ insert u C.supp := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_neighborhood_subset_of_weak_centre hle u z hmatch heven hz hdz huz hc
    ht C hC hzC

end Gallai
