/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.EvenStarPuncture
public import Gallai.Structure.SETRetainedPair

@[expose] public section

/-! # Actual odd-leaf Fan puncture interface

The distinguished leaf loses one edge and changes from odd to even. Every
other active noncentre vertex changes from even to odd. No triangle labels
or component parity witnesses are supplied.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Exact parity interface of a deleted star with one originally odd leaf. -/
theorem odd_star_puncture_parity (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) :
    Even ((G \ F).degree z) ∧
    (∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Odd ((G \ F).degree v)) ∧
    (∀ v, v ≠ u → v ≠ z → Even ((G \ F).degree v) → Even (G.degree v)) := by
  have ho : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Odd ((G \ F).degree v) := by
    intro v hv hvz hp
    have hd := degree_sdiff_add_of_le hle v
    have hm := hmatch v hv
    have he := heven v hv hvz hp
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  refine ⟨?_, ho, ?_⟩
  · have hd := degree_sdiff_add_of_le hle z
    rw [Nat.odd_iff] at hz
    rw [Nat.even_iff]
    omega
  · intro v hv hvz he
    by_cases hp : 0 < F.degree v
    · exact False.elim ((Nat.not_even_iff_odd.mpr (ho v hv hvz hp)) he)
    have hd := degree_sdiff_add_of_le hle v
    have hzv : F.degree v = 0 := by omega
    simp only [hzv, Nat.add_zero] at hd
    rwa [← hd]

/-- A SET component in an actual odd-leaf puncture excludes the centre.
If it contains the distinguished leaf, its other promoted odd vertices form
a subsingleton, with the retained triangle labels derived internally. -/
theorem odd_star_puncture_set_interface_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) :
    u ∉ C.supp ∧ ∀ hzC : z ∈ C.supp,
      Even (((G \ F).induce C.supp).degree ⟨z, hzC⟩) ∧
      Set.Subsingleton {v : C.supp |
        Odd (((G \ F).induce C.supp).degree v) ∧ Even (G.degree v)} := by
  classical
  obtain ⟨hze, _, hk⟩ := odd_star_puncture_parity hle u z hmatch heven hz hdz
  have hc : ∀ v ∈ C.supp, (G \ F).neighborSet v ⊆ C.supp :=
    fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw
  have hu : u ∉ C.supp := by
    intro hu
    by_cases hzC : z ∈ C.supp
    · obtain ⟨v, huv, hev, hvz⟩ := hC.even_neighbor_ne ⟨u, hu⟩ ⟨z, hzC⟩
      rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at hev
      exact hcentre v huv (fun hh => hvz (Subtype.ext hh)) hev
    · obtain ⟨v, huv, hev, _⟩ := hC.even_neighbor_ne ⟨u, hu⟩ ⟨u, hu⟩
      rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at hev
      exact hcentre v huv (fun hh => hzC (hh ▸ v.property)) hev
  refine ⟨hu, ?_⟩
  intro hzC
  have hez : Even (((G \ F).induce C.supp).degree ⟨z, hzC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc z hzC)]
    exact hze
  refine ⟨hez, ?_⟩
  apply hC.promoted_odd_except_one_subsingleton (G := G) (Function.Embedding.subtype _)
    (fun {_ _} hh => hh.1) ht ⟨z, hzC⟩ hez
  intro v hv he
  rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc v v.property)] at he
  exact hk v (fun hh => hu (hh ▸ v.property)) (fun hh => hv (Subtype.ext hh)) he

/-- Apart from the distinguished leaf, at most one endpoint of a removed
edge lies in the SET component. This is the actual deleted-edge boundary,
not a separately supplied promoted-vertex set. -/
theorem odd_star_puncture_boundary_subsingleton_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp) :
    Set.Subsingleton {v | v ∈ C.supp ∧ v ≠ z ∧ 0 < F.degree v} := by
  obtain ⟨hu, hi⟩ := odd_star_puncture_set_interface_of_weak_centre
    hle u z hmatch heven hz hdz hcentre ht C hC
  have hs := (hi hzC).2
  have ho := (odd_star_puncture_parity hle u z hmatch heven hz hdz).2.1
  have hp (v : V) (hv : v ∈ C.supp) (hvz : v ≠ z) (hd : 0 < F.degree v) :
      Odd (((G \ F).induce C.supp).degree ⟨v, hv⟩) ∧ Even (G.degree v) := by
    have hvu : v ≠ u := fun hh => hu (hh ▸ hv)
    refine ⟨?_, heven v hvu hvz hd⟩
    have hclosed : (G \ F).neighborSet v ⊆ C.supp :=
      fun _ hw => C.mem_supp_of_adj_mem_supp hv hw
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hclosed]
    exact ho v hvu hvz hd
  intro v hv w hw
  exact congrArg Subtype.val (hs (hp v hv.1 hv.2.1 hv.2.2) (hp w hw.1 hw.2.1 hw.2.2))

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_set_interface (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) :
    u ∉ C.supp ∧ ∀ hzC : z ∈ C.supp,
      Even (((G \ F).induce C.supp).degree ⟨z, hzC⟩) ∧
      Set.Subsingleton {v : C.supp |
        Odd (((G \ F).induce C.supp).degree v) ∧ Even (G.degree v)} := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_set_interface_of_weak_centre hle u z hmatch heven hz hdz hc ht C hC

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_boundary_subsingleton (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp) :
    Set.Subsingleton {v | v ∈ C.supp ∧ v ≠ z ∧ 0 < F.degree v} := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_boundary_subsingleton_of_weak_centre hle u z hmatch heven hz hdz hc ht
    C hC hzC

end Gallai
