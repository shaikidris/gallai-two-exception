/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddStarBoundary
public import Gallai.Structure.ESETAttachment

@[expose] public section

/-! # The actual two-boundary odd-leaf ESET attachment

No ESET witness or attachment neighbourhood is supplied. They are derived
from the puncture component and its second active boundary vertex.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- The SET component together with the centre is an actual induced ESET
when there is a second active boundary vertex besides the odd leaf. -/
theorem odd_star_puncture_attachment_data_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hy : 0 < F.degree y) :
    IsESETAt (G.induce (insert u C.supp)) ⟨u, Set.mem_insert u C.supp⟩ ∧
      (G.induce (insert u C.supp)).spanningCoe.degree u = 2 := by
  classical
  obtain ⟨hu, hi⟩ := odd_star_puncture_set_interface_of_weak_centre
    hle u z hmatch heven hz hdz hcentre ht C hC
  have hs := odd_star_puncture_boundary_subsingleton_of_weak_centre
    hle u z hmatch heven hz hdz hcentre ht C hC hzC
  have hdeleted : ∀ v ∈ C.supp, ∀ w, F.Adj v w → w = u := by
    intro v hv w hvw
    by_cases hvz : v = z
    · subst v
      obtain ⟨a, _, ha⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdz
      exact (ha w hvw).trans (ha u huz.symm).symm
    · exact odd_star_puncture_boundary_spoke_of_weak_centre hle u z hmatch heven hz hdz huz
        hcentre ht C hC hzC v w hv hvz hvw
  let f : ((G \ F).induce C.supp) ≃g G.induce C.supp :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        change G.Adj a.val b.val ↔ G.Adj a.val b.val ∧ ¬ F.Adj a.val b.val
        constructor
        · intro hab
          refine ⟨hab, ?_⟩
          intro hf
          exact hu ((hdeleted a a.property b hf) ▸ b.property)
        · exact And.left }
  have hfy : F.Adj u y := by
    obtain ⟨w, hw⟩ := (F.degree_pos_iff_exists_adj y).mp hy
    have he := hdeleted y hyC w hw
    simpa only [he] using hw.symm
  have hn : ∀ v ∈ C.supp, G.Adj u v ↔ v = y ∨ v = z := by
    intro v hv
    constructor
    · intro huv
      have hf : F.Adj u v := by
        by_contra hf
        exact hu (C.mem_supp_of_adj_mem_supp hv
          (show (G \ F).Adj v u from ⟨huv.symm, fun h => hf h.symm⟩))
      by_cases hvz : v = z
      · exact Or.inr hvz
      · exact Or.inl (hs ⟨hv, hvz, hf.degree_pos_right⟩ ⟨hyC, hyz, hy⟩)
    · rintro (rfl | rfl)
      · exact hle hfy
      · exact hle huz
  have hoy : Odd (((G \ F).induce C.supp).degree ⟨y, hyC⟩) := by
    have hc : (G \ F).neighborSet y ⊆ C.supp :=
      fun _ hw => C.mem_supp_of_adj_mem_supp hyC hw
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hc]
    exact (odd_star_puncture_parity hle u z hmatch heven hz hdz).2.1 y
      (fun he => hu (he ▸ hyC)) hyz hy
  constructor
  · apply isESETAt_induce_insert C.supp u hu (hC.iso f) (f ⟨y, hyC⟩) (f ⟨z, hzC⟩)
      (by rw [f.degree_eq]; exact hoy) (by rw [f.degree_eq]; exact (hi hzC).1)
    exact hn
  · let A := (G.induce (insert u C.supp)).spanningCoe
    have ha : ∀ v, A.Adj u v ↔ v = y ∨ v = z := by
      intro v
      constructor
      · intro hv
        have hgv := G.spanningCoe_induce_le (insert u C.supp) hv
        obtain ⟨a, b, _, _, hb⟩ := (SimpleGraph.map_adj _ _ u v).mp hv
        have hvs : v ∈ insert u C.supp := hb ▸ b.property
        exact (hn v ((Set.mem_insert_iff.mp hvs).resolve_left
          (fun he => hgv.ne he.symm))).mp hgv
      · intro hv
        have hvs : v ∈ C.supp := by rcases hv with rfl | rfl <;> assumption
        exact (SimpleGraph.map_adj (Function.Embedding.subtype _) _ u v).mpr
          ⟨⟨u, Set.mem_insert u C.supp⟩, ⟨v, Set.mem_insert_of_mem u hvs⟩,
            (hn v hvs).mpr hv, rfl, rfl⟩
    have hf : A.neighborFinset u = {y, z} := by
      ext v
      simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        Finset.mem_singleton] using ha v
    change A.degree u = 2
    rw [← A.card_neighborFinset_eq_degree u, hf]
    simp [hyz]

/-- Structural projection of the exact attachment-and-degree interface. -/
theorem odd_star_puncture_attachment_of_weak_centre (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hy : 0 < F.degree y) :
    IsESETAt (G.induce (insert u C.supp)) ⟨u, Set.mem_insert u C.supp⟩ :=
  (odd_star_puncture_attachment_data_of_weak_centre hle u z hmatch heven hz hdz huz
    hcentre ht C hC hzC y hyC hyz hy).1

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_attachment_data (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hy : 0 < F.degree y) :
    IsESETAt (G.induce (insert u C.supp)) ⟨u, Set.mem_insert u C.supp⟩ ∧
      (G.induce (insert u C.supp)).spanningCoe.degree u = 2 := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_attachment_data_of_weak_centre hle u z hmatch heven hz hdz huz hc ht C
    hC hzC y hyC hyz hy

/-- Original-parity compatibility entry point for the generalized odd-leaf argument. -/
theorem odd_star_puncture_attachment (hle : F ≤ G) (u z : V)
    (hmatch : ∀ v, v ≠ u → F.degree v ≤ 1)
    (heven : ∀ v, v ≠ u → v ≠ z → 0 < F.degree v → Even (G.degree v))
    (hz : Odd (G.degree z)) (hdz : F.degree z = 1) (huz : F.Adj u z)
    (hcentre : ∀ v, (G \ F).Adj u v → ¬ Even (G.degree v))
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (C : (G \ F).ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hC : IsSET ((G \ F).induce C.supp)) (hzC : z ∈ C.supp)
    (y : V) (hyC : y ∈ C.supp) (hyz : y ≠ z) (hy : 0 < F.degree y) :
    IsESETAt (G.induce (insert u C.supp)) ⟨u, Set.mem_insert u C.supp⟩ := by
  have hc : ∀ v, (G \ F).Adj u v → v ≠ z → ¬ Even ((G \ F).degree v) := by
    intro v huv hvz hev
    exact hcentre v huv
      ((odd_star_puncture_parity hle u z hmatch heven hz hdz).2.2 v huv.ne.symm hvz hev)
  exact odd_star_puncture_attachment_of_weak_centre hle u z hmatch heven hz hdz huz hc ht C hC
    hzC y hyC hyz hy

end Gallai
