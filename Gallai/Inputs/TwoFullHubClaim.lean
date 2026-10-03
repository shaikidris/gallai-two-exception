/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleClaim
public import Gallai.Inputs.TwoTriangleFullFullRestore

@[expose] public section

/-! # Adjacent odd hubs cannot link distinct even components in a counterexample -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Claim 10 in both orientations and full/full restoration exclude adjacent
odd hubs touching distinct even components. Every local input is derived. -/
theorem minimal_counterexample_adjacent_odd_components_eq
    (u v : V) (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C E : (evenSubgraph G).ConnectedComponent)
    (htC : ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj u w)
    (htE : ∃ w : evenVertices G, w ∈ E.supp ∧ G.Adj v w) : C = E := by
  classical
  by_contra hCE
  have hfullV := minimal_counterexample_distinct_triangle_neighbor_full
    u v hu hv huv hconn hcap hnot hset hmin C E hCE htC htE
  have hfullU := minimal_counterexample_distinct_triangle_neighbor_full
    v u hv hu huv.symm hconn hcap hnot hset hmin E C (Ne.symm hCE) htE htC
  obtain ⟨a, b, c, hab, hac, hbc, hmC, _, _, _, hua, hub, hNu, hlocalU⟩ :=
    minimal_counterexample_triangle_labels u hu hconn hcap hnot hset hmin C htC
  obtain ⟨d, e, z, hde, hdz, hez, hmE, _, _, _, hvd, hve, hNv, hlocalV⟩ :=
    minimal_counterexample_triangle_labels v hv hconn hcap hnot hset hmin E htE
  have haC : a ∈ C.supp := (hmC a).mpr (Or.inl rfl)
  have hbC : b ∈ C.supp := (hmC b).mpr (Or.inr (Or.inl rfl))
  have hcC : c ∈ C.supp := (hmC c).mpr (Or.inr (Or.inr rfl))
  have hdE : d ∈ E.supp := (hmE d).mpr (Or.inl rfl)
  have heE : e ∈ E.supp := (hmE e).mpr (Or.inr (Or.inl rfl))
  have hzE : z ∈ E.supp := (hmE z).mpr (Or.inr (Or.inr rfl))
  have hcross (p q : evenVertices G) (hp : p ∈ C.supp) (hq : q ∈ E.supp) : p ≠ q := by
    intro h
    apply hCE
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hp (h.symm ▸ hq)
  have hlistEven : [a, b, c, d, e, z].Nodup := by
    simp [hab, hac, hbc, hde, hdz, hez,
      hcross a d haC hdE, hcross a e haC heE, hcross a z haC hzE,
      hcross b d hbC hdE, hcross b e hbC heE, hcross b z hbC hzE,
      hcross c d hcC hdE, hcross c e hcC heE, hcross c z hcC hzE]
  have hlistVal : [(a : V), (b : V), (c : V), (d : V), (e : V), (z : V)].Nodup :=
    hlistEven.map Subtype.val_injective
  let l : List V := [u, v, (a : V), (b : V), (c : V), (d : V), (e : V), (z : V)]
  have hl : l.Nodup := by
    change (u :: v :: [(a : V), (b : V), (c : V), (d : V), (e : V), (z : V)]).Nodup
    rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hlistVal⟩
    · simp [huv.ne, ComponentDeletionChoice.hub_ne_even hu]
    · simp [ComponentDeletionChoice.hub_ne_even hv]
  let f : Fin 8 ↪ V := ⟨l.get, List.nodup_iff_injective_get.mp hl⟩
  have hfEven (i : Fin 8) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : Even (G.degree (f i)) := by
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · exact a.property
    · exact b.property
    · exact c.property
    · exact d.property
    · exact e.property
    · exact z.property
  have hS : evenNeighbors G (f 0) = {f 2, f 3, f 4} := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors (f 0) w).mp hw
      exact hNu w ha he
    · rintro (rfl | rfl | rfl)
      · exact (mem_evenNeighbors u a).mpr ⟨hua, a.property⟩
      · exact (mem_evenNeighbors u b).mpr ⟨hub, b.property⟩
      · exact (mem_evenNeighbors u c).mpr ⟨hfullU c hcC, c.property⟩
  have hT : evenNeighbors G (f 1) = {f 5, f 6, f 7} := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      obtain ⟨ha, he⟩ := (mem_evenNeighbors (f 1) w).mp hw
      exact hNv w ha he
    · rintro (rfl | rfl | rfl)
      · exact (mem_evenNeighbors v d).mpr ⟨hvd, d.property⟩
      · exact (mem_evenNeighbors v e).mpr ⟨hve, e.property⟩
      · exact (mem_evenNeighbors v z).mpr ⟨hfullV z hzE, z.property⟩
  have hle : twoTriangleDeletion true true f ≤ G := by
    rw [twoTriangleDeletion_full_split, ← hS, ← hT]
    have hstar (w : V) : (evenNeighbors G w).sup (SimpleGraph.edge w) ≤ G := by
      apply Finset.sup_le
      intro t ht
      exact (SimpleGraph.edge_le_iff G).mpr (Or.inr ((mem_evenNeighbors w t).mp ht).1)
    exact sup_le (sup_le ((SimpleGraph.edge_le_iff G).mpr (Or.inr huv)) (hstar u)) (hstar v)
  have hcapU : ∀ w ∈ evenNeighbors G (f 0), eDegree G w ≤ 2 := by
    rw [hS]
    exact hlocalU
  have hcapV : ∀ w ∈ evenNeighbors G (f 1), eDegree G w ≤ 2 := by
    rw [hT]
    exact hlocalV
  obtain ⟨D, hD⟩ := two_triangle_deletion_floor true true f hle hu hv hfEven
    hconn hcap hnot hset hmin
  obtain ⟨P, hP, _⟩ := D.restore_two_triangle_full_full f hu hv huv hS hT hcapU hcapV
  exact hnot ⟨P, hP.le.trans hD⟩

end Gallai
