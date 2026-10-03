/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoTriangleLabels
public import Gallai.Inputs.TwoTriangleFullRestore
public import Gallai.Inputs.TwoTrianglePartialRestore

@[expose] public section

/-! # Claim 10: adjacent odd hubs touching different triangles are full -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Source Claim 10 in one orientation. All labels and restoration hypotheses
are constructed from the actual distinct components and strict minimality. -/
theorem minimal_counterexample_distinct_triangle_neighbor_full
    (u v : V) (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J)
    (C E : (evenSubgraph G).ConnectedComponent) (hCE : C ≠ E)
    (htC : ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj u w)
    (htE : ∃ w : evenVertices G, w ∈ E.supp ∧ G.Adj v w) :
    ∀ w : evenVertices G, w ∈ E.supp → G.Adj v w := by
  classical
  by_contra hfail
  obtain ⟨a, b, c, hab, hac, hbc, hmC, habE, hacE, hbcE, hua, hub, hNu, hlocal⟩ :=
    minimal_counterexample_triangle_labels u hu hconn hcap hnot hset hmin C htC
  obtain ⟨d, e, z, hde, hdz, hez, hmE, hdeE, hdzE, hezE, hvd, hve, hNv, _⟩ :=
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
  have hnVz : ¬ G.Adj v z := by
    intro hz
    apply hfail
    intro w hw
    rcases (hmE w).mp hw with rfl | rfl | rfl
    · exact hvd
    · exact hve
    · exact hz
  have havoid (q : evenVertices G) (hq : q ∈ E.supp) : ¬ G.Adj u q := by
    intro h
    rcases hNu q h q.property with h | h | h
    · exact hcross a q haC hq (Subtype.ext h.symm)
    · exact hcross b q hbC hq (Subtype.ext h.symm)
    · exact hcross c q hcC hq (Subtype.ext h.symm)
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
  have hprivate (K : (evenSubgraph G).ConnectedComponent) (p : evenVertices G)
      (hp : p ∈ K.supp) (w : V) (ha : G.Adj p w) (he : Even (G.degree w)) :
      (⟨w, he⟩ : evenVertices G) ∈ K.supp := K.mem_supp_of_adj_mem_supp hp ha
  have hfN (t : Fin 8) (ht : t = 0 ∨ t = 1 ∨ t = 6) (w : V)
      (ha : G.Adj (f t) w) (he : Even (G.degree w)) : ∃ i : Fin 8, f i = w := by
    rcases ht with rfl | rfl | rfl
    · rcases hNu w ha he with h | h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
      · exact ⟨4, h.symm⟩
    · rcases hNv w ha he with h | h | h
      · exact ⟨5, h.symm⟩
      · exact ⟨6, h.symm⟩
      · exact ⟨7, h.symm⟩
    · rcases (hmE ⟨w, he⟩).mp (hprivate E e heE w ha he) with h | h | h
      · exact ⟨5, (congrArg Subtype.val h).symm⟩
      · exact ⟨6, (congrArg Subtype.val h).symm⟩
      · exact ⟨7, (congrArg Subtype.val h).symm⟩
  have hedge (i j : Fin 8) (h : G.Adj (f i) (f j)) :
      SimpleGraph.edge (f i) (f j) ≤ G := (SimpleGraph.edge_le_iff G).mpr (Or.inr h)
  have hdel (L : Bool) (hc : L = true → G.Adj u c) : twoTriangleDeletion L false f ≤ G := by
    rw [twoTriangleDeletion_split]
    apply sup_le
    · exact sup_le (sup_le (hedge 6 7 hezE) (hedge 1 5 hvd)) (hedge 0 1 huv)
    · cases L
      · rw [twoTriangleLeftDeletion_partial]
        exact sup_le (hedge 0 2 hua) (hedge 3 4 hbcE)
      · rw [twoTriangleLeftDeletion_full]
        apply Finset.sup_le
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hedge 0 2 hua
        · exact hedge 0 3 hub
        · exact hedge 0 4 (hc rfl)
  by_cases huc : G.Adj u c
  · have hle := hdel true (fun _ => huc)
    have hs : evenNeighbors G (f 0) = {f 2, f 3, f 4} := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hw
        obtain ⟨ha, he⟩ := (mem_evenNeighbors (f 0) w).mp hw
        exact hNu w ha he
      · rintro (rfl | rfl | rfl)
        · exact (mem_evenNeighbors u a).mpr ⟨hua, a.property⟩
        · exact (mem_evenNeighbors u b).mpr ⟨hub, b.property⟩
        · exact (mem_evenNeighbors u c).mpr ⟨huc, c.property⟩
    have hlocal' : ∀ w ∈ evenNeighbors G (f 0), eDegree G w ≤ 2 := by
      rw [hs]
      exact hlocal
    obtain ⟨D, hD⟩ := two_triangle_deletion_floor true false f hle hu hv hfEven
      hconn hcap hnot hset hmin
    obtain ⟨P, hP, _⟩ := D.restore_two_triangle_full_left f hle hu hv hfEven hfN
      (havoid z hzE) hnVz (havoid d hdE) hs hlocal'
    exact hnot ⟨P, hP.le.trans hD⟩
  · have hle := hdel false (by simp)
    have hNa : ∀ w, G.Adj (f 2) w → Even (G.degree w) → w = f 3 ∨ w = f 4 := by
      intro w ha he
      rcases (hmC ⟨w, he⟩).mp (hprivate C a haC w ha he) with h | h | h
      · exact (ha.ne (congrArg Subtype.val h).symm).elim
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    have hNc : ∀ w, G.Adj (f 4) w → Even (G.degree w) → w = f 2 ∨ w = f 3 := by
      intro w ha he
      rcases (hmC ⟨w, he⟩).mp (hprivate C c hcC w ha he) with h | h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
      · exact (ha.ne (congrArg Subtype.val h).symm).elim
    obtain ⟨D, hD⟩ := two_triangle_deletion_floor false false f hle hu hv hfEven
      hconn hcap hnot hset hmin
    obtain ⟨P, hP⟩ := D.restore_two_triangle_partial_left f hle hu hv hfEven hfN
      (havoid z hzE) hnVz (havoid d hdE) huc hNa hNc
    exact hnot ⟨P, hP.le.trans hD⟩

end Gallai
