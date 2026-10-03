/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.FullTriangleRestore
public import Gallai.Inputs.FanPunctureFloor

@[expose] public section

/-! # The floor witness for full-triangle odd-neighbour restoration -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The four-leaf odd Fan puncture gives the actual floor witness consumed
by full-triangle restoration. Its parity and E-degree cap are derived. -/
theorem full_triangle_odd_neighbor_floor
    (u v : V) (hu : Odd (G.degree u)) (hv : Odd (G.degree v)) (huv : G.Adj u v)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w)) (hthree : eDegree G u = 3)
    (ht : ComponentsAreTriangles (evenSubgraph G))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (evenStarPuncture (G.deleteEdges {s(u, v)}) u)
      (Fintype.card V / 2) := by
  classical
  let B := insert v (evenNeighbors G u)
  let F := B.sup (SimpleGraph.edge u)
  let H := G \ F
  have huB : u ∉ B := by simp [B, huv.ne]
  have hvS : v ∉ evenNeighbors G u := by
    intro h
    exact Nat.not_even_iff_odd.mpr hv ((mem_evenNeighbors u v).mp h).2
  have hB : #B = 4 := by simp [B, hvS, show #(evenNeighbors G u) = 3 from hthree]
  have hBa : ∀ w ∈ B, G.Adj u w := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact huv
    · exact ((mem_evenNeighbors u w).mp hw).1
  have hle : F ≤ G := by
    apply Finset.sup_le
    intro w hw
    exact (SimpleGraph.edge_le_iff G).mpr (Or.inr (hBa w hw))
  have hdF (w : V) (hwu : w ≠ u) : F.degree w = if w ∈ B then 1 else 0 := by
    have hn : F.neighborFinset w = if w ∈ B then {u} else ∅ := by
      ext t
      simp only [SimpleGraph.neighborFinset, Set.mem_toFinset, SimpleGraph.mem_neighborSet]
      change (B.sup (SimpleGraph.edge u)).Adj w t ↔ _
      rw [star_sup_adj_off_center u B w t hwu]
      split_ifs <;> simp_all
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hn]
    split_ifs <;> simp
  have hm : ∀ w, w ≠ u → F.degree w ≤ 1 := by
    intro w hw
    rw [hdF w hw]
    split_ifs <;> omega
  have he : ∀ w, w ≠ u → w ≠ v → 0 < F.degree w → Even (G.degree w) := by
    intro w hwu hwv hp
    have hwB : w ∈ B := by
      by_contra hn
      rw [hdF w hwu, if_neg hn] at hp
      omega
    rcases Finset.mem_insert.mp hwB with h | h
    · exact (hwv h).elim
    · exact ((mem_evenNeighbors u w).mp h).2
  have hdv : F.degree v = 1 := by rw [hdF v huv.ne.symm]; simp [B]
  have hfv : F.Adj u v := (star_sup_adj_center u B huB v).mpr (by simp [B])
  obtain ⟨_, _, hk⟩ := odd_star_puncture_parity hle u v hm he hv hdv
  have huH : Odd (H.degree u) := by
    have hd := starPuncture_degree_center G u B huB
      (fun w hw => (G.mem_neighborFinset u w).mpr (hBa w hw))
    rw [Nat.odd_iff] at hu ⊢
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', H, F, starPuncture] at hd hu ⊢
    omega
  have hkeep : ∀ w, w ≠ v → Even (H.degree w) → Even (G.degree w) := by
    intro w hwv hw
    by_cases hwu : w = u
    · subst w
      exact (Nat.not_even_iff_odd.mpr huH hw).elim
    · exact hk w hwu hwv hw
  have hcu : ∀ w, H.Adj u w → ¬ Even (H.degree w) := by
    intro w ha hw
    have hwB : w ∉ B := fun hb => ha.2 ((star_sup_adj_center u B huB w).mpr hb)
    have hwv : w ≠ v := by intro h; subst w; exact hwB (by simp [B])
    have hg := hkeep w hwv hw
    exact hwB (Finset.mem_insert_of_mem ((mem_evenNeighbors u w).mpr ⟨ha.1, hg⟩))
  have hcv : ∀ w, H.Adj v w → ¬ Even (H.degree w) := by
    intro w ha hw
    exact hNv w ha.1 (hkeep w ha.ne.symm hw)
  have hcapH := even_degree_cap_of_isolated_exception (G := G) (H := H)
    (fun _ _ h => h.1) v hkeep hcv 3 hcap
  have hfloor : HasPathBudget H (Fintype.card V / 2) :=
    odd_star_puncture_floor hle u v hm he hu hv hdv hfv hcu ht hcapH
      hconn hcap hnot hset hmin
  have hj : G.deleteEdges {s(u, v)} = G \ SimpleGraph.edge u v := by
    ext a b
    simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sdiff_adj,
      Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
    constructor
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun h => hn h.1⟩
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun h => hn ⟨h, ha.ne⟩⟩
  have hgraph : evenStarPuncture (G.deleteEdges {s(u, v)}) u = H := by
    change G.deleteEdges {s(u, v)} \
      (evenNeighbors (G.deleteEdges {s(u, v)}) u).sup (SimpleGraph.edge u) = H
    rw [odd_edge_hub_evenNeighbors u v hv, hj, sdiff_sdiff]
    simp only [H, F, B, Finset.sup_insert]
  rwa [hgraph]

end Gallai
