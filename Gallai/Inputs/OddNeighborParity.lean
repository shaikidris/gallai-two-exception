/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OddNeighborDeletion

@[expose] public section

/-! # Parity and isolated-even-vertex control for the three-edge puncture -/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two odd labels and three even labels have their exact new parities;
only the distinguished odd neighbour can become newly even. -/
theorem oddNeighborDeletion_parity (u v x y z : V) (hd : [u, v, x, y, z].Nodup)
    (hle : oddNeighborDeletion u v x y z ≤ G)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hx : Even (G.degree x)) (hy : Even (G.degree y)) (hz : Even (G.degree z)) :
    let H := G \ oddNeighborDeletion u v x y z
    Odd (H.degree u) ∧ Even (H.degree v) ∧ Odd (H.degree x) ∧
      Odd (H.degree y) ∧ Odd (H.degree z) ∧
      (∀ w, w ≠ v → Even (H.degree w) → Even (G.degree w)) := by
  classical
  let H := G \ oddNeighborDeletion u v x y z
  have hsum (w : V) : H.degree w +
      (if w = u then 2 else if w ∈ ({v, x, y, z} : Finset V) then 1 else 0) =
      G.degree w := by
    have h := degree_sdiff_add_of_le hle w
    rwa [oddNeighborDeletion_degree u v x y z hd w] at h
  have hsum1 (w : V) (hwu : w ≠ u) (hw : w ∈ ({v, x, y, z} : Finset V)) :
      H.degree w + 1 = G.degree w := by simpa [hwu, hw] using hsum w
  have h0 : H.degree u + 2 = G.degree u := by simpa using hsum u
  have huv : u ≠ v := by simp_all
  have hux : u ≠ x := by simp_all
  have huy : u ≠ y := by simp_all
  have huz : u ≠ z := by simp_all
  have h1 := hsum1 v huv.symm (by simp)
  have h2 := hsum1 x hux.symm (by simp)
  have h3 := hsum1 y huy.symm (by simp)
  have h4 := hsum1 z huz.symm (by simp)
  have hp : Odd (H.degree u) ∧ Even (H.degree v) ∧ Odd (H.degree x) ∧
      Odd (H.degree y) ∧ Odd (H.degree z) := by
    simp only [Nat.odd_iff, Nat.even_iff] at hu hv hx hy hz ⊢
    omega
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, ?_⟩
  intro w hwv he
  have hwu : w ≠ u := by
    intro h
    subst w
    exact Nat.not_even_iff_odd.mpr hp.1 he
  have hwx : w ≠ x := by
    intro h
    subst w
    exact Nat.not_even_iff_odd.mpr hp.2.2.1 he
  have hwy : w ≠ y := by
    intro h
    subst w
    exact Nat.not_even_iff_odd.mpr hp.2.2.2.1 he
  have hwz : w ≠ z := by
    intro h
    subst w
    exact Nat.not_even_iff_odd.mpr hp.2.2.2.2 he
  have hs : H.degree w = G.degree w := by
    simpa [hwu, hwv, hwx, hwy, hwz] using hsum w
  rwa [← hs]

/-- The distinguished neighbour is isolated in the punctured even subgraph.
The centre also has no even neighbour there; the original centre may retain
an originally even neighbour whose parity has changed. -/
theorem oddNeighborDeletion_centres (u v x y z : V) (hd : [u, v, x, y, z].Nodup)
    (hle : oddNeighborDeletion u v x y z ≤ G)
    (hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hx : Even (G.degree x)) (hy : Even (G.degree y)) (hz : Even (G.degree z))
    (hNu : ∀ w, G.Adj u w → Even (G.degree w) → w = x ∨ w = y)
    (hNv : ∀ w, G.Adj v w → ¬ Even (G.degree w)) :
    let H := G \ oddNeighborDeletion u v x y z
    (∀ w, H.Adj u w → ¬ Even (H.degree w)) ∧
      (∀ w, H.Adj v w → ¬ Even (H.degree w)) := by
  classical
  obtain ⟨_, _, hx', hy', _, hk⟩ := oddNeighborDeletion_parity u v x y z hd hle
    hu hv hx hy hz
  constructor
  · intro w huw he
    have hwv : w ≠ v := by
      intro h
      subst w
      apply huw.2
      have huv : u ≠ v := by simp_all
      exact Or.inl (Or.inl ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩))
    rcases hNu w huw.1 (hk w hwv he) with rfl | rfl
    · exact Nat.not_even_iff_odd.mpr hx' he
    · exact Nat.not_even_iff_odd.mpr hy' he
  · intro w hvw he
    exact hNv w hvw.1 (hk w hvw.ne.symm he)

end Gallai
