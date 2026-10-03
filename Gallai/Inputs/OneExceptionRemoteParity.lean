/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.OneExceptionOddEDegree
public import Gallai.Structure.StarPunctureException

@[expose] public section

/-! # E-degree parity away from the designated vertex and its neighbours -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- An even vertex not adjacent to the designated exception has even E-degree
in a strict minimum counterexample. The actual restoration preserves x's
endpoint reserve because x is outside the restored star. -/
theorem one_exception_nonadjacent_eDegree_even (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (hconn : G.Connected)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → eDegree G v ≤ 3)
    (hnot : ¬ ∃ D : Decomposition G,
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount x)
    (hmin : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (J : SimpleGraph W) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ y : W, 0 < J.degree y → Even (J.degree y) →
        (∀ v, Even (J.degree v) → v ≠ y → eDegree J v ≤ 3) →
        ∃ D : Decomposition J, D.size ≤ (Fintype.card W + 1) / 2 ∧
          2 ≤ D.endpointCount y)
    (z : V) (hz : Even (G.degree z)) (hzx : z ≠ x) (hmissing : ¬ G.Adj z x) :
    Even (eDegree G z) := by
  classical
  by_contra hn
  have ho : Odd (eDegree G z) := Nat.not_even_iff_odd.mp hn
  let H := evenStarPuncture G z
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hc := one_exception_delete_even_connected G x hconn hxpos hxEven hcap hnot hmin z hz
  have hcH := odd_evenStarPuncture_connected G z hz ho hc
  have hlt := evenStarPuncture_edge_count_lt G z ho.pos
  have hxS : x ∉ evenNeighbors G z := fun h => hmissing ((mem_evenNeighbors z x).mp h).1
  have hd : H.degree x = G.degree x := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', H, evenStarPuncture] using
      starPuncture_degree_other G z (evenNeighbors G z) x hzx.symm hxS
  obtain ⟨D, hs, he⟩ := hmin V H
    (by simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card', H] using hlt)
    hcH x (by rwa [hd]) (by rwa [hd])
    (by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
        ← Set.ncard_eq_toFinset_card', H] using evenStarPuncture_cap_except G z x hcap)
  obtain ⟨P, hp, _, hkeep⟩ := D.restore_odd_even_star_exposing_preserving z hz ho
    (fun v hv => hcap v ((mem_evenNeighbors z v).mp hv).2
      (fun h => hxS (h ▸ hv)))
  have heP : P.endpointCount x = D.endpointCount x := hkeep x hzx.symm hxS
  exact hnot ⟨P, by omega, by omega⟩

end Gallai
