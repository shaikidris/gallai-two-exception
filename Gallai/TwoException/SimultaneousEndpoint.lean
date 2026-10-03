/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.OddOrder
public import Gallai.TwoException.SimultaneousBridge
public import Gallai.TwoException.SimultaneousNonbridge

@[expose] public section

/-! # Simultaneous endpoint exposure for two exceptional vertices

The public proposition is the literal three-way dispatch on the edge joining
the designated even vertices.  The nonedge case is the inherited addition and
deletion construction; an existing edge is either a bridge or a nonbridge.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two designated positive-degree even vertices can be exposed
simultaneously within the floor budget plus one path, without an adjacency
assumption. -/
theorem simultaneous_floor_add_one
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by
  by_cases hedge : G.Adj h x
  · by_cases hbridge : G.IsBridge s(h, x)
    · exact simultaneous_of_bridge hconn h x hne hedge hbridge hh hx hcap
    · exact simultaneous_of_nonbridge hconn h x hne hedge hbridge hh hx hcap
  · exact Gallai.two_exception_floor_add_one hconn h x hne hedge hh hx hcap

/-- At odd order, the floor-plus-one simultaneous bound is the Gallai ceiling
bound. -/
theorem odd_order_simultaneous (m : ℕ) (horder : Fintype.card V = 2 * m + 1)
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ m + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x := by
  obtain ⟨D, hDsize, hDh, hDx⟩ :=
    simultaneous_floor_add_one hconn h x hne hh hx hcap
  exact ⟨D, by omega, hDh, hDx⟩

end Gallai.TwoException
