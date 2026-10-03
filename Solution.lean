/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Gallai.TwoException.Main
public import Gallai.TwoException.SimultaneousEndpoint

/-! # Proofs of the four selected two-exception statements -/

@[expose] public section

namespace Gallai.Submission
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The prescribed-endpoint ceiling theorem. -/
theorem prescribed_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V)
    (hconn : G.Connected) (hhne : h ≠ x) (hhpos : 0 < G.degree h)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h :=
  TwoException.prescribed_endpoint G h x hconn hhne hhpos hhEven hxEven hcap

/-- Gallai's ceiling bound with at most two E-degree exceptions. -/
theorem ceiling_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcount : (Finset.univ.filter
      (fun v : V => Even (G.degree v) ∧ 3 < eDegree G v)).card ≤ 2) :
    HasPathBudget G ((Fintype.card V + 1) / 2) :=
  TwoException.ceiling_bound G hconn hcount

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Simultaneous endpoint reserves at the floor-plus-one budget. -/
theorem simultaneous_floor_add_one
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ Fintype.card V / 2 + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
  TwoException.simultaneous_floor_add_one hconn h x hne hh hx hcap

/-- Simultaneous endpoint reserves at the odd-order ceiling. -/
theorem odd_order_simultaneous (m : ℕ) (horder : Fintype.card V = 2 * m + 1)
    (hconn : G.Connected) (h x : V) (hne : h ≠ x)
    (hh : Even (G.degree h)) (hx : Even (G.degree x))
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ m + 1 ∧
      2 ≤ D.endpointCount h ∧ 2 ≤ D.endpointCount x :=
  TwoException.odd_order_simultaneous m horder hconn h x hne hh hx hcap

end Gallai.Submission
