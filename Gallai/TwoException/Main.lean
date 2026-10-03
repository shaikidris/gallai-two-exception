/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.PrescribedEndpoint

@[expose] public section

/-! # The ceiling bound with at most two E-degree exceptions -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every connected finite simple graph with at most two even vertices
having more than three even neighbours satisfies the ceiling path bound.
No designated vertices, positive degrees, or non-cut hypotheses are needed. -/
theorem ceiling_bound_of_subtype (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcount : Fintype.card {v : V // Even (G.degree v) ∧ 3 < eDegree G v} ≤ 2) :
    HasPathBudget G ((Fintype.card V + 1) / 2) := by
  classical
  let E : Finset V := Finset.univ.filter fun v => Even (G.degree v) ∧ 3 < eDegree G v
  have hmem (v : V) : v ∈ E ↔ Even (G.degree v) ∧ 3 < eDegree G v := by simp [E]
  have hcard : E.card ≤ 2 := by simpa [Fintype.card_subtype, E] using hcount
  by_cases hex : E.Nonempty
  · obtain ⟨h, hh⟩ := hex
    obtain ⟨hhEven, hhLarge⟩ := (hmem h).mp hh
    have hhpos : 0 < G.degree h := by
      have hb := eDegree_le_degree (G := G) h
      omega
    by_cases hx : ∃ x ∈ E, x ≠ h
    · obtain ⟨x, hxE, hxh⟩ := hx
      have hxEven := ((hmem x).mp hxE).1
      have hcap (v : V) (hv : Even (G.degree v)) (hvh : v ≠ h) (hvx : v ≠ x) :
          eDegree G v ≤ 3 := by
        by_contra hn
        have hvE : v ∈ E := (hmem v).mpr ⟨hv, by omega⟩
        have hs : ({h, x, v} : Finset V) ⊆ E := by
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl | rfl <;> assumption
        have hb := Finset.card_le_card hs
        have ht : ({h, x, v} : Finset V).card = 3 := by
          simp [Ne.symm hxh, Ne.symm hvh, Ne.symm hvx]
        omega
      obtain ⟨D, hd, _⟩ := prescribed_endpoint G h x hconn hxh.symm hhpos hhEven hxEven hcap
      exact ⟨D, hd⟩
    · have hcap (v : V) (hv : Even (G.degree v)) (hvh : v ≠ h) : eDegree G v ≤ 3 := by
        by_contra hn
        exact hx ⟨v, (hmem v).mpr ⟨hv, by omega⟩, hvh⟩
      obtain ⟨D, hd, _⟩ := one_exception_endpoint G h hconn hhpos hhEven hcap
      exact ⟨D, hd⟩
  · have hcap (v : V) (hv : Even (G.degree v)) : eDegree G v ≤ 3 := by
      by_contra hn
      exact hex ⟨v, (hmem v).mpr ⟨hv, by omega⟩⟩
    rcases floor_or_set G hconn hcap with ⟨D, hd⟩ | hs
    · exact ⟨D, by omega⟩
    · let : Nonempty V := hconn.nonempty
      obtain ⟨v⟩ := (inferInstance : Nonempty V)
      obtain ⟨D, hd, _⟩ := hs.endpoint_reserve v
      exact ⟨D, hd⟩

/-- Finite-set formulation of the ceiling bound with at most two E-degree exceptions. -/
theorem ceiling_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcount : (Finset.univ.filter
      (fun v : V => Even (G.degree v) ∧ 3 < eDegree G v)).card ≤ 2) :
    HasPathBudget G ((Fintype.card V + 1) / 2) := by
  classical
  apply ceiling_bound_of_subtype G hconn
  simpa only [Fintype.card_subtype] using hcount

end Gallai.TwoException
