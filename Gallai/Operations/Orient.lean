/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Operations.Transport
public import Gallai.Foundations.Endpoints

@[expose] public section

/-!
# Orienting every terminal carrier toward a hub

Reversal changes no edge owner or endpoint count. All carriers starting at
the hub are reversed; all other carriers, including through carriers, stay
unchanged. This supplies a uniform normalization without a favourable choice.
-/

namespace Gallai

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- Reverse a path exactly when its initial vertex is the designated vertex. -/
def NonemptyPath.toward (P : NonemptyPath G) (x : V) : NonemptyPath G :=
  if P.start = x then P.reverse else P

/-- A path starting at the designated vertex is reversed. -/
theorem NonemptyPath.toward_of_start_eq (P : NonemptyPath G) (x : V)
    (hs : P.start = x) : P.toward x = P.reverse := if_pos hs

/-- A carrier not starting at the designated vertex is left unchanged. -/
theorem NonemptyPath.toward_of_start_ne (P : NonemptyPath G) (x : V)
    (hs : P.start ≠ x) : P.toward x = P := if_neg hs

/-- Orientation changes no unordered edge membership. -/
theorem NonemptyPath.mem_toward_edges (P : NonemptyPath G) (x : V) (e : Sym2 V) :
    e ∈ (P.toward x).walk.edges ↔ e ∈ P.walk.edges := by
  by_cases hs : P.start = x
  · have h := congrArg (fun Q : NonemptyPath G => Q.walk.edges) (P.toward_of_start_eq x hs)
    rw [h, reverse_edges, List.mem_reverse]
  · have h := congrArg (fun Q : NonemptyPath G => Q.walk.edges) (P.toward_of_start_ne x hs)
    rw [h]

/-- Orientation changes no vertex membership. -/
theorem NonemptyPath.mem_toward_support (P : NonemptyPath G) (x w : V) :
    w ∈ (P.toward x).walk.support ↔ w ∈ P.walk.support := by
  by_cases hs : P.start = x
  · have h := congrArg (fun Q : NonemptyPath G => Q.walk.support) (P.toward_of_start_eq x hs)
    rw [h]
    change w ∈ P.walk.reverse.support ↔ _
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  · have h := congrArg (fun Q : NonemptyPath G => Q.walk.support) (P.toward_of_start_ne x hs)
    rw [h]

/-- If the designated vertex was an endpoint, it is the new final endpoint. -/
theorem NonemptyPath.toward_finish (P : NonemptyPath G) (x : V)
    (hx : P.start = x ∨ P.finish = x) : (P.toward x).finish = x := by
  unfold toward
  split_ifs with hs
  · exact hs
  · exact hx.resolve_left hs

/-- Orientation preserves the endpoint contribution at every vertex. -/
theorem NonemptyPath.toward_endpoint_contribution (P : NonemptyPath G) (x w : V) :
    ((if (P.toward x).start = w then 1 else 0) +
      (if (P.toward x).finish = w then 1 else 0 : ℕ)) =
    ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) := by
  by_cases hs : P.start = x
  · rw [P.toward_of_start_eq x hs]
    exact Nat.add_comm _ _
  · rw [P.toward_of_start_ne x hs]

/-- Orient every path starting at the hub toward that hub, preserving exact coverage. -/
def Decomposition.orientToward (D : Decomposition G) (x : V) : Decomposition G where
  size := D.size
  path := fun i => (D.path i).toward x
  covers := by
    intro e he
    obtain ⟨i, hi, hu⟩ := D.covers e he
    refine ⟨i, ((D.path i).mem_toward_edges x e).mpr hi, ?_⟩
    intro j hj
    exact hu j (((D.path j).mem_toward_edges x e).mp hj)

/-- Uniform orientation preserves the number of decomposition carriers. -/
@[simp] theorem Decomposition.orientToward_size (D : Decomposition G) (x : V) :
    (D.orientToward x).size = D.size := rfl

/-- Uniform orientation preserves every vertex's endpoint multiplicity. -/
theorem Decomposition.orientToward_endpointCount (D : Decomposition G) (x w : V) :
    (D.orientToward x).endpointCount w = D.endpointCount w := by
  apply Finset.sum_congr rfl
  intro i _
  exact (D.path i).toward_endpoint_contribution x w

/-- Every old terminal carrier now finishes at the hub, with its index retained. -/
theorem Decomposition.orientToward_terminal (D : Decomposition G) (x : V) (i : Fin D.size)
    (hx : (D.path i).start = x ∨ (D.path i).finish = x) :
    ((D.orientToward x).path i).finish = x := (D.path i).toward_finish x hx

end Gallai
