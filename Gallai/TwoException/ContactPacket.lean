/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.StarSurplus
public import Gallai.Inputs.OddHubReserve
public import Gallai.Structure.StarPuncture

@[expose] public section

/-!
# Reserved-contact packet restoration

A contact packet consists of a missing star at `u` and one separately
reserved edge `uv`.  The reserved edge is absent while the star is restored.
The separation condition says that no star leaf is a neighbour of `v`; hence
the star transformation cannot create a passing neighbour at `v`.

This is the common restoration interface for the five finite contact rows in
the bare-minimality proof.  It deliberately does *not* assert that those rows
provide a packet: their graph-specific parity and component arguments remain
separate obligations.
-/

namespace Gallai.TwoException

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

noncomputable local instance contactPacketStarAdj (u : V) (S : Finset V) :
    DecidableRel (G ⊔ S.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The local hypotheses needed to restore a prepared contact star and then
its reserved edge.  All endpoint conditions refer to the punctured graph `G`.
-/
structure ContactPacket (D : Decomposition G) (u v : V) (S : Finset V) : Prop where
  hub_not_leaf : u ∉ S
  distinct : u ≠ v
  reserved_not_leaf : v ∉ S
  star_missing : ∀ w ∈ S, ¬ G.Adj u w
  reserved_missing : ¬ G.Adj u v
  leaves_away_from_reserved : ∀ w ∈ S, ¬ G.Adj v w
  leaf_passing : ∀ w ∈ S, passingNeighborCount D w ≤ 2
  hub_reserve : #S + 2 ≤ D.endpointCount u
  reserved_neighbour_positive : ∀ w, G.Adj v w → 0 < D.endpointCount w

/-- Expose the packet conditions in the form consumed by graph-specific
contact preparations.  In particular, the reserved edge is absent from the
ambient graph used for the star restoration, and no selected star leaf can
touch its protected endpoint. -/
theorem contact_packet_invariants (D : Decomposition G) (u v : V) (S : Finset V)
    (P : ContactPacket D u v S) :
    u ≠ v ∧ v ∉ S ∧ ¬ G.Adj u v ∧
      (∀ w ∈ S, ¬ G.Adj u w) ∧ (∀ w ∈ S, ¬ G.Adj v w) ∧
      #S + 2 ≤ D.endpointCount u :=
  ⟨P.distinct, P.reserved_not_leaf, P.reserved_missing, P.star_missing,
    P.leaves_away_from_reserved, P.hub_reserve⟩

/-- The packet hypotheses imply that `v` has no passing neighbours after the
star is restored, while `uv` is still absent. -/
private theorem zero_reserved_neighbors_after_star
    (D : Decomposition G) (u v : V) (S : Finset V)
    (P : ContactPacket D u v S)
    (E : Decomposition (G ⊔ S.sup (SimpleGraph.edge u)))
    (hvec : ∀ w, E.endpointCount w + (if u = w then #S else 0) =
      D.endpointCount w + if w ∈ S then 1 else 0) :
    #{w ∈ (G ⊔ S.sup (SimpleGraph.edge u)).neighborFinset v |
      E.endpointCount w = 0} = 0 := by
  classical
  letI : Fintype ↑((G ⊔ S.sup (SimpleGraph.edge u)).neighborSet v) := Subtype.fintype _
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwAdj, hwZero⟩ := Finset.mem_filter.mp hw
  rw [SimpleGraph.neighborFinset_sup] at hwAdj
  rcases Finset.mem_union.mp hwAdj with hwG | hwStar
  · have hwu : w ≠ u := by
      intro h
      subst w
      exact P.reserved_missing ((G.mem_neighborFinset v u).mp hwG).symm
    have hwS : w ∉ S := by
      intro hs
      exact P.leaves_away_from_reserved w hs ((G.mem_neighborFinset v w).mp hwG)
    have he := hvec w
    simp only [hwu.symm, if_false, hwS, Nat.add_zero] at he
    have hp := P.reserved_neighbour_positive w ((G.mem_neighborFinset v w).mp hwG)
    omega
  · have hstar := ((S.sup (SimpleGraph.edge u)).mem_neighborFinset v w).mp hwStar
    by_cases hvu : v = u
    · exact P.distinct (hvu.symm)
    · have hvs := (star_sup_adj_off_center u S v w hvu).mp hstar
      exact P.reserved_not_leaf hvs.1

/-- Restore a prepared contact packet without increasing the path count.
The final endpoint equation records all effects: star leaves gain one,
the protected vertex `v` gains one, and `u` pays once per restored edge.
-/
theorem restore_reserved_contact_packet
    (D : Decomposition G) (u v : V) (S : Finset V)
    (P : ContactPacket D u v S) :
    ∃ E : Decomposition ((G ⊔ S.sup (SimpleGraph.edge u)) ⊔ SimpleGraph.edge v u),
      E.size = D.size ∧
      ∀ w, E.endpointCount w + (if u = w then #S + 1 else 0) =
        D.endpointCount w + (if w ∈ S then 1 else 0) + if v = w then 1 else 0 := by
  obtain ⟨E₁, hs₁, hv₁⟩ := restore_star_surplus_two D u S P.hub_not_leaf
    P.star_missing P.leaf_passing P.hub_reserve
  have hzero := zero_reserved_neighbors_after_star D u v S P E₁ hv₁
  have hu : 2 ≤ E₁.endpointCount u := by
    have hv : E₁.endpointCount u + #S = D.endpointCount u := by
      simpa [P.hub_not_leaf] using hv₁ u
    have hreserve := P.hub_reserve
    omega
  have hmissing : ¬ (G ⊔ S.sup (SimpleGraph.edge u)).Adj v u := by
    intro h
    rcases (SimpleGraph.sup_adj _ _ _ _).mp h with hG | hS
    · exact P.reserved_missing hG.symm
    · have hsu := (star_sup_adj_center u S P.hub_not_leaf v).mp hS.symm
      exact P.reserved_not_leaf hsu
  obtain ⟨E₂, hs₂, hv₂⟩ := E₁.single_edge_addibility v u P.distinct.symm hmissing
    (by rw [hzero]; omega)
  refine ⟨E₂, hs₂.trans hs₁, ?_⟩
  intro w
  have h₁ := hv₁ w
  have h₂ := hv₂ w
  by_cases huw : u = w <;> by_cases hvw : v = w <;> by_cases hSw : w ∈ S <;>
    simp only [huw, hvw, hSw, if_true, if_false, Nat.add_zero] at h₁ h₂ ⊢ <;> omega

end Gallai.TwoException
