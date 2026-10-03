/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.Endpoints
public import Lean.Elab.Tactic.Omega
public import Mathlib.Combinatorics.SimpleGraph.Trails

@[expose] public section

/-!
# Endpoint parity from edge incidence

The local parity law is inherited from Mathlib's trail theorem, with
nonemptiness excluding coincident endpoints. Global parity must use the
decomposition's unique edge coverage; it is not a field of the representation.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- A path's incident-edge count has the parity of its endpoint indicators. -/
theorem NonemptyPath.incident_mod_two (P : NonemptyPath G) (v : V) :
    (P.walk.edges.countP fun e => v ∈ e) % 2 =
      ((if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0)) % 2 := by
  have hdistinct := P.start_ne_finish G
  have hparity : (P.walk.edges.countP fun e => v ∈ e) % 2 = 0 ↔
      v ≠ P.start ∧ v ≠ P.finish := by
    have hbase := P.isPath.isTrail.even_countP_edges_iff v
    rw [Nat.even_iff] at hbase
    exact ⟨fun h => hbase.mp h hdistinct, fun h => hbase.mpr (fun _ => h)⟩
  by_cases hs : P.start = v
  · have ht : P.finish ≠ v := fun h => hdistinct (hs.trans h.symm)
    have hodd : (P.walk.edges.countP fun e => v ∈ e) % 2 ≠ 0 :=
      fun h => (hparity.mp h).1 hs.symm
    simp only [if_pos hs, if_neg ht]
    omega
  · by_cases ht : P.finish = v
    · have hodd : (P.walk.edges.countP fun e => v ∈ e) % 2 ≠ 0 :=
        fun h => (hparity.mp h).2 ht.symm
      simp only [if_neg hs, if_pos ht]
      omega
    · have heven := hparity.mpr ⟨Ne.symm hs, Ne.symm ht⟩
      simp only [if_neg hs, if_neg ht]
      omega

/-- Filtering the edge finset of a path counts its incident edges. -/
theorem NonemptyPath.card_incident_edges (P : NonemptyPath G) (v : V) :
    #(P.isPath.isTrail.edgesFinset.filter (v ∈ ·)) =
      P.walk.edges.countP (fun e => v ∈ e) := by
  change Multiset.card ((P.isPath.isTrail.edgesFinset.val).filter (v ∈ ·)) = _
  rw [← Multiset.countP_eq_card_filter]
  rfl

omit [DecidableEq V] in
/-- Distinct decomposition paths cannot share an edge. -/
theorem Decomposition.disjoint_path_edges (D : Decomposition G)
    {i j : Fin D.size} (hne : i ≠ j) :
    Disjoint (D.path i).isPath.isTrail.edgesFinset
      (D.path j).isPath.isTrail.edgesFinset := by
  apply Finset.disjoint_left.mpr
  intro e hi hj
  have hei : e ∈ (D.path i).walk.edges := hi
  have hej : e ∈ (D.path j).walk.edges := hj
  obtain ⟨k, _, hu⟩ := D.covers e ((D.path i).walk.edges_subset_edgeSet hei)
  exact hne ((hu i hei).trans (hu j hej).symm)

variable [Fintype V] [DecidableRel G.Adj]

/-- Unique edge coverage partitions the edges incident at each vertex. -/
theorem Decomposition.incidence_partition (D : Decomposition G) (v : V) :
    G.incidenceFinset v = Finset.univ.biUnion (fun i : Fin D.size =>
      (D.path i).isPath.isTrail.edgesFinset.filter (v ∈ ·)) := by
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
    Set.mem_ofPred_eq, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨he, hv⟩
    obtain ⟨i, hi, _⟩ := D.covers e he
    exact ⟨i, hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨(D.path i).walk.edges_subset_edgeSet hi, hv⟩

/-- Vertex degree is the sum of the incident-edge counts of the paths. -/
theorem Decomposition.degree_eq_sum_incident (D : Decomposition G) (v : V) :
    G.degree v = ∑ i : Fin D.size, (D.path i).walk.edges.countP (fun e => v ∈ e) := by
  rw [← G.card_incidenceFinset_eq_degree v, D.incidence_partition v]
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => (D.path i).card_incident_edges v)
  · intro i _ j _ hne
    exact (D.disjoint_path_edges hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Endpoint multiplicity and ordinary graph degree have the same parity. -/
theorem Decomposition.endpointCount_mod_two (D : Decomposition G) (v : V) :
    D.endpointCount v % 2 = G.degree v % 2 := by
  rw [D.degree_eq_sum_incident v]
  unfold Decomposition.endpointCount
  rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ((D.path i).incident_mod_two v).symm)

end Gallai
