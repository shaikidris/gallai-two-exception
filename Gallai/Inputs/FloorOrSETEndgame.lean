/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.TwoFullHubClaim
public import Gallai.Inputs.EveryOddNeighbor

@[expose] public section

/-! # Connectivity closes the floor-or-SET minimal-counterexample argument -/

namespace Gallai

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Connected propagation forces a single even triangle and the literal SET
condition, contradicting the two failure guards. -/
theorem minimal_counterexample_floor_or_set_false
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) : False := by
  classical
  have hex : ∃ a, Even (G.degree a) := by
    by_contra hn
    apply hnot
    apply pathBudget_of_at_most_one_even G
    intro a ha b hb
    exact (hn ⟨a, ha⟩).elim
  obtain ⟨a, ha⟩ := hex
  let q : evenVertices G := ⟨a, ha⟩
  let C := (evenSubgraph G).connectedComponentMk q
  have hqC : q ∈ C.supp := by simp [C, SimpleGraph.ConnectedComponent.mem_supp_iff]
  let R := fun v => ∃ w : evenVertices G, w ∈ C.supp ∧ ((w : V) = v ∨ G.Adj v w)
  have heven (v : V) (hv : Even (G.degree v)) (hr : R v) :
      (⟨v, hv⟩ : evenVertices G) ∈ C.supp := by
    obtain ⟨w, hw, he | he⟩ := hr
    · have hh : w = (⟨v, hv⟩ : evenVertices G) := Subtype.ext he
      rwa [hh] at hw
    · exact C.mem_supp_of_adj_mem_supp hw he.symm
  have htouch (v : V) (hv : Odd (G.degree v)) (hr : R v) :
      ∃ w : evenVertices G, w ∈ C.supp ∧ G.Adj v w := by
    obtain ⟨w, hw, he | he⟩ := hr
    · have hev : Even (G.degree v) := by rw [← he]; exact w.property
      exact (Nat.not_even_iff_odd.mpr hv hev).elim
    · exact ⟨w, hw, he⟩
  have hstep (s t : V) (hst : G.Adj s t) (hs : R s) : R t := by
    by_cases heS : Even (G.degree s)
    · have hsC := heven s heS hs
      by_cases heT : Even (G.degree t)
      · exact ⟨⟨t, heT⟩, C.mem_supp_of_adj_mem_supp hsC hst, Or.inl rfl⟩
      · exact ⟨⟨s, heS⟩, hsC, Or.inr hst.symm⟩
    have hoS := Nat.not_even_iff_odd.mp heS
    have htS := htouch s hoS hs
    by_cases heT : Even (G.degree t)
    · let b : evenVertices G := ⟨t, heT⟩
      let E := (evenSubgraph G).connectedComponentMk b
      have hbE : b ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hCE := minimal_counterexample_odd_neighbors_one_component
        s hoS hconn hcap hnot hset hmin C E htS ⟨b, hbE, hst⟩
      exact ⟨b, hCE.symm ▸ hbE, Or.inl rfl⟩
    · have hoT := Nat.not_even_iff_odd.mp heT
      obtain ⟨b, htb, hb⟩ := minimal_counterexample_odd_has_even_neighbor
        hconn hcap hnot hset hmin t hoT
      let r : evenVertices G := ⟨b, hb⟩
      let E := (evenSubgraph G).connectedComponentMk r
      have hrE : r ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hCE := minimal_counterexample_adjacent_odd_components_eq
        s t hoS hoT hst hconn hcap hnot hset hmin C E htS ⟨r, hrE, htb⟩
      exact ⟨r, hCE.symm ▸ hrE, Or.inr htb⟩
  have hwalk : ∀ {s t : V}, G.Walk s t → R s → R t := by
    intro s t p
    induction p with
    | nil => exact fun h => h
    | @cons s t v hst p ih => exact fun hs => ih (hstep s t hst hs)
  have hall (w : evenVertices G) : w ∈ C.supp := by
    obtain ⟨p⟩ := hconn.preconnected a w
    exact heven w w.property (hwalk p ⟨q, hqC, Or.inl rfl⟩)
  have huniv : C.supp = Set.univ := Set.eq_univ_of_forall hall
  obtain ⟨hcard, hcomplete⟩ := minimal_counterexample_even_components_triangles
    hconn hcap hnot hset hmin C
  apply hset
  refine ⟨?_, ?_, ?_⟩
  · rw [huniv] at hcard
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_subtype, evenVertices, Set.mem_ofPred_eq] using hcard
  · intro s t hs ht hst
    have hcs := hall ⟨s, hs⟩
    have hct := hall ⟨t, ht⟩
    have he : C.toSimpleGraph.Adj ⟨⟨s, hs⟩, hcs⟩ ⟨⟨t, ht⟩, hct⟩ := by
      rw [hcomplete]
      intro heq
      exact hst (congrArg (fun w : C.supp => (w.val : V)) heq)
    exact he
  · intro v hv
    obtain ⟨w, hvw, hw⟩ := minimal_counterexample_odd_has_even_neighbor
      hconn hcap hnot hset hmin v hv
    have hp : 0 < eDegree G v := Finset.card_pos.mpr
      ⟨w, (mem_evenNeighbors v w).mpr ⟨hvw, hw⟩⟩
    have hn := minimal_counterexample_eDegree_ne_one hconn hcap hnot hset hmin v
    omega

end Gallai
