/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.SETImageComponent
public import Gallai.Inputs.NoEvenIsolates
public import Gallai.Inputs.PunctureCaps
public import Gallai.Inputs.PunctureComponentFloor

@[expose] public section

/-! # The parity-explicit puncture floor lemma

The proof of source Claim 9 requires every active deleted vertex to be odd
in the puncture. This condition is explicit here and must be proved by each
concrete deletion consumer; it is not a consequence of deletion alone.
-/

namespace Gallai

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G F : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel F.Adj]

/-- Corrected Claim 9 with the punctured oddness used by its proof explicit.
The conclusion is an actual floor decomposition, allowing disconnected punctures. -/
theorem active_odd_puncture_floor (hle : F ≤ G) (hactive : ∃ a b, F.Adj a b)
    (hodd : ∀ w, 0 < F.degree w → Odd ((G \ F).degree w))
    (hneighbor : ∀ u, Odd (G.degree u) → 0 < F.degree u →
      ∃ v, F.Adj u v ∧ Even (G.degree v))
    (hconn : G.Connected) (hcap : ∀ w, Even (G.degree w) → eDegree G w ≤ 3)
    (hnot : ¬ HasPathBudget G (Fintype.card V / 2)) (hset : ¬ IsSET G)
    (hmin : ∀ (U : Set V) [DecidablePred (· ∈ U)]
      (J : SimpleGraph U) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      (∀ w, Even (J.degree w) → eDegree J w ≤ 3) →
      HasPathBudget J (Fintype.card U / 2) ∨ IsSET J) :
    HasPathBudget (G \ F) (Fintype.card V / 2) := by
  classical
  let H := G \ F
  have ht : ComponentsAreTriangles (evenSubgraph G) :=
    minimal_counterexample_even_components_triangles hconn hcap hnot hset hmin
  have hlt : H < G := by
    refine lt_iff_le_not_ge.mpr ⟨fun _ _ h => h.1, ?_⟩
    intro hh
    obtain ⟨a, b, hab⟩ := hactive
    exact (hh (hle hab)).2 hab
  have hkeep : ∀ w, Even (H.degree w) → Even (G.degree w) := by
    intro w hw
    by_cases hp : 0 < F.degree w
    · exact (Nat.not_even_iff_odd.mpr (hodd w hp) hw).elim
    have hd := degree_sdiff_add_of_le hle w
    have hz : F.degree w = 0 := by omega
    simp only [hz, Nat.add_zero] at hd
    rwa [← hd]
  have hcapH := even_degree_cap_of_even_preserved (G := G) (H := H)
    hlt.le hkeep 3 hcap
  apply proper_puncture_floor hlt hcapH hmin
  intro C hC
  have hc : ∀ w ∈ C.supp, H.neighborSet w ⊆ C.supp :=
    fun _ hw _ ha => C.mem_supp_of_adj_mem_supp hw ha
  have hk : ∀ w : C.supp, Even ((H.induce C.supp).degree w) →
      Even (G.degree (w : V)) := by
    intro w hw
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc w w.property)] at hw
    exact hkeep w hw
  have hmap : ∀ ⦃a b : C.supp⦄, (H.induce C.supp).Adj a b → G.Adj a b :=
    fun {_ _} ha => ha.1
  obtain ⟨u, huC, v, huv, hnuv⟩ :=
    puncture_closed_boundary_nonempty hconn hlt C.supp C.nonempty_supp hc
  have hFu : F.Adj u v := by
    by_contra hn
    exact hnuv ⟨huv, hn⟩
  have hpu : 0 < F.degree u := (F.degree_pos_iff_exists_adj u).mpr ⟨v, hFu⟩
  have ho : Odd ((H.induce C.supp).degree ⟨u, huC⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc u huC)]
    exact hodd u hpu
  have huOdd : Odd (G.degree u) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact Nat.not_even_iff_odd.mpr ho
      (hC.even_image_reflects (Function.Embedding.subtype _) hmap ht hk ⟨u, huC⟩ he)
  obtain ⟨w, huw, hwEven⟩ := hneighbor u huOdd hpu
  obtain ⟨a, hua, haEven, _⟩ := hC.even_neighbor_ne ⟨u, huC⟩ ⟨u, huC⟩
  let q : evenVertices G := ⟨(a : V), hk a haEven⟩
  let r : evenVertices G := ⟨w, hwEven⟩
  let E := (evenSubgraph G).connectedComponentMk q
  let T := (evenSubgraph G).connectedComponentMk r
  have hqE : q ∈ E.supp := by simp [E, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hrT : r ∈ T.supp := by simp [T, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hET := minimal_counterexample_odd_neighbors_one_component u huOdd
    hconn hcap hnot hset hmin E T ⟨q, hqE, hmap hua⟩ ⟨r, hrT, hle huw⟩
  have hr : (evenSubgraph G).Reachable q r := SimpleGraph.ConnectedComponent.exact hET
  obtain ⟨b, hb, hbw⟩ := hC.even_image_reachable (Function.Embedding.subtype _)
    hmap ht hk a haEven r hr
  rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc b b.property)] at hb
  have hbw' : (b : V) = w := hbw
  rw [hbw'] at hb
  have hpw : 0 < F.degree w := (F.degree_pos_iff_exists_adj w).mpr ⟨u, huw.symm⟩
  exact Nat.not_even_iff_odd.mpr (hodd w hpw) hb

end Gallai
