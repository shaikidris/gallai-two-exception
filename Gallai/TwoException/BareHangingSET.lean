/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.ESETAssembly
public import Gallai.Inputs.HangingESET
public import Gallai.TwoException.BareMinimality

@[expose] public section

/-! # Hanging-SET assembly for the bare prescribed-vertex induction

This module is the reconstruction half of the hanging-SET reduction.  It is
deliberately parameterized by the literal pruned subtype graph and its two
embeddings.  A later structural lemma must construct these data by deleting
the non-joint vertices of a hanging induced SET; no such deletion fact is
assumed here.
-/

namespace Gallai.TwoException

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A smaller bare instance and a SET core meeting it only at a nontrivial
joint reconstruct the original bare conclusion.  The explicit budget premise
is the exact cardinality arithmetic supplied by the later vertex-deletion
lemma.  The endpoint-aware hanging absorber keeps the prescribed `h` reserve
outside the SET core. -/
theorem bare_hanging_set_assembly
    (h x : V) (H : BareMinimalCounterexample G h x)
    {U W : Type u} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (J : SimpleGraph U) [DecidableRel J.Adj] (K : SimpleGraph W)
    [DecidableRel K.Adj] (f : U ↪ V) (g : W ↪ V)
    (hU xU qU : U) (qK : W)
    (hsmall : Fintype.card U < Fintype.card V)
    (hJ : BareInstance J hU xU) (hfu : f hU = h)
    (hK : IsSET K) (hjoint : f qU = g qK)
    (hpos : ∃ t, (J.map f).Adj (g qK) t)
    (hmeet : ∀ w, (∃ t, (J.map f).Adj w t) → w ∈ Set.range g → w = g qK)
    (hhoutside : h ∉ Set.range g)
    (hgraph : G = K.map g ⊔ J.map f)
    (hbudget : (Fintype.card W + 1) / 2 + (Fintype.card U + 1) / 2 - 1 ≤
      (Fintype.card V + 1) / 2) :
    BareConclusion G h := by
  classical
  obtain ⟨D, hDsize, hDh⟩ := H.of_vertex_smaller U J hU xU hsmall hJ
  obtain ⟨E, hEsize, hEh⟩ := (hK.isESETAt qK).absorb_hanging_endpoint_outside
    g (D.map f) (by simpa [hjoint] using hpos) hmeet h hhoutside
  simp only [Decomposition.map_size] at hEsize
  have hmap : (D.map f).endpointCount h = D.endpointCount hU := by
    rw [← hfu]
    exact D.map_endpointCount f hU
  have castSize {L M : SimpleGraph V} (e : L = M) (P : Decomposition L) :
      (e ▸ P).size = P.size := by subst M; rfl
  have castEnds {L M : SimpleGraph V} (e : L = M) (P : Decomposition L) (v : V) :
      (e ▸ P).endpointCount v = P.endpointCount v := by subst M; rfl
  refine ⟨hgraph.symm ▸ E, ?_, ?_⟩
  · rw [castSize hgraph.symm E]
    omega
  · rw [castEnds hgraph.symm E h, hEh, hmap]
    exact hDh

/-- In a bare instance, the prescribed vertex cannot be the external endpoint
of a hanging SET boundary whose SET endpoint is even in the original graph.
This is the literal `a ≠ h` guard needed before the SET is pruned. -/
theorem bare_hanging_boundary_not_prescribed
    (h x q : V) (H : BareInstance G h x) (hq : Even (G.degree q)) :
    ¬ G.Adj h q := by
  intro hAdj
  have hmem : q ∈ evenNeighbors G h :=
    (mem_evenNeighbors h q).mpr ⟨hAdj, hq⟩
  have hzero := H.2.2.2.2.2.1
  change (evenNeighbors G h).card = 0 at hzero
  have hpos : 0 < (evenNeighbors G h).card := Finset.card_pos.mpr ⟨q, hmem⟩
  omega

/-- If an induced piece has exactly one boundary edge `q-a`, retaining only
the joint `q` turns it into a leaf in the pruned induced graph.  This is the
local graph-theoretic part of the hanging-SET puncture; connectivity, parity,
and the smaller bare-instance transport are deliberately separate. -/
theorem hanging_retained_joint_degree_one
    (C : Set V) [DecidablePred (· ∈ C)] (q a : V)
    (hqC : q ∈ C) (haC : a ∉ C) (hqa : G.Adj q a)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q ∧ v = a) :
    (G.induce (Cᶜ ∪ {q})).degree ⟨q, Or.inr rfl⟩ = 1 := by
  classical
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨⟨a, Or.inl haC⟩, ?_, ?_⟩
  · exact hqa
  · intro w hqw
    change G.Adj q w.val at hqw
    rcases w.property with hwout | hwq
    · obtain ⟨_, hwa⟩ := hboundary q w.val hqC hwout hqw
      apply Subtype.ext
      exact hwa
    · have hwq' : w.val = q := by simpa using hwq
      have hloop : G.Adj q q := by simpa [hwq'] using hqw
      exact (G.irrefl hloop).elim

/-- Retaining only the joint of a nontrivial hanging piece strictly lowers the
vertex type.  The witness `r` is a deleted core vertex distinct from the
joint; graph connectivity and parity play no role in this cardinal step. -/
theorem hanging_pruned_card_lt
    (C : Set V) [DecidablePred (· ∈ C)] (q r : V)
    (hrC : r ∈ C) (hrq : r ≠ q) :
    Fintype.card {v : V // v ∈ Cᶜ ∪ {q}} < Fintype.card V := by
  apply Fintype.card_subtype_lt
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact fun h => h.elim (fun hnot => hnot hrC) (fun heq => hrq heq)

/-- A connected graph remains connected after deleting every vertex of a
piece except its sole boundary joint.  The proof transports an ambient walk:
while it travels inside the deleted core, the retained-reachability invariant
is vacuous; its next return to the retained graph is forced to occur at `q`. -/
theorem hanging_pruned_connected
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hconn : G.Connected)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q) :
    (G.induce (Cᶜ ∪ {q})).Connected := by
  classical
  let T : Set V := Cᶜ ∪ {q}
  let R := G.induce T
  have hqT : q ∈ T := Or.inr rfl
  have transport : ∀ {u v : V}, G.Walk u v →
      (∀ hu : u ∈ T, R.Reachable ⟨q, hqT⟩ ⟨u, hu⟩) →
      ∀ hv : v ∈ T, R.Reachable ⟨q, hqT⟩ ⟨v, hv⟩ := by
    intro u v p
    induction p with
    | nil =>
        intro hu hv
        exact hu hv
    | @cons u v w huv p ih =>
        intro hu hw
        apply ih ?_ hw
        intro hv
        by_cases huT : u ∈ T
        · exact (hu huT).trans (show R.Adj ⟨u, huT⟩ ⟨v, hv⟩ from huv).reachable
        · have huC : u ∈ C := by
            by_contra huC
            exact huT (Or.inl huC)
          change v ∉ C ∨ v = q at hv
          rcases hv with hvout | hvq
          · have huq := hboundary u v huC hvout huv
            subst u
            exact (show R.Adj ⟨q, hqT⟩ ⟨v, Or.inl hvout⟩ from huv).reachable
          · subst v
            exact SimpleGraph.Reachable.refl _
  let : Nonempty T := ⟨⟨q, hqT⟩⟩
  refine ⟨fun a b => ?_⟩
  have reach (v : T) : R.Reachable ⟨q, hqT⟩ v := by
    obtain ⟨p⟩ := hconn q v.val
    exact transport p (fun _ => SimpleGraph.Reachable.refl _) v.property
  exact (reach a).symm.trans (reach b)

/-- Away from the retained joint, every retained vertex keeps its complete
ambient neighbourhood after the hanging-core puncture.  An edge to the core
can only meet the joint, which is retained. -/
theorem hanging_pruned_neighbor_closed
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (v : (Cᶜ ∪ {q} : Set V)) (hvq : v.val ≠ q) :
  G.neighborSet v.val ⊆ Cᶜ ∪ {q} := by
  have hvout : v.val ∉ C := by
    have hvT : v.val ∉ C ∨ v.val = q := by
      simpa only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff] using v.property
    exact hvT.resolve_right hvq
  intro w hw
  by_cases hwC : w ∈ C
  · right
    exact hboundary w v.val hwC hvout hw.symm
  · exact Or.inl hwC

/-- The ambient neighbour finset of a retained non-joint vertex is exactly the
mapped neighbour finset after the hanging-core puncture.  This explicit finset
identity is stable across the subtype enumeration used by the induced graph. -/
theorem hanging_pruned_map_neighborFinset_eq
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (v : (Cᶜ ∪ {q} : Set V)) (hvq : v.val ≠ q) :
    ((G.induce (Cᶜ ∪ {q})).neighborFinset v).map (Function.Embedding.subtype _) =
      G.neighborFinset v.val := by
  ext w
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hvz, rfl⟩
    exact hvz
  · intro hvw
    refine ⟨⟨w, hanging_pruned_neighbor_closed (G := G) C q hboundary v hvq hvw⟩,
      hvw, rfl⟩

/-- Every retained non-joint vertex preserves its ordinary degree under the
hanging-core puncture. -/
theorem hanging_pruned_degree_eq
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (v : (Cᶜ ∪ {q} : Set V)) (hvq : v.val ≠ q) :
    (G.induce (Cᶜ ∪ {q})).degree v = G.degree v.val := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  calc
    ((G.induce (Cᶜ ∪ {q})).neighborFinset v).card =
        (((G.induce (Cᶜ ∪ {q})).neighborFinset v).map
          (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
    _ = (G.neighborFinset v.val).card := congrArg Finset.card
      (hanging_pruned_map_neighborFinset_eq (G := G) C q hboundary v hvq)

/-- Every even neighbour of a retained non-joint vertex in the pruned graph
was already an even neighbour in the ambient graph.  The only retained vertex
whose degree can change is the joint `q`; its odd leaf degree excludes it from
the induced even-neighbour finset. -/
theorem hanging_pruned_evenNeighbors_subset
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (hqodd : Odd ((G.induce (Cᶜ ∪ {q})).degree ⟨q, Or.inr rfl⟩))
    (v : (Cᶜ ∪ {q} : Set V)) (hvq : v.val ≠ q) :
    (evenNeighbors (G.induce (Cᶜ ∪ {q})) v).map (Function.Embedding.subtype _) ⊆
      evenNeighbors G v.val := by
  intro w hw
  obtain ⟨t, ht, htw⟩ := Finset.mem_map.mp hw
  change t.val = w at htw
  subst w
  obtain ⟨hvt, hteven⟩ := (mem_evenNeighbors v t).mp ht
  refine (mem_evenNeighbors v.val t.val).mpr ⟨hvt, ?_⟩
  have htq : t.val ≠ q := by
    intro htq
    have hteq : t = ⟨q, Or.inr rfl⟩ := Subtype.ext htq
    rw [hteq] at hteven
    exact (Nat.not_even_iff_odd.mpr hqodd) hteven
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hteven
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hmap := hanging_pruned_map_neighborFinset_eq (G := G) C q hboundary t htq
  have hmapeven : Even (((G.induce (Cᶜ ∪ {q})).neighborFinset t).map
      (Function.Embedding.subtype _)).card := by
    simpa only [Finset.card_map] using hteven
  exact (congrArg Finset.card hmap) ▸ hmapeven

/-- The hanging-core puncture cannot increase the E-degree of a retained
non-joint even vertex.  This is the cap-transport form consumed by the
smaller bare instance. -/
theorem hanging_pruned_eDegree_le
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (hqodd : Odd ((G.induce (Cᶜ ∪ {q})).degree ⟨q, Or.inr rfl⟩))
    (v : (Cᶜ ∪ {q} : Set V)) (hvq : v.val ≠ q) :
    eDegree (G.induce (Cᶜ ∪ {q})) v ≤ eDegree G v.val := by
  change (evenNeighbors (G.induce (Cᶜ ∪ {q})) v).card ≤ (evenNeighbors G v.val).card
  have hsub := hanging_pruned_evenNeighbors_subset (G := G) C q hboundary hqodd v hvq
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_map] using hcard

/-- The retained-joint puncture is again a bare instance whenever both
designated vertices remain away from the odd retained leaf.  The hypotheses
on membership and inequality are kept literal here; the hanging-SET consumer
must derive them from its actual component embedding. -/
theorem hanging_pruned_bareInstance
    (C : Set V) [DecidablePred (· ∈ C)] (q h x : V)
    (H : BareInstance G h x)
    (hhT : h ∈ Cᶜ ∪ {q}) (hxT : x ∈ Cᶜ ∪ {q})
    (hhq : h ≠ q) (hxq : x ≠ q)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q)
    (hqodd : Odd ((G.induce (Cᶜ ∪ {q})).degree ⟨q, Or.inr rfl⟩)) :
    BareInstance (G.induce (Cᶜ ∪ {q})) ⟨h, hhT⟩ ⟨x, hxT⟩ := by
  let hT : (Cᶜ ∪ {q} : Set V) := ⟨h, hhT⟩
  let xT : (Cᶜ ∪ {q} : Set V) := ⟨x, hxT⟩
  have hconn : (G.induce (Cᶜ ∪ {q})).Connected :=
    hanging_pruned_connected (G := G) C q H.1 hboundary
  have hhdeg : (G.induce (Cᶜ ∪ {q})).degree hT = G.degree h :=
    hanging_pruned_degree_eq (G := G) C q hboundary hT hhq
  have hxdeg : (G.induce (Cᶜ ∪ {q})).degree xT = G.degree x :=
    hanging_pruned_degree_eq (G := G) C q hboundary xT hxq
  refine ⟨hconn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    apply H.2.1
    exact congrArg Subtype.val hEq
  · rw [show (⟨h, hhT⟩ : (Cᶜ ∪ {q} : Set V)) = hT from rfl, hhdeg]
    exact H.2.2.1
  · rw [show (⟨h, hhT⟩ : (Cᶜ ∪ {q} : Set V)) = hT from rfl, hhdeg]
    exact H.2.2.2.1
  · rw [show (⟨x, hxT⟩ : (Cᶜ ∪ {q} : Set V)) = xT from rfl, hxdeg]
    exact H.2.2.2.2.1
  · apply Nat.eq_zero_of_le_zero
    refine (hanging_pruned_eDegree_le (G := G) C q hboundary hqodd hT hhq).trans ?_
    exact Nat.le_of_eq H.2.2.2.2.2.1
  · intro v hveven hvh hvx
    have hvq : v.val ≠ q := by
      intro hvq
      have hvEq : v = ⟨q, Or.inr rfl⟩ := Subtype.ext hvq
      rw [hvEq] at hveven
      exact (Nat.not_even_iff_odd.mpr hqodd) hveven
    have hvambient : Even (G.degree v.val) := by
      rw [← hanging_pruned_degree_eq (G := G) C q hboundary v hvq]
      exact hveven
    refine (hanging_pruned_eDegree_le (G := G) C q hboundary hqodd v hvq).trans ?_
    apply H.2.2.2.2.2.2
    · exact hvambient
    · intro hvh'
      apply hvh
      exact Subtype.ext hvh'
    · intro hvx'
      apply hvx
      exact Subtype.ext hvx'

/-- A literal hanging-core boundary partitions every ambient edge between the
core induced graph and the retained-joint puncture.  The shared vertex is
`q`; the unique crossing edge is retained on the puncture side. -/
theorem hanging_pruned_union_eq
    (C : Set V) [DecidablePred (· ∈ C)] (q a : V)
    (hqC : q ∈ C) (haC : a ∉ C)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q ∧ v = a) :
    G = (G.induce C).map (Function.Embedding.subtype _) ⊔
      (G.induce (Cᶜ ∪ {q})).map (Function.Embedding.subtype _) := by
  ext u v
  constructor
  · intro huv
    by_cases huC : u ∈ C
    · by_cases hvC : v ∈ C
      · left
        rw [SimpleGraph.map_adj]
        exact ⟨⟨u, huC⟩, ⟨v, hvC⟩, huv, rfl, rfl⟩
      · right
        obtain ⟨huq, hva⟩ := hboundary u v huC hvC huv
        subst u
        subst v
        rw [SimpleGraph.map_adj]
        exact ⟨⟨q, Or.inr rfl⟩, ⟨a, Or.inl haC⟩, huv, rfl, rfl⟩
    · by_cases hvC : v ∈ C
      · right
        obtain ⟨hvq, hua⟩ := hboundary v u hvC huC huv.symm
        subst u
        subst v
        rw [SimpleGraph.map_adj]
        exact ⟨⟨a, Or.inl haC⟩, ⟨q, Or.inr rfl⟩, huv, rfl, rfl⟩
      · right
        rw [SimpleGraph.map_adj]
        exact ⟨⟨u, Or.inl huC⟩, ⟨v, Or.inl hvC⟩, huv, rfl, rfl⟩
  · intro huv
    rcases huv with huv | huv
    · obtain ⟨u', v', huv', hu', hv'⟩ := (SimpleGraph.map_adj _ _ u v).mp huv
      simpa [hu', hv'] using huv'
    · obtain ⟨u', v', huv', hu', hv'⟩ := (SimpleGraph.map_adj _ _ u v).mp huv
      simpa [hu', hv'] using huv'

/-- The core and retained-joint puncture have the exact ceiling budget in an
even-order bare counterexample.  A SET core has odd order and overlaps the
puncture exactly at `q`, so the saved absorber path is precisely the required
one-unit slack. -/
theorem hanging_pruned_exact_budget
    (h x : V) (H : BareMinimalCounterexample G h x)
    (C : Set V) [DecidablePred (· ∈ C)] (q : V)
    (hqC : q ∈ C) (hset : IsSET (G.induce C)) :
    (Fintype.card C + 1) / 2 +
        (Fintype.card (Cᶜ ∪ {q} : Set V) + 1) / 2 - 1 ≤
          (Fintype.card V + 1) / 2 := by
  let T : Set V := Cᶜ ∪ {q}
  have hcover : C ∪ T = Set.univ := by
    ext v
    by_cases hv : v ∈ C <;> simp [T, hv]
  have hinter : C ∩ T = {q} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvC, hvT⟩
      rcases hvT with hvnot | hvq
      · exact (hvnot hvC).elim
      · exact hvq
    · intro hvq
      subst v
      exact ⟨hqC, Or.inr rfl⟩
  have hcard := card_cover_single_inter C T q hcover hinter
  change (Fintype.card C + 1) / 2 +
      (Fintype.card T + 1) / 2 - 1 ≤ (Fintype.card V + 1) / 2
  exact ceiling_one_vertex_budget (Fintype.card C) (Fintype.card T)
    (Fintype.card V) (by simpa [T] using hcard)

/-- A literal induced hanging SET with its one-boundary puncture contradicts
the relative bare minimal counterexample once its exact vertex-budget identity
is supplied.  This is the consumer that joins the checked puncture topology,
smaller bare-instance transport, and endpoint-aware SET assembly.  It keeps
the finite cardinal arithmetic explicit: deriving that identity from a
particular SET component is the remaining structural extraction step. -/
theorem bare_hanging_set_literal_false
    (h x : V) (H : BareMinimalCounterexample G h x)
    (C : Set V) [DecidablePred (· ∈ C)] (q a r : V)
    (hqC : q ∈ C) (haC : a ∉ C) (hrC : r ∈ C) (hrq : r ≠ q)
    (hhC : h ∉ C) (hxC : x ∉ C)
    (hqa : G.Adj q a)
    (hboundary : ∀ u v, u ∈ C → v ∉ C → G.Adj u v → u = q ∧ v = a)
    (hset : IsSET (G.induce C)) :
    False := by
  classical
  let T : Set V := Cᶜ ∪ {q}
  let J : SimpleGraph T := G.induce T
  let K : SimpleGraph C := G.induce C
  let f : T ↪ V := Function.Embedding.subtype _
  let g : C ↪ V := Function.Embedding.subtype _
  let qT : T := ⟨q, Or.inr rfl⟩
  let qK : C := ⟨q, hqC⟩
  let hT : T := ⟨h, Or.inl hhC⟩
  let xT : T := ⟨x, Or.inl hxC⟩
  have hbare := H.counterexample.1
  have hhq : h ≠ q := by
    intro heq
    exact hhC (heq.symm ▸ hqC)
  have hxq : x ≠ q := by
    intro heq
    exact hxC (heq.symm ▸ hqC)
  have hqdegree : J.degree qT = 1 := by
    change (G.induce (Cᶜ ∪ {q})).degree ⟨q, Or.inr rfl⟩ = 1
    exact hanging_retained_joint_degree_one (G := G) C q a hqC haC hqa hboundary
  have hqodd : Odd (J.degree qT) := by
    rw [hqdegree]
    exact ⟨0, by omega⟩
  have hJ : BareInstance J hT xT := by
    change BareInstance (G.induce (Cᶜ ∪ {q})) ⟨h, Or.inl hhC⟩ ⟨x, Or.inl hxC⟩
    exact hanging_pruned_bareInstance (G := G) C q h x hbare
      (Or.inl hhC) (Or.inl hxC) hhq hxq
      (fun u v hu hv huv => (hboundary u v hu hv huv).1)
      (by simpa [J, qT] using hqodd)
  have hsmall : Fintype.card T < Fintype.card V := by
    change Fintype.card {v : V // v ∈ Cᶜ ∪ {q}} < Fintype.card V
    exact hanging_pruned_card_lt C q r hrC hrq
  have hjoint : f qT = g qK := rfl
  have hpos : ∃ t, (J.map f).Adj (g qK) t := by
    refine ⟨a, ?_⟩
    rw [SimpleGraph.map_adj]
    exact ⟨qT, ⟨a, Or.inl haC⟩, hqa, rfl, rfl⟩
  have hmeet : ∀ w, (∃ t, (J.map f).Adj w t) → w ∈ Set.range g → w = g qK := by
    intro w hw hrange
    rcases hw with ⟨t, hwt⟩
    rcases (SimpleGraph.map_adj f J w t).mp hwt with ⟨u, v, huv, hfu, hfv⟩
    rcases hrange with ⟨c, hc⟩
    change u.val = w at hfu
    change c.val = w at hc
    have huc : u.val = c.val := by
      calc
        u.val = w := hfu
        _ = c.val := hc.symm
    have hcT : c.val ∈ Cᶜ ∪ {q} := by
      have huT : u.val ∈ Cᶜ ∪ {q} := by simpa [T] using u.property
      simpa [huc] using huT
    have hcq : c.val = q := by
      rcases hcT with hcnot | hcq
      · exact (hcnot c.property).elim
      · exact hcq
    have ceq : c = qK := Subtype.ext hcq
    subst c
    exact hc.symm
  have hhoutside : h ∉ Set.range g := by
    rintro ⟨c, hc⟩
    apply hhC
    change c.val = h at hc
    have hch : c.val = h := hc
    simpa [hch] using c.property
  have hgraph : G = K.map g ⊔ J.map f := by
    change G = (G.induce C).map (Function.Embedding.subtype _) ⊔
      (G.induce (Cᶜ ∪ {q})).map (Function.Embedding.subtype _)
    exact hanging_pruned_union_eq (G := G) C q a hqC haC hboundary
  have hbudget' : (Fintype.card C + 1) / 2 + (Fintype.card T + 1) / 2 - 1 ≤
      (Fintype.card V + 1) / 2 := by
    simpa [T] using hanging_pruned_exact_budget h x H C q hqC hset
  have hconclusion : BareConclusion G h :=
    bare_hanging_set_assembly h x H J K f g hT xT qT qK hsmall hJ rfl hset hjoint
      hpos hmeet hhoutside hgraph hbudget'
  exact H.counterexample.2 hconclusion

end Gallai.TwoException
