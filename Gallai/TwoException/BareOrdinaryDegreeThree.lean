/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareOrdinaryDegreeOne
public import Gallai.Inputs.OddEvenStarRestore
public import Gallai.Structure.StarPunctureException

@[expose] public section

/-! # Ordinary three-star restoration in the bare two-exception kernel -/

namespace Gallai.TwoException

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance ordinaryThreeStarAdj (a : V) :
    DecidableRel (evenStarPuncture G a).Adj := fun _ _ => Classical.propDecidable _

/-- Restoring the complete even-neighbour star of an ordinary E-degree-three
vertex preserves the prescribed bare vertex's endpoint count. Leaf caps and
the off-star guard are derived from the actual ordinary component. -/
theorem restore_ordinary_three_star_preserves_bare
    (z a : evenVertices G) (h : V)
    (H : BareCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3)
    (D : Decomposition (evenStarPuncture G (a : V))) :
    ∃ E : Decomposition G, E.size = D.size ∧ E.endpointCount h = D.endpointCount h := by
  classical
  have hcap : ∀ v ∈ evenNeighbors G (a : V), eDegree G v ≤ 3 := by
    intro v hv
    obtain ⟨hav, hvEven⟩ := (mem_evenNeighbors (a : V) v).mp hv
    let ve : evenVertices G := ⟨v, hvEven⟩
    have hvC : ve ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hav
    have hvz : v ≠ (z : V) := by
      intro heq
      exact hz (by simpa only [show ve = z from Subtype.ext heq] using hvC)
    by_cases hvh : v = h
    · rw [hvh, H.1.2.2.2.2.2.1]
      omega
    · exact H.1.2.2.2.2.2.2 v hvEven hvh hvz
  have hha : h ≠ (a : V) := by
    intro heq
    have hb := H.1.2.2.2.2.2.1
    rw [heq, hthree] at hb
    omega
  have hhS : h ∉ evenNeighbors G (a : V) := by
    intro hh
    have hah := ((mem_evenNeighbors (a : V) h).mp hh).1
    have haN : (a : V) ∈ evenNeighbors G h :=
      (mem_evenNeighbors h (a : V)).mpr ⟨hah.symm, a.property⟩
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp H.1.2.2.2.2.2.1
    simpa [hempty] using haN
  obtain ⟨E, hs, _, he⟩ := D.restore_odd_even_star_exposing_preserving (a : V)
    a.property (by rw [hthree]; decide) hcap
  exact ⟨E, hs, he h hha hhS⟩

/-- A ceiling-budget puncture exposing h contradicts bare failure after the
ordinary three-star is restored. The puncture budget remains a separate
structural obligation. -/
theorem bare_ordinary_three_star_false_of_puncture_conclusion
    (z a : evenVertices G) (h : V)
    (H : BareCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3)
    (hP : BareConclusion (evenStarPuncture G (a : V)) h) : False := by
  obtain ⟨D, hD, hhD⟩ := hP
  obtain ⟨E, hs, he⟩ := restore_ordinary_three_star_preserves_bare z a h H C hz ha hthree D
  apply H.2
  exact ⟨E, hs.le.trans hD, by rw [he]; exact hhD⟩

/-- The connected ordinary three-star puncture is reducible by the same
literal relative minimality used for the ordinary one-edge puncture. -/
theorem bare_ordinary_three_star_connected_false
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3)
    (hP : (evenStarPuncture G (a : V)).Connected) : False := by
  classical
  let P := evenStarPuncture G (a : V)
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.counterexample.1
  have hha : h ≠ (a : V) := by
    intro heq
    rw [heq, hthree] at hhbare
    omega
  have hza : (z : V) ≠ (a : V) := by
    intro heq
    exact hz (by simpa only [show z = a from Subtype.ext heq] using ha)
  have hhS : h ∉ evenNeighbors G (a : V) := by
    intro hh
    have hah := ((mem_evenNeighbors (a : V) h).mp hh).1
    have haN := (mem_evenNeighbors h (a : V)).mpr ⟨hah.symm, a.property⟩
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhbare
    simpa [hempty] using haN
  have hzS : (z : V) ∉ evenNeighbors G (a : V) := by
    intro hzN
    exact hz (C.mem_supp_of_adj_mem_supp ha ((mem_evenNeighbors (a : V) (z : V)).mp hzN).1)
  have hhd : P.degree h = G.degree h :=
    starPuncture_degree_other G (a : V) (evenNeighbors G (a : V)) h hha hhS
  have hzd : P.degree (z : V) = G.degree (z : V) :=
    starPuncture_degree_other G (a : V) (evenNeighbors G (a : V)) (z : V) hza hzS
  have hkeep : ∀ v, Even (P.degree v) → Even (G.degree v) := by
    intro v hv
    by_cases hva : v = (a : V)
    · rw [hva]
      exact a.property
    · exact (evenStarPuncture_even_off_center G (a : V) v hva hv).1
  have hle : P ≤ G := fun _ _ hadj => hadj.1
  have hmono : ∀ v, eDegree P v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation hle hkeep
  have hinst : BareInstance P h (z : V) := by
    refine ⟨hP, hhz, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [hhd]
    · rwa [hhd]
    · rwa [hzd]
    · have hb := hmono h
      rw [hhbare] at hb
      omega
    · intro v hv hvh hvz
      exact (hmono v).trans (hcap v (hkeep v hv) hvh hvz)
  have hlt := evenStarPuncture_edge_count_lt G (a : V) (by rw [hthree]; omega)
  have hout := H.of_edge_smaller V P h (z : V) rfl hlt hinst
  exact bare_ordinary_three_star_false_of_puncture_conclusion z a h H.counterexample
    C hz ha hthree hout

/-- The full ordinary three-star puncture keeps the designated vertices in
one component, because the even centre cannot separate them. -/
theorem bare_ordinary_three_star_designated_reachable
    (z a : evenVertices G) (h : V)
    (H : BareCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3) :
    (evenStarPuncture G (a : V)).Reachable h (z : V) := by
  classical
  have hha : h ≠ (a : V) := by
    intro heq
    have hb := H.1.2.2.2.2.2.1
    rw [heq, hthree] at hb
    omega
  have hza : (z : V) ≠ (a : V) := by
    intro heq
    exact hz (by simpa only [show z = a from Subtype.ext heq] using ha)
  have hr : (G.induce {v | v ≠ (a : V)}).Reachable
      ⟨h, hha⟩ ⟨(z : V), hza⟩ := by
    by_contra hnot
    exact bare_even_separator_separating_hubs_false G (a : V) h (z : V)
      H hha.symm hza.symm a.property hnot
  let φ : (G.induce {v | v ≠ (a : V)}) →g (evenStarPuncture G (a : V)) :=
    { toFun := Subtype.val
      map_rel' := by
        intro v w hvw
        refine (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hvw, ?_⟩
        intro hstar
        exact w.property ((star_sup_adj_off_center (a : V) (evenNeighbors G (a : V))
          v.val w.val v.property).mp hstar).2 }
  exact hr.map φ

/-- The actual protected component of an ordinary three-star puncture is a
native bare instance. Outside vertices are not included as isolated vertices
in the recursive input. -/
theorem bare_ordinary_three_star_component_instance
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hhB : h ∈ B.supp) (hzB : (z : V) ∈ B.supp) :
    BareInstance ((evenStarPuncture G (a : V)).induce B.supp)
      ⟨h, hhB⟩ ⟨(z : V), hzB⟩ := by
  classical
  let P := evenStarPuncture G (a : V)
  obtain ⟨_, hhz, hhpos, hheven, hzeven, hhbare, hcap⟩ := H.counterexample.1
  have hha : h ≠ (a : V) := by
    intro heq
    rw [heq, hthree] at hhbare
    omega
  have hza : (z : V) ≠ (a : V) := by
    intro heq
    exact hz (by simpa only [show z = a from Subtype.ext heq] using ha)
  have hhS : h ∉ evenNeighbors G (a : V) := by
    intro hh
    have hah := ((mem_evenNeighbors (a : V) h).mp hh).1
    have haN := (mem_evenNeighbors h (a : V)).mpr ⟨hah.symm, a.property⟩
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhbare
    simpa [hempty] using haN
  have hzS : (z : V) ∉ evenNeighbors G (a : V) := by
    intro hzN
    exact hz (C.mem_supp_of_adj_mem_supp ha ((mem_evenNeighbors (a : V) (z : V)).mp hzN).1)
  have hhd : P.degree h = G.degree h :=
    starPuncture_degree_other G (a : V) (evenNeighbors G (a : V)) h hha hhS
  have hzd : P.degree (z : V) = G.degree (z : V) :=
    starPuncture_degree_other G (a : V) (evenNeighbors G (a : V)) (z : V) hza hzS
  have hkeep : ∀ v, Even (P.degree v) → Even (G.degree v) := by
    intro v hv
    by_cases hva : v = (a : V)
    · rw [hva]; exact a.property
    · exact (evenStarPuncture_even_off_center G (a : V) v hva hv).1
  have hmono : ∀ v, eDegree P v ≤ eDegree G v :=
    eDegree_le_of_subgraph_of_even_preservation (fun _ _ hadj => hadj.1) hkeep
  have hclosed : ∀ v ∈ B.supp, P.neighborSet v ⊆ B.supp := by
    intro v hv w hvw
    exact B.mem_supp_of_adj_mem_supp hv hvw
  have hdeg : ∀ v : B.supp, (P.induce B.supp).degree v = P.degree v.val := by
    intro v
    exact SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v.val v.property)
  refine ⟨B.connected_toSimpleGraph, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact hhz (congrArg Subtype.val heq)
  · rw [hdeg, hhd]; exact hhpos
  · rw [hdeg, hhd]; exact hheven
  · rw [hdeg, hzd]; exact hzeven
  · rw [eDegree_induce_of_closed P B.supp hclosed]
    have hb := hmono h
    rw [hhbare] at hb
    exact Nat.le_zero.mp hb
  · intro v hv hvh hvz
    have hvP : Even (P.degree v.val) := by rwa [hdeg] at hv
    rw [eDegree_induce_of_closed P B.supp hclosed]
    exact (hmono v.val).trans (hcap v.val (hkeep v.val hvP)
      (fun heq => hvh (Subtype.ext heq)) (fun heq => hvz (Subtype.ext heq)))

/-- A proper protected component of the three-star puncture receives its
ceiling budget and h's endpoint reserve from strict vertex minimality. -/
theorem bare_ordinary_three_star_protected_conclusion
    (z a : evenVertices G) (h r : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hhB : h ∈ B.supp) (hzB : (z : V) ∈ B.supp) (hr : r ∉ B.supp) :
    BareConclusion ((evenStarPuncture G (a : V)).induce B.supp) ⟨h, hhB⟩ := by
  classical
  exact H.of_vertex_smaller B.supp _ ⟨h, hhB⟩ ⟨(z : V), hzB⟩
    (Fintype.card_subtype_lt hr)
    (bare_ordinary_three_star_component_instance z a h H C hz ha hthree B hhB hzB)

/-- A SET component of the three-star puncture cannot contain its centre.
All surviving neighbours of the centre are odd, so its E-degree is zero. -/
theorem ordinary_three_star_center_component_not_set
    (a : evenVertices G) (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (haB : (a : V) ∈ B.supp) :
    ¬ IsSET ((evenStarPuncture G (a : V)).induce B.supp) := by
  classical
  let P := evenStarPuncture G (a : V)
  have hzero : eDegree P (a : V) = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hadj, heven⟩ := (mem_evenNeighbors (G := P) (a : V) v).mp hv
    exact evenStarPuncture_no_even_neighbor G (a : V) v hadj heven
  have hodd : Odd (P.degree (a : V)) := by
    have hd := evenStarPuncture_degree_center G (a : V)
    have he : Even (G.degree (a : V)) := a.property
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    change P.degree (a : V) + eDegree G (a : V) = G.degree (a : V) at hd
    rw [hthree] at hd
    omega
  exact component_not_set_of_odd_eDegree_zero B (a : V) haB hodd hzero

/-- Any SET component of the ordinary three-star puncture is an induced
SET in the original graph: its centre is outside the component. -/
theorem ordinary_three_star_set_induced_original
    (a : evenVertices G) (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hs : IsSET ((evenStarPuncture G (a : V)).induce B.supp)) :
    (a : V) ∉ B.supp ∧ IsSET (G.induce B.supp) := by
  classical
  have ha : (a : V) ∉ B.supp := fun hm =>
    ordinary_three_star_center_component_not_set a hthree B hm hs
  refine ⟨ha, ?_⟩
  simpa only [induce_evenStarPuncture_eq_of_notMem G (a : V) B.supp ha] using hs

/-- Every original edge leaving a centre-avoiding puncture component is a
deleted spoke, oriented from an even leaf to the centre. -/
theorem ordinary_three_star_component_crossing
    (a : V) (B : (evenStarPuncture G a).ConnectedComponent)
    (ha : a ∉ B.supp) (v w : V) (hv : v ∈ B.supp) (hw : w ∉ B.supp)
    (hvw : G.Adj v w) : v ∈ evenNeighbors G a ∧ w = a := by
  classical
  have hmissing : ¬ (evenStarPuncture G a).Adj v w :=
    fun hp => hw (B.mem_supp_of_adj_mem_supp hv hp)
  have hstar : ((evenNeighbors G a).sup (SimpleGraph.edge a)).Adj v w := by
    by_contra hn
    exact hmissing ((SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hvw, hn⟩)
  exact (star_sup_adj_off_center a (evenNeighbors G a) v w
    (fun he => ha (he ▸ hv))).mp hstar

/-- A puncture component missing the exceptional vertex inherits the full
subcubic even-degree cap. No SET exclusion is assumed or concluded here. -/
theorem bare_ordinary_three_star_component_cap
    (z a : evenVertices G) (h : V) (H : BareCounterexample G h (z : V))
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hz : (z : V) ∉ B.supp) :
    ∀ v, Even (((evenStarPuncture G (a : V)).induce B.supp).degree v) →
      eDegree ((evenStarPuncture G (a : V)).induce B.supp) v ≤ 3 := by
  classical
  let P := evenStarPuncture G (a : V)
  have hcap : ∀ v, Even (G.degree v) → v ≠ (z : V) → eDegree G v ≤ 3 := by
    intro v he hvz
    by_cases hvh : v = h
    · rw [hvh, H.1.2.2.2.2.2.1]; omega
    · exact H.1.2.2.2.2.2.2 v he hvh hvz
  have hPcap := evenStarPuncture_cap_except G (a : V) (z : V) hcap
  have hclosed : ∀ v ∈ B.supp, P.neighborSet v ⊆ B.supp := by
    intro v hv w hvw
    exact B.mem_supp_of_adj_mem_supp hv hvw
  intro v he
  have heP : Even (P.degree v.val) := by
    rwa [SimpleGraph.degree_induce_of_neighborSet_subset
      (hclosed v.val v.property)] at he
  rw [eDegree_induce_of_closed P B.supp hclosed]
  exact hPcap v.val heP (fun heq => hz (heq ▸ v.property))

/-- The SET promotion obstruction only needs the ambient E-degree cap at
the images of its even triangle, not at every ambient even vertex. -/
theorem set_promoted_odd_subsingleton_of_local_cap
    {W : Type*} [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} [DecidableRel J.Adj]
    (hs : IsSET J) (f : W ↪ V)
    (hle : ∀ ⦃v w⦄, J.Adj v w → G.Adj (f v) (f w))
    (hkeep : ∀ v, Even (J.degree v) → Even (G.degree (f v)))
    (hcap : ∀ v, Even (J.degree v) → eDegree G (f v) ≤ 3) :
    Set.Subsingleton {v | Odd (J.degree v) ∧ Even (G.degree (f v))} := by
  classical
  intro v hv w hw
  by_contra hvw
  obtain ⟨t, hvt, hwt, het⟩ := hs.exists_common_even_neighbor_of_odd v w hv.1 hw.1
  have hvN : v ∉ evenNeighbors J t := by
    intro hm
    exact (Nat.not_even_iff_odd.mpr hv.1) ((mem_evenNeighbors t v).mp hm).2
  have hwN : w ∉ evenNeighbors J t := by
    intro hm
    exact (Nat.not_even_iff_odd.mpr hw.1) ((mem_evenNeighbors t w).mp hm).2
  have hsub : (insert v (insert w (evenNeighbors J t))).map f ⊆
      evenNeighbors G (f t) := by
    intro b hb
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_map.mp hb
    rcases Finset.mem_insert.mp hbS with rfl | hbS
    · exact (mem_evenNeighbors (f t) _).mpr ⟨hle hvt.symm, hv.2⟩
    rcases Finset.mem_insert.mp hbS with rfl | hbS
    · exact (mem_evenNeighbors (f t) _).mpr ⟨hle hwt.symm, hw.2⟩
    obtain ⟨htb, heb⟩ := (mem_evenNeighbors t b).mp hbS
    exact (mem_evenNeighbors (f t) (f b)).mpr ⟨hle htb, hkeep b heb⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_insert_of_notMem (by simp [hvw, hvN]),
    Finset.card_insert_of_notMem hwN] at hc
  have ht := hs.eDegree_even t het
  have hu := hcap t het
  unfold eDegree at ht hu
  omega

/-- In a nonprotected SET component of the ordinary three-star puncture,
at most one of the deleted leaves can occur. -/
theorem ordinary_three_star_set_leaves_subsingleton
    (z a : evenVertices G) (h : V) (H : BareCounterexample G h (z : V))
    (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hz : (z : V) ∉ B.supp)
    (hs : IsSET ((evenStarPuncture G (a : V)).induce B.supp)) :
    Set.Subsingleton {v : V | v ∈ B.supp ∧ v ∈ evenNeighbors G (a : V)} := by
  classical
  let P := evenStarPuncture G (a : V)
  let J := P.induce B.supp
  have ha := (ordinary_three_star_set_induced_original a hthree B hs).1
  have hclosed : ∀ v ∈ B.supp, P.neighborSet v ⊆ B.supp := by
    intro v hv w hvw
    exact B.mem_supp_of_adj_mem_supp hv hvw
  have hdeg (v : B.supp) : J.degree v = P.degree v.val :=
    SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v.val v.property)
  have hkeep (v : B.supp) (he : Even (J.degree v)) : Even (G.degree v.val) := by
    rw [hdeg] at he
    have hne : v.val ≠ (a : V) := by
      intro heq
      apply ha
      simpa only [heq] using v.property
    exact (evenStarPuncture_even_off_center G (a : V) v.val hne he).1
  have hcap (v : B.supp) (he : Even (J.degree v)) : eDegree G v.val ≤ 3 := by
    by_cases hvh : v.val = h
    · rw [hvh, H.1.2.2.2.2.2.1]; omega
    · exact H.1.2.2.2.2.2.2 v.val (hkeep v he) hvh
        (fun heq => hz (heq ▸ v.property))
  have hprom := set_promoted_odd_subsingleton_of_local_cap hs
    (Function.Embedding.subtype (· ∈ B.supp))
    (fun {_ _} hvw => hvw.1) hkeep hcap
  intro v hv w hw
  have hodd (b : V) (hb : b ∈ B.supp) (hleaf : b ∈ evenNeighbors G (a : V)) :
      Odd (J.degree ⟨b, hb⟩) := by
    rw [hdeg]
    exact evenStarPuncture_odd_leaf G (a : V) b hleaf
  have heq := hprom ⟨hodd v hv.1 hv.2, ((mem_evenNeighbors (a : V) v).mp hv.2).2⟩
    ⟨hodd w hw.1 hw.2, ((mem_evenNeighbors (a : V) w).mp hw.2).2⟩
  exact congrArg Subtype.val heq

/-- Every component of the nonempty even-star puncture touches a deleted
spoke. If it avoids the centre, that contact is a deleted even leaf. -/
theorem ordinary_three_star_component_has_leaf
    (a : V) (hconn : G.Connected) (hp : 0 < eDegree G a)
    (B : (evenStarPuncture G a).ConnectedComponent) (ha : a ∉ B.supp) :
    ∃ v, v ∈ B.supp ∧ v ∈ evenNeighbors G a := by
  classical
  let P := evenStarPuncture G a
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hp
  have hlt : P < G := by
    refine lt_of_le_not_ge (fun _ _ hab => hab.1) ?_
    intro hle
    exact starPuncture_missing G a (evenNeighbors G a) (by simp) b hb
      (hle ((mem_evenNeighbors a b).mp hb).1)
  obtain ⟨v, hv, w, hvw, hmissing⟩ := puncture_closed_boundary_nonempty
    hconn hlt B.supp B.nonempty_supp
    (fun v hv w hvw => B.mem_supp_of_adj_mem_supp hv hvw)
  have hstar : ((evenNeighbors G a).sup (SimpleGraph.edge a)).Adj v w := by
    by_contra hn
    exact hmissing ((SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hvw, hn⟩)
  exact ⟨v, hv, ((star_sup_adj_off_center a (evenNeighbors G a) v w
    (fun heq => ha (heq ▸ hv))).mp hstar).1⟩

/-- A nonprotected component of the ordinary three-star puncture cannot be
SET: its unique leaf contact makes it a literal hanging SET in G. -/
theorem bare_ordinary_three_star_component_not_set
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hh : h ∉ B.supp) (hz : (z : V) ∉ B.supp) :
    ¬ IsSET ((evenStarPuncture G (a : V)).induce B.supp) := by
  classical
  intro hs
  obtain ⟨ha, hsG⟩ := ordinary_three_star_set_induced_original a hthree B hs
  obtain ⟨v, hv, hvN⟩ := ordinary_three_star_component_has_leaf (a : V)
    H.counterexample.1.1 (by rw [hthree]; omega) B ha
  have huniq := ordinary_three_star_set_leaves_subsingleton z a h
    H.counterexample hthree B hz hs
  let E : Finset B.supp := Finset.univ.filter fun u =>
    Even (((evenStarPuncture G (a : V)).induce B.supp).degree u)
  have hc : E.card = 3 := by simpa [E] using hs.card_even
  obtain ⟨b, c, d, hbc, hbd, hcd, hE⟩ := Finset.card_eq_three.mp hc
  have hex : ∃ r, r ∈ B.supp ∧ r ≠ v := by
    by_cases hb : b.val = v
    · refine ⟨c.val, c.property, ?_⟩
      intro heq
      exact hbc (Subtype.ext (hb.trans heq.symm))
    · exact ⟨b.val, b.property, hb⟩
  obtain ⟨r, hr, hrv⟩ := hex
  refine bare_hanging_set_literal_false h (z : V) H B.supp v (a : V) r
    hv ha hr hrv hh hz ((mem_evenNeighbors (a : V) v).mp hvN).1.symm ?_ hsG
  intro u w hu hw huw
  obtain ⟨huN, hwa⟩ := ordinary_three_star_component_crossing (a : V) B ha
    u w hu hw huw
  exact ⟨huniq ⟨hu, huN⟩ ⟨hv, hvN⟩, hwa⟩

/-- The nonprotected three-star components receive the published floor
budget after the local cap and hanging-SET exclusion are established. -/
theorem bare_ordinary_three_star_component_floor
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (hthree : eDegree G (a : V) = 3)
    (B : (evenStarPuncture G (a : V)).ConnectedComponent)
    (hh : h ∉ B.supp) (hz : (z : V) ∉ B.supp) :
    HasPathBudget ((evenStarPuncture G (a : V)).induce B.supp)
      (Fintype.card B.supp / 2) := by
  classical
  rcases floor_or_set ((evenStarPuncture G (a : V)).induce B.supp) B.connected_toSimpleGraph
    (bare_ordinary_three_star_component_cap z a h H.counterexample B hz) with hf | hs
  · exact hf
  · exact (bare_ordinary_three_star_component_not_set z a h H hthree B hh hz hs).elim

/-- An ordinary E-degree-three vertex is reducible, with both connected
and disconnected punctures accounted for. -/
theorem bare_ordinary_degree_three_false
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp)
    (hthree : eDegree G (a : V) = 3) : False := by
  classical
  let P := evenStarPuncture G (a : V)
  by_cases hP : P.Connected
  · exact bare_ordinary_three_star_connected_false z a h H C hz ha hthree hP
  have hreached := bare_ordinary_three_star_designated_reachable z a h
    H.counterexample C hz ha hthree
  let B₀ := P.connectedComponentMk h
  have hh₀ : h ∈ B₀.supp := rfl
  have hz₀ : (z : V) ∈ B₀.supp :=
    SimpleGraph.ConnectedComponent.eq.mpr hreached.symm
  have hex : ∃ r, ¬ P.Reachable h r := by
    by_contra hnot
    push_neg at hnot
    exact hP (P.connected_iff_exists_forall_reachable.mpr ⟨h, hnot⟩)
  obtain ⟨r, hr⟩ := hex
  have hr₀ : r ∉ B₀.supp := fun hm => hr (B₀.reachable_of_mem_supp hh₀ hm)
  obtain ⟨D, hD, hhD⟩ := bare_ordinary_three_star_protected_conclusion
    z a h r H C hz ha hthree B₀ hh₀ hz₀ hr₀
  have hf : ∀ B : P.ConnectedComponent, B ≠ B₀ →
      HasPathBudget (P.induce B.supp) (Fintype.card B.supp / 2) := by
    intro B hB
    have hhB : h ∉ B.supp := by
      intro hm
      apply hB
      change P.connectedComponentMk h = B at hm
      exact hm.symm
    have hzB : (z : V) ∉ B.supp := by
      intro hm
      apply hB
      change P.connectedComponentMk (z : V) = B at hm
      change P.connectedComponentMk (z : V) = B₀ at hz₀
      exact hm.symm.trans hz₀
    exact bare_ordinary_three_star_component_floor z a h H hthree B hhB hzB
  have hconclusion : BareConclusion P h := assemble_one_ceiling P h D hD hhD hf
  exact bare_ordinary_three_star_false_of_puncture_conclusion z a h
    H.counterexample C hz ha hthree hconclusion

/-- Every even vertex in an ordinary even-subgraph component has E-degree
different from three in a bare minimal counterexample. -/
theorem bare_ordinary_no_degree_three
    (z a : evenVertices G) (h : V)
    (H : BareMinimalCounterexample G h (z : V))
    (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (ha : a ∈ C.supp) : eDegree G (a : V) ≠ 3 :=
  fun hthree => bare_ordinary_degree_three_false z a h H C hz ha hthree

end Gallai.TwoException
