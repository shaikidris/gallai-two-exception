/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyAuxiliaryBudget
public import Gallai.TwoException.OrdinaryRetainedPositivity

@[expose] public section

/-! # Early spoke payment followed by ordinary-mate restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance (u x q : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restoring the unpaid spoke recovers exactly the mate-prepared star.
The leaf avoidance guard prevents any later mate deletion from removing it. -/
theorem early_spoke_restored_graph
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hxu : x ≠ u) (hqu : q ≠ u) (hxq : G.Adj x q)
    (havoid : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2) :
    ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M ⊔
        SimpleGraph.edge q x = ordinaryMatePuncture (starPuncture G u B) M := by
  have hs : (starPuncture G u B).Adj x q :=
    ⟨hxq, fun ht => hqu ((star_sup_adj_off_center u B x q hxu).mp ht).2⟩
  rw [SimpleGraph.edge_comm q x, ← ordinaryMatePuncture_sup_edge M x q havoid,
    delete_edge_sup_edge (starPuncture G u B) x q hs]

/-- Early spoke payment supplies positive contact leaves; restoring the
ordinary prefix preserves them and prepares recipient surplus. The exact
endpoint transfer outside that prefix is retained for the protected vertex. -/
theorem restore_early_spoke_and_ordinary_prefix
    (u x q : V) (B : Finset V) (O N : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hxB : x ∉ B) (hxu : x ≠ u) (hqu : q ≠ u) (hxq : G.Adj x q)
    (hdis : (O ++ N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O ++ N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O ++ N, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hxAvoid : ∀ e ∈ O ++ N, x ≠ e.1 ∧ x ≠ e.2)
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B) :
    let J := ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) (O ++ N)
    ∀ D : Decomposition J, Odd (J.degree x) → eDegree J q = 0 →
      ∃ E : Decomposition (ordinaryMatePuncture (starPuncture G u B) N),
        E.size = D.size ∧ (∀ t ∈ B, 0 < E.endpointCount t) ∧
        (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
        ∀ t, (∀ e ∈ O, t ≠ e.1 ∧ t ≠ e.2) →
          E.endpointCount t + (if x = t then 1 else 0) =
            D.endpointCount t + if q = t then 1 else 0 := by
  classical
  dsimp only
  intro D hxOdd hzero
  have hgraph := early_spoke_restored_graph u x q B (O ++ N) hxu hqu hxq hxAvoid
  have hspoke := restore_early_double_spoke u x q B (O ++ N) hadj hleaves hxB
    hxq.ne.symm (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
    D hxOdd hzero
  rw [hgraph] at hspoke
  obtain ⟨D1, hs1, hleaves1, hv1⟩ := hspoke
  have hu1 := ordinary_star_mates_centre_reserve u B (O ++ N) hadj huOdd hEvenB
    (fun e he => ⟨(havoid e he).1,(havoid e he).2.1⟩) D1
  obtain ⟨E, hs, _, hrec, hkeep⟩ := restore_ordinary_mate_prefix
    u B hadj hleaves O N hdis havoid hedges hpacket D1 hu1
  refine ⟨E, hs.trans hs1, ?_, hrec, ?_⟩
  · intro t ht
    rw [hkeep t (fun e he => ?_)]
    · exact hleaves1 t ht
    · have hav := havoid e (List.mem_append_left N he)
      exact ⟨fun heq => hav.2.2.1 (heq ▸ ht),
        fun heq => hav.2.2.2 (heq ▸ ht)⟩
  · intro t ht
    rw [hkeep t ht]
    exact hv1 t

/-- Once the early ordinary prefix is paid, all retained even contacts
are either protected or restored recipients. This supplies Fan's full
neighbourhood positivity on the actual star puncture, including original
odd neighbours which were not part of the contact packet. -/
theorem early_prefix_full_neighbourhood_positive
    (u h : V) (B : Finset V) (O : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ t = h ∨ ∃ e ∈ O, t = e.1)
    (E : Decomposition (starPuncture G u B))
    (hh : 0 < E.endpointCount h)
    (hrec : ∀ e ∈ O, 2 ≤ E.endpointCount e.1) :
    ∀ t, (starPuncture G u B).Adj u t ∨ t ∈ B →
      0 < E.endpointCount t := by
  classical
  intro t ht
  by_cases htB : t ∈ B
  · apply E.endpointCount_pos_of_odd_degree
    have hd := starPuncture_degree_leaf (G := G) u B t htB (hadj t htB)
    have he := hleaves t htB
    simp only [← SimpleGraph.ncard_neighborSet] at hd he ⊢
    rw [Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega
  · have hat : G.Adj u t := (ht.resolve_right htB).1
    by_cases he : Even (G.degree t)
    · rcases hcover t hat he with hb | rfl | ⟨e,heO,rfl⟩
      · exact False.elim (htB hb)
      · exact hh
      · exact lt_of_lt_of_le (by decide : 0 < 2) (hrec e heO)
    · apply E.endpointCount_pos_of_odd_degree
      have htu : t ≠ u := fun heq => G.irrefl (heq ▸ hat)
      have hd := starPuncture_degree_other (G := G) u B t htu htB
      have ho : Odd (G.degree t) := Nat.not_even_iff_odd.mp he
      simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
      rwa [hd]

noncomputable local instance : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Component packet coverage implies the contact classification required
by early restoration. The deleted contact set may include all windmill
privates, rather than only an exceptional hub and ordinary leaves. -/
theorem early_ordinary_packet_contact_coverage
    (u h : V) (B : Finset V) (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hselected : ∀ C ∈ F, ∀ t ∈ P C, (t : V) ∈ B)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hdonor : ∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t ∈ B ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ t = h ∨ ∃ e ∈
        (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))), t = e.1 := by
  classical
  intro t hat ht
  rcases hclass t hat ht with hb | hh | hs
  · exact Or.inl hb
  · exact Or.inr (Or.inl hh)
  · let a : evenVertices G := ⟨t,ht⟩
    let C := (evenSubgraph G).connectedComponentMk a
    have hC : C ∈ F := htouched a hs
    have ha : a ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨hs,
        (SimpleGraph.ConnectedComponent.mem_supp_iff C a).mpr rfl⟩
    rcases hcover C hC a ha with hp | ⟨e,he,heq⟩
    · exact Or.inl (hselected C hC a hp)
    · rcases heq with heq | heq
      · refine Or.inr (Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩)
        · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
            ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
        · exact congrArg Subtype.val heq
      · exact False.elim (hdonor C hC e he (heq ▸ hs))

end Gallai.TwoException
