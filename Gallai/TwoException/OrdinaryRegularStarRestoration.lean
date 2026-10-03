/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryAssembledHalfStarGain
public import Gallai.TwoException.OrdinaryPendingBound
public import Gallai.TwoException.PacketGainStarRestoration

@[expose] public section

/-! # Restoring a regular ordinary star without a distinguished hub spoke -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance regularComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance regularAdj (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- The literal ordinary packets underlying a selected spoke set and mate
list. Keeping these witnesses permits budget and reconstruction to use one
preparation; donor nonadjacency protects the retained centre neighbours. -/
structure OrdinaryRegularPacketData (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : V) (x : evenVertices G) (v : V) (B : Finset V) (O : List (V × V)) where
  contacts : Finset (evenVertices G)
  components : Finset (evenSubgraph G).ConnectedComponent
  packets : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G)
  mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G)
  component_contact : components ⊆ contacts.image (evenSubgraph G).connectedComponentMk
  exception_absent : ∀ Z ∈ components, x ∉ Z.supp
  packet_subset : ∀ Z ∈ components, packets Z ⊆ ordinaryComponentPacket G contacts Z
  contacts_avoid_h : ∀ t ∈ contacts, (t : V) ≠ h
  spoke_eq : B = (components.biUnion packets).image Subtype.val
  mate_eq : O = (components.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  cover : ∀ Z ∈ components, ∀ t ∈ Z.supp,
    t ∈ packets Z ∨ ∃ e ∈ mates Z, t = e.1 ∨ t = e.2
  mate_avoid : ∀ Z ∈ components, ∀ e ∈ mates Z,
    e.1 ∉ packets Z ∧ e.2 ∉ packets Z
  mate_labels : ∀ Z ∈ components, ∀ e ∈ mates Z, ∃ a : evenVertices G,
    Z.supp = {a,e.1,e.2} ∧ a ∈ packets Z
  donor_avoid : ∀ e ∈ O, ¬ G.Adj v e.2

/-- A positive centre and regular packet gains close the entire ordinary
star. Unlike the hub-contact consumer, no exceptional spoke is inserted.
The empty packet family is handled without a positivity-of-cardinality
assumption. -/
theorem bare_ordinary_regular_star_restore
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (v : V) (B : Finset V) (O : List (V × V))
    (R : OrdinaryRegularPacketData G h x v B O)
    (hadj : ∀ t ∈ B, G.Adj v t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (D : Decomposition (starPuncture G v B)) (hDv : 0 < D.endpointCount v)
    (hrec : ∀ e ∈ O, 2 ≤ D.endpointCount e.1)
    (hpositive : ∀ t, (starPuncture G v B).Adj v t ∨ t ∈ B →
      0 < D.endpointCount t) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ t, t ≠ v → t ∉ B → E.endpointCount t = D.endpointCount t := by
  classical
  by_cases hB : B = ∅
  · subst B
    have hgraph : starPuncture G v ∅ = G := by
      ext a b
      simp [starPuncture]
    let n := D.size
    let f := D.endpointCount
    have hout : ∃ E : Decomposition (starPuncture G v ∅), E.size = n ∧
        ∀ t, t ≠ v → t ∉ (∅ : Finset V) → E.endpointCount t = f t :=
        ⟨D,rfl,fun _ _ _ => rfl⟩
    rwa [hgraph] at hout
  have hvB : v ∉ B := fun ht => G.irrefl (hadj v ht)
  have hmissing : ∀ t ∈ B, ¬ (starPuncture G v B).Adj v t :=
    fun t ht => starPuncture_missing G v B hvB t ht
  obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  obtain ⟨A,hAB,_,hhalf,Q,hQD,hvec⟩ :=
    D.prescribed_half_star_addibility v B hvB hmissing hpositive b hb
  have hvA : v ∉ A := fun ht => hvB (hAB ht)
  have hQv : Q.endpointCount v = D.endpointCount v + #A := by
    simpa only [hvA,if_false,if_true,Nat.add_zero] using hvec v
  have hpart := Finset.card_sdiff_add_card_eq_card hAB
  have hreserve : #(B \ A) + 1 ≤ Q.endpointCount v := by omega
  have hpassing : ∀ t ∈ B \ A, passingNeighborCount Q t ≤ 2 := by
    intro t ht
    have htB := Finset.mem_sdiff.mp ht |>.1
    rw [R.spoke_eq] at htB
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp htB
    obtain ⟨Z,hZ,hwZ⟩ := Finset.mem_biUnion.mp hw
    have hwt := Finset.mem_filter.mp (R.packet_subset Z hZ hwZ)
    have hc := bare_ordinary_half_star_pending_le_two h x w H Z
      (R.exception_absent Z hZ) hwt.2 (R.contacts_avoid_h w hwt.1)
      v B A hAB hadj hleaves ht Q
    convert hc using 1
    unfold passingNeighborCount
    congr 1
    ext z
    simp
  have hmissQ : ∀ t ∈ B \ A, ¬ (starPuncture G v B ⊔ A.sup (SimpleGraph.edge v)).Adj v t := by
    intro t ht ha
    rcases ha with ha | ha
    · exact hmissing t (Finset.mem_sdiff.mp ht).1 ha
    · exact (Finset.mem_sdiff.mp ht).2 ((star_sup_adj_center v A hvA t).mp ha)
  have hrestore : ∃ E : Decomposition ((starPuncture G v B ⊔ A.sup (SimpleGraph.edge v)) ⊔
      (B \ A).sup (SimpleGraph.edge v)), E.size = Q.size ∧
      ∀ t, E.endpointCount t + (if v = t then #(B \ A) else 0) =
        Q.endpointCount t + if t ∈ B \ A then 1 else 0 := by
    by_contra hf
    obtain ⟨he,htight⟩ := star_surplus_failure_profile Q v (B \ A)
      (fun ht => hvB (Finset.mem_sdiff.mp ht).1) hmissQ hpassing hreserve hf
    have hPB : ∀ Z ∈ R.components, (R.packets Z).image Subtype.val ⊆ B := by
      intro Z hZ t ht
      rw [R.spoke_eq]
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨w,Finset.mem_biUnion.mpr ⟨Z,hZ,hw⟩,rfl⟩
    have hg := bare_ordinary_assembled_half_star_gain h x H v B A hAB hadj hleaves
      R.contacts R.components ∅ R.packets R.mates R.component_contact R.exception_absent
      R.packet_subset hPB (fun Z hZ _ => R.cover Z hZ) R.mate_avoid R.mate_labels
      (by simp) D (by simpa only [← R.mate_eq] using hrec) Q hvec
      (by
        intro w hw
        have hc := htight w hw
        convert hc using 1
        unfold passingNeighborCount
        congr 1
        ext z
        simp)
    simp only [Finset.card_empty,Nat.add_zero,← R.spoke_eq] at hg
    have hFpos : 0 < #R.components := by
      apply Finset.card_pos.mpr
      rw [R.spoke_eq] at hb
      obtain ⟨w,hw,_⟩ := Finset.mem_image.mp hb
      obtain ⟨Z,hZ,_⟩ := Finset.mem_biUnion.mp hw
      exact ⟨Z,hZ⟩
    have hAc : #(B ∩ A) = #A := by rw [Finset.inter_eq_right.mpr hAB]
    rw [hAc] at hg
    omega
  obtain ⟨E,hEQ,hend⟩ := hrestore
  have hgraph : (starPuncture G v B ⊔ A.sup (SimpleGraph.edge v)) ⊔
      (B \ A).sup (SimpleGraph.edge v) = G := by
    rw [sup_assoc,← Finset.sup_union,Finset.union_sdiff_of_subset hAB,
      ordinary_half_star_graph v B B (by rfl) hadj,Finset.sdiff_self]
    simp [starPuncture]
  have hout : ∃ E : Decomposition ((starPuncture G v B ⊔ A.sup (SimpleGraph.edge v)) ⊔
      (B \ A).sup (SimpleGraph.edge v)), E.size = D.size ∧
      ∀ t, t ≠ v → t ∉ B → E.endpointCount t = D.endpointCount t := by
    refine ⟨E,hEQ.trans hQD,?_⟩
    intro t htv htB
    have htA : t ∉ A := fun ht => htB (hAB ht)
    have htR : t ∉ B \ A := fun ht => htB (Finset.mem_sdiff.mp ht).1
    have hv := hvec t
    have he := hend t
    simp only [htA,htR,htv.symm,if_false,Nat.add_zero] at hv he
    exact he.trans hv
  rwa [hgraph] at hout

end Gallai.TwoException
