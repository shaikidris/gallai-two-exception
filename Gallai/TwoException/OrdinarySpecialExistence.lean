/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationFamily

@[expose] public section

/-! # Special T2 labels extracted from actual contact packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A size-two packet in the bare kernel is a whole triangle with exactly
two contact vertices. This labels the special deletion and its retained
noncontact witness directly from minimality. -/
theorem bare_ordinary_two_contact_labels
    (h : V) (z w : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (hsize : #(ordinaryComponentPacket G S C) = 2) :
    ∃ b c : evenVertices G, C.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      ordinaryComponentPacket G S C = {w,b} := by
  classical
  obtain ⟨_,hpacket⟩ | ⟨b,c,hs,hwb,hbc,hcw,hshape⟩ :=
    bare_ordinary_contact_shapes h z w H S C hz hwC hwS
  · simp [hpacket] at hsize
  · have hwbN : w ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hwb)
    have hwcN : w ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hcw.symm)
    have hbcN : b ≠ c := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc)
    rcases hshape with hsingle | hpair | hpair | hfull
    · simp [hsingle] at hsize
    · exact ⟨b,c,hs,hwb,hbc,hcw,hpair⟩
    · refine ⟨c,b,?_,hcw.symm,hbc.symm,hwb.symm,hpair⟩
      rw [hs]
      ext t
      simp [or_comm, or_left_comm, or_assoc]
    · simp [hfull,hwbN,hwcN,hbcN] at hsize

/-- The special packet's retained third vertex avoids the centre. The
complete original contact set supplies the needed locality guard. -/
theorem bare_ordinary_special_preparation_exists
    (h u : V) (z w : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (hsize : #(ordinaryComponentPacket G S C) = 2)
    (hcontacts : ∀ t : evenVertices G, G.Adj u t → t ∈ S) :
    ∃ b c : evenVertices G, C.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      ordinaryComponentPacket G S C = {w,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
  obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket⟩ :=
    bare_ordinary_two_contact_labels h z w H S C hz hwC hwS hsize
  obtain ⟨_,hc,hcu,_⟩ := ordinary_triangle_special_preparation u S C w b c
    hs hwb hbc hcw hpacket hcontacts
  exact ⟨b,c,hs,hwb,hbc,hcw,hpacket,hc,hcu⟩

/-- Component-local contact coverage suffices for the special triangle.
Contacts with the exceptional hub outside this component need not belong to S. -/
theorem bare_ordinary_special_preparation_local
    (h u : V) (z w : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (hsize : #(ordinaryComponentPacket G S C) = 2)
    (hcontacts : ∀ t : evenVertices G, t ∈ C.supp → G.Adj u t → t ∈ S) :
    ∃ b c : evenVertices G, C.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      ordinaryComponentPacket G S C = {w,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
  classical
  obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket⟩ :=
    bare_ordinary_two_contact_labels h z w H S C hz hwC hwS hsize
  have hcwN : c ≠ w := fun he => G.irrefl (congrArg Subtype.val he ▸ hcw)
  have hcbN : c ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc.symm)
  have hcS : c ∉ S := by
    intro hc
    have hp : c ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨hc, by simp [hs]⟩
    rw [hpacket] at hp
    simpa [hcwN,hcbN] using hp
  exact ⟨b,c,hs,hwb,hbc,hcw,hpacket,hcS,
    fun hcu => hcS (hcontacts c (by simp [hs]) hcu.symm)⟩

/-- Hub/contact classification supplies the retained special vertex guard.
The exceptional hub lies outside C and the protected isolate cannot be a
vertex of its triangle. -/
theorem bare_ordinary_special_preparation_classified
    (h u : V) (z w : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hz : z ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (hsize : #(ordinaryComponentPacket G S C) = 2)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (z : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    ∃ b c : evenVertices G, C.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      ordinaryComponentPacket G S C = {w,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
  classical
  obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket⟩ :=
    bare_ordinary_two_contact_labels h z w H S C hz hwC hwS hsize
  have hcwN : c ≠ w := fun he => G.irrefl (congrArg Subtype.val he ▸ hcw)
  have hcbN : c ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc.symm)
  have hcS : c ∉ S := by
    intro hc
    have hp : c ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨hc, by simp [hs]⟩
    rw [hpacket] at hp
    simpa [hcwN,hcbN] using hp
  refine ⟨b,c,hs,hwb,hbc,hcw,hpacket,hcS,?_⟩
  intro hcu
  rcases hclass c hcu.symm c.property with hcz | hch | hc
  · have he : c = z := Subtype.ext hcz
    exact hz (he ▸ (show c ∈ C.supp by simp [hs]))
  · rcases H.counterexample.1 with ⟨_,_,_,_,_,hhzero,_⟩
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
    have hm := (mem_evenNeighbors (G := G) h w).mpr
      ⟨by simpa only [hch] using hcw,w.property⟩
    rw [hempty] at hm
    simpa using hm
  · exact hcS hc

/-- The actual contact set outside the hub component supplies the special
triangle's noncontact witness even when the centre also contacts hub
privates. No hub-only contact classification is required. -/
theorem bare_ordinary_special_preparation_outside_hub
    (h u : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C D : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (hxD : x ∉ D.supp) (hwD : w ∈ D.supp)
    (hwS : w ∈ Finset.univ.filter
      (fun a : evenVertices G => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h))
    (hsize : #(ordinaryComponentPacket G (Finset.univ.filter
      (fun a : evenVertices G => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) = 2) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    ∃ b c : evenVertices G, D.supp = {w,b,c} ∧
      G.Adj w b ∧ G.Adj b c ∧ G.Adj c w ∧
      ordinaryComponentPacket G S D = {w,b} ∧ c ∉ S ∧ ¬ G.Adj c u := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  obtain ⟨b,c,hs,hwb,hbc,hcw,hpacket⟩ :=
    bare_ordinary_two_contact_labels h x w H S D hxD hwD hwS hsize
  have hcD : c ∈ D.supp := by rw [hs]; simp
  have hcC : c ∉ C.supp := by
    intro hc
    have he := SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hcD
    exact hxD (he ▸ hxC)
  have hch : (c : V) ≠ h := by
    intro he
    have hbare := H.counterexample.1.2.2.2.2.2.1
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hbare
    have hm := (mem_evenNeighbors (G := G) h w).mpr
      ⟨by simpa only [he] using hcw,w.property⟩
    rw [hempty] at hm
    simpa using hm
  have hcS : c ∉ S := by
    intro hc
    have hp : c ∈ ordinaryComponentPacket G S D := Finset.mem_filter.mpr ⟨hc,hcD⟩
    rw [hpacket] at hp
    have hcwN : c ≠ w := fun he => G.irrefl (congrArg Subtype.val he ▸ hcw)
    have hcbN : c ≠ b := fun he => G.irrefl (congrArg Subtype.val he ▸ hbc.symm)
    simpa [hcwN,hcbN] using hp
  exact ⟨b,c,hs,hwb,hbc,hcw,hpacket,hcS,fun hcu =>
    hcS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcu.symm,hcC,hch⟩)⟩

/-- Label the very special packets selected for delayed payment. The two
deleted contacts and retained noncontact witness belong to the same
original ordinary component, and the selected mate list there is empty. -/
theorem bare_delayed_special_family_labels
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (hx : ∀ D ∈ F, x ∉ D.supp)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hs : special ⊆ F.filter (fun D => #(ordinaryComponentPacket G
      (Finset.univ.filter (fun a : evenVertices G =>
        G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) = 2))
    (hspec : ∀ D ∈ special, P D = ordinaryComponentPacket G
      (Finset.univ.filter (fun a : evenVertices G =>
        G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D ∧ mates D = []) :
    ∀ D ∈ special, ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ a ∈ P D ∧ b ∈ P D ∧ mates D = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u := by
  classical
  intro D hD
  obtain ⟨hDF,htwo⟩ := Finset.mem_filter.mp (hs hD)
  have hnon := Finset.card_pos.mp (show 0 < #(ordinaryComponentPacket G
    (Finset.univ.filter (fun a : evenVertices G =>
      G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) by omega)
  obtain ⟨a,ha⟩ := hnon
  obtain ⟨haS,haD⟩ := Finset.mem_filter.mp ha
  obtain ⟨b,c,hsupp,_,hbc,hca,hpacket,_,hcu⟩ :=
    bare_ordinary_special_preparation_outside_hub h u x a H C D hxC
      (hx D hDF) haD haS htwo
  obtain ⟨hP,hM⟩ := hspec D hD
  refine ⟨a,b,c,hsupp,?_,?_,hM,hca.symm,hbc,hcu⟩
  · rw [hP,hpacket]; simp
  · rw [hP,hpacket]; simp

/-- The selected special packets have the exact two-leaf interface needed
by prepared-star restoration, including the edge between those leaves. -/
theorem bare_delayed_special_family_star_shape
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (hx : ∀ D ∈ F, x ∉ D.supp)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hs : special ⊆ F.filter (fun D => #(ordinaryComponentPacket G
      (Finset.univ.filter (fun a : evenVertices G =>
        G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) = 2))
    (hspec : ∀ D ∈ special, P D = ordinaryComponentPacket G
      (Finset.univ.filter (fun a : evenVertices G =>
        G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) :
    ∀ D ∈ special, ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ G.Adj a b ∧
      (P D).image Subtype.val = {a.val,b.val} := by
  classical
  intro D hD
  obtain ⟨hDF,htwo⟩ := Finset.mem_filter.mp (hs hD)
  have hnon := Finset.card_pos.mp (show 0 < #(ordinaryComponentPacket G
    (Finset.univ.filter (fun a : evenVertices G =>
      G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) by omega)
  obtain ⟨a,ha⟩ := hnon
  obtain ⟨haS,haD⟩ := Finset.mem_filter.mp ha
  obtain ⟨b,c,hsupp,hab,_,_,hpacket,_,_⟩ :=
    bare_ordinary_special_preparation_outside_hub h u x a H C D hxC
      (hx D hDF) haD haS htwo
  refine ⟨a,b,c,hsupp,hab,?_⟩
  rw [hspec D hD,hpacket]
  simp

end Gallai.TwoException
