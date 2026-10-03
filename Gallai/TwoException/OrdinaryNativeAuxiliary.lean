/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeSpokeFamily
public import Gallai.TwoException.OrdinaryAuxiliaryEndpoint

@[expose] public section

/-! # Native ordinary preparation with a protected auxiliary decomposition -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeAuxiliaryEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance nativeAuxiliaryAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Original hub-only contact data produce an actual preparation and its
protected endpoint decomposition, without supplying a preparation family. -/
theorem bare_ordinary_native_auxiliary
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (hSh : ∀ t ∈ S, (t : V) ≠ h)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
    (∀ C ∈ F, (mates C).length ≤ 1 ∧
      (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P C ∧ e.2 ∉ P C) ∧
      (∀ e ∈ mates C, ∃ a : evenVertices G,
        C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
    ((F.biUnion P).image Subtype.val).card = F.card +
      2 * (F.filter (fun C => (ordinaryComponentPacket G S C).card = 3)).card +
      special.card ∧
    ((F.filter (fun C => (ordinaryComponentPacket G S C).card = 2) \ special).Nonempty →
      Even (1 + ((F.biUnion P).image Subtype.val).card)) ∧
    special.card ≤ (if Even (1 + ((F.biUnion P).image Subtype.val).card) then 1 else 0) ∧
    (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
    (∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
    (∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
    (∀ C ∈ F, C ∈ special →
      (ordinaryComponentPacket G S C).card = 2 ∧ P C = ordinaryComponentPacket G S C) ∧
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∃ D : Decomposition (ordinaryMatePuncture (starPuncture G u B) M),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  obtain ⟨special,P,mates,hs,_,hP,hcount,heven,hreserve,hm,hcover,hregular,hspec,hdonor⟩ :=
    bare_ordinary_native_spoke_family h x H S F hF hx 1
  have hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ a ∈ P C ∧ b ∈ P C ∧ mates C = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u := by
    intro C hC hCs
    have htwo := (Finset.mem_filter.mp (hs hCs)).2
    have hnon : (ordinaryComponentPacket G S C).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨a,ha⟩ := hnon
    have haS := (Finset.mem_filter.mp ha).1
    have haC := (Finset.mem_filter.mp ha).2
    obtain ⟨b,c,hsupp,hab,hbc,hca,hpacket,_,hcu⟩ :=
      bare_ordinary_special_preparation_classified h u x a H S C
        (hx C hC) haC haS htwo hclass
    obtain ⟨hPC,hMC⟩ := hspec C hCs
    refine ⟨a,b,c,hsupp,?_,?_,hMC,hca.symm,hbc,hcu⟩
    · rw [hPC,hpacket]; simp
    · rw [hPC,hpacket]; simp
  refine ⟨special,P,mates,hP,hm,hcount,heven,hreserve,hdonor,hcover,hregular,?_,?_⟩
  · intro C _ hCs
    exact ⟨(Finset.mem_filter.mp (hs hCs)).2,(hspec C hCs).1⟩
  exact bare_ordinary_auxiliary_endpoint h x H u hu hxu S hS hSh F special P mates
    hP (fun C hC => (hm C hC).1) (fun C hC => (hm C hC).2.1)
    hx htouched hcover hclass hregular hspecial

end Gallai.TwoException
