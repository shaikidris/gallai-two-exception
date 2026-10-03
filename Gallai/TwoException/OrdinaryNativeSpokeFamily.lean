/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinarySpecialExistence
public import Gallai.TwoException.OrdinarySpokeAssembly
public import Gallai.TwoException.OrdinaryMateOrientation

@[expose] public section

/-! # Graph-native parity-selected ordinary spoke family -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeSpokeFamilyComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Actual ordinary contacts admit a parity-selected spoke family with
at most one special T2. No regular/special preparation family or total
deletion count is assumed. The hub contribution is counted separately. -/
theorem bare_ordinary_native_spoke_family
    (h : V) (z : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hz : ∀ C ∈ F, z ∉ C.supp) (hub : ℕ) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      special ⊆ F.filter (fun C => #(ordinaryComponentPacket G S C) = 2) ∧
      #special ≤ 1 ∧
      (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) + #special ∧
      ((F.filter (fun C => #(ordinaryComponentPacket G S C) = 2) \ special).Nonempty →
        Even (hub + #((F.biUnion P).image Subtype.val))) ∧
      #special ≤ (if Even (hub + #((F.biUnion P).image Subtype.val)) then 1 else 0) ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ F, C ∉ special → ∀ t, t ∈ C.supp →
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ special, P C = ordinaryComponentPacket G S C ∧ mates C = []) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) := by
  classical
  obtain ⟨regular,M,hdata⟩ := bare_ordinary_regular_preparation_family h z H S F hF hz
  have horiented (C) (hC : C ∈ F) :=
    ordinary_regular_preparation_oriented S (regular C) C (M C)
      (hdata C hC).2.1 (hdata C hC).2.2.2.2.2.2.1
      (hdata C hC).2.2.1 (hdata C hC).2.2.2.1
      (hdata C hC).2.2.2.2.2.2.2
  let T3 := F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)
  let eligible := F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)
  have hT3 : T3 ⊆ F := Finset.filter_subset _ _
  have heligible : eligible ⊆ F := Finset.filter_subset _ _
  have hnot : ∀ C ∈ eligible, C ∉ T3 := by
    intro C hC hCt
    have htwo := (Finset.mem_filter.mp hC).2
    have hthree := (Finset.mem_filter.mp hCt).2
    omega
  have hregSupport : ∀ C ∈ F, ∀ t ∈ regular C, t ∈ C.supp := by
    intro C hC t ht
    obtain ⟨_,hsub,_,_,_,_,_,_⟩ := hdata C hC
    exact (Finset.mem_filter.mp (hsub ht)).2
  have hspecSupport : ∀ C ∈ eligible, ∀ t ∈ ordinaryComponentPacket G S C, t ∈ C.supp :=
    fun _ _ _ ht => (Finset.mem_filter.mp ht).2
  have hregCard : ∀ C ∈ F, #(regular C) = 1 + 2 * (if C ∈ T3 then 1 else 0) := by
    intro C hC
    obtain ⟨_,_,_,_,_,_,hc,_⟩ := hdata C hC
    simpa [T3,hC] using hc
  have hspecCard : ∀ C ∈ eligible, #(ordinaryComponentPacket G S C) = 2 :=
    fun _ hC => (Finset.mem_filter.mp hC).2
  obtain ⟨special,hs,hsize,hcount,heven,hreserve⟩ :=
    ordinary_parity_spoke_assembly G F T3 eligible hub regular
      (ordinaryComponentPacket G S) hT3 heligible hnot hregSupport hspecSupport hregCard hspecCard
  let P := fun C => if C ∈ special then ordinaryComponentPacket G S C else regular C
  let mates := fun C => if C ∈ special then [] else (M C).map (orientOrdinaryMate S)
  refine ⟨special,P,mates,hs,hsize,?_,hcount,heven,hreserve,?_,?_,?_,?_,?_⟩
  · intro C hC
    by_cases hCs : C ∈ special
    · simp [P,hCs]
    · obtain ⟨_,hsub,_,_,_,_,_,_⟩ := hdata C hC
      simpa [P,hCs] using hsub
  · intro C hC
    by_cases hCs : C ∈ special
    · simp [mates,hCs]
    · obtain ⟨hln,_,hm⟩ := horiented C hC
      simp only [mates,P,ite_eq_right hCs]
      refine ⟨hln.trans_le (hdata C hC).2.2.2.2.1,?_,?_⟩
      · intro e he
        obtain ⟨ha,hb,hc,hd,he',_,_⟩ := hm e he
        exact ⟨ha,hb,hc,hd,he'⟩
      · intro e he
        exact (hm e he).2.2.2.2.2.2
  · intro C hC t ht
    by_cases hCs : C ∈ special
    · exact Or.inl (by simpa [P,hCs] using ht)
    · simpa only [mates,P,ite_eq_right hCs] using
        (horiented C hC).2.1 t (Finset.mem_filter.mp ht).2
  · intro C hC hCs t ht
    simpa only [mates,P,ite_eq_right hCs] using (horiented C hC).2.1 t ht
  · intro C hCs
    simp [P,mates,hCs]
  · intro C hC e he
    by_cases hCs : C ∈ special
    · simp [mates,hCs] at he
    · have he' : e ∈ (M C).map (orientOrdinaryMate S) := by
        simpa only [mates,ite_eq_right hCs] using he
      exact ((horiented C hC).2.2 e he').2.2.2.2.2.1

/-- When the private offset and ordinary component count have even sum,
native preparation needs no special packet. This includes odd component
count with offset one, and even component count with one spare private leaf. -/
theorem bare_ordinary_native_even_preparation
    (h : V) (z : evenVertices G) (H : BareMinimalCounterexample G h (z : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hz : ∀ C ∈ F, z ∉ C.supp) (offset : ℕ) (heven : Even (offset + #F)) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) ∧
      Even (offset + #((F.biUnion P).image Subtype.val)) ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, ∀ t ∈ C.supp,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) := by
  classical
  obtain ⟨special,P,mates,_,hsize,hP,hcount,_,hreserve,hdata,_,hcover,_,hdonor⟩ :=
    bare_ordinary_native_spoke_family h z H S F hF hz offset
  have hs0 : #special = 0 := by
    by_cases hk : Even (offset + #((F.biUnion P).image Subtype.val))
    · rw [Nat.even_iff] at heven hk
      omega
    · simp only [hk,ite_false] at hreserve
      omega
  have hsEmpty : special = ∅ := Finset.card_eq_zero.mp hs0
  have hc : #((F.biUnion P).image Subtype.val) = #F +
      2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) := by
    simpa only [hs0,Nat.add_zero] using hcount
  refine ⟨P,mates,hP,hc,?_,hdata,?_,hdonor⟩
  · rw [Nat.even_iff] at heven ⊢
    omega
  · intro C hC t ht
    exact hcover C hC (by simp [hsEmpty]) t ht

end Gallai.TwoException
