/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeAuxiliary
public import Gallai.TwoException.OrdinaryEvenRestoration
public import Gallai.TwoException.OrdinaryRetainedPositivity
public import Gallai.TwoException.OrdinaryOddStarRecipients

@[expose] public section

/-! # Native ordinary preparation with a protected auxiliary decomposition -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance nativeRestorationEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance nativeRestorationAdj (u : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture (starPuncture G u B) M).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable local instance nativeRestorationStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _

/-- A nonempty ordinary family restores its mates in either parity regime.
The resulting packet gain and centre count suffice for full-star restoration. -/
theorem bare_ordinary_native_mate_restoration
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (S : Finset (evenVertices G)) (hS : ∀ t ∈ S, G.Adj u t)
    (hSh : ∀ t ∈ S, (t : V) ≠ h)
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (hFnon : F.Nonempty) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
    (∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
    (∀ C ∈ F, C ∈ special →
      (ordinaryComponentPacket G S C).card = 2 ∧ P C = ordinaryComponentPacket G S C) ∧
    (∀ C ∈ F, ∀ e ∈ mates C, e.1 ∉ P C ∧ e.2 ∉ P C) ∧
    (∀ C ∈ F, ∀ e ∈ mates C, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P C) ∧
    let B := insert (x : V) ((F.biUnion P).image Subtype.val)
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∃ E : Decomposition (starPuncture G u B),
      E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
      (∀ e ∈ M, 2 ≤ E.endpointCount e.1) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
      (∀ t, (starPuncture G u B).Adj u t ∨ t ∈ B → 0 < E.endpointCount t) ∧
      special.card < F.card + E.endpointCount u ∧
      (0 < E.endpointCount u ∨ Odd B.card) := by
  classical
  obtain ⟨special,P,mates,hP,hm,_,heven,hreserve,hdonor,hcover,hregular,hspecial,D,hsize,hh⟩ :=
    bare_ordinary_native_auxiliary h x H u hu hxu S hS hSh F hF hx htouched hclass
  have hs : special.card ≤ 1 := by
    split_ifs at hreserve <;> omega
  let B := insert (x : V) ((F.biUnion P).image Subtype.val)
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hadj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hxu
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
      exact hS a (Finset.mem_filter.mp (hP C hC ha)).1
  have hxnot : (x : V) ∉ (F.biUnion P).image Subtype.val := by
    intro ht
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    have he' : a = x := Subtype.ext he
    obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
    exact hx C hC (he' ▸ (Finset.mem_filter.mp (hP C hC ha)).2)
  have hcentreEven : Even (1 + ((F.biUnion P).image Subtype.val).card) →
      0 < D.endpointCount u := by
    intro he
    have hB : Even B.card := by
      simpa only [B,Finset.card_insert_of_notMem hxnot,Nat.add_comm] using he
    apply ordinary_star_mates_centre_reserve u B M hadj hu hB
    intro e hem
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hem
    exact ⟨fun he => (Nat.not_even_iff_odd.mpr hu) (he ▸ f.1.property),
      fun he => (Nat.not_even_iff_odd.mpr hu) (he ▸ f.2.property)⟩
  have hchoice : 0 < D.endpointCount u ∨ ∀ e ∈ M, ¬ G.Adj e.1 u := by
    by_cases he : Even (1 + ((F.biUnion P).image Subtype.val).card)
    · exact Or.inl (hcentreEven he)
    · right
      have hk := Nat.not_even_iff_odd.mp he
      have hn := ordinary_odd_star_recipients_noncontact S F special P mates hP
        (fun C hC e hem => by
          obtain ⟨a,ha,hap,hab,hca⟩ := (hm C hC).2.2 e hem
          exact ⟨((hm C hC).2.1 e hem).2.2.2.1,a,ha,hap,hab,
            ((hm C hC).2.1 e hem).1,hca⟩)
        hdonor (fun C hC hCs => (hspecial C hC hCs).2) _ hk heven
      intro e hem
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hem
      obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
      have hCF := Finset.mem_toList.mp hC
      have hfdata := (hm C hCF).2.1 f hfC
      exact bare_ordinary_noncontact_recipient_nonadjacent h u x f.1 f.2 H S C
        (hx C hCF) hfdata.2.1 hfdata.1 (hn C hCF f hfC) hclass
  obtain ⟨E,hED,hEu,hrec,houtside⟩ := restore_assembled_ordinary_mates
    u hu x hxu S hS F P mates hP (fun C hC => (hm C hC).1)
    (fun C hC => (hm C hC).2.1)
    (fun C hC e he => by
      obtain ⟨a,ha,hap,_,_⟩ := (hm C hC).2.2 e he
      exact ⟨a,ha,hap⟩) hx D hchoice
  have hav : ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      h ≠ e.1 ∧ h ≠ e.2 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hedge := ((hm C (Finset.mem_toList.mp hC)).2.1 f hfC).1
    rcases H.counterexample.1 with ⟨_,_,_,_,_,hz,_⟩
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hz
    constructor
    · intro heq
      have ha : G.Adj h f.2 := by simpa only [heq] using hedge
      have hmem := (mem_evenNeighbors (G := G) h f.2).mpr ⟨ha,f.2.property⟩
      rw [hempty] at hmem
      simpa using hmem
    · intro heq
      have ha : G.Adj h f.1 := by simpa only [heq] using hedge.symm
      have hmem := (mem_evenNeighbors (G := G) h f.1).mpr ⟨ha,f.1.property⟩
      rw [hempty] at hmem
      simpa using hmem
  have hhE : 2 ≤ E.endpointCount h := by
    rw [houtside h hav]; exact hh
  have hFpos := Finset.card_pos.mpr hFnon
  have hstrict : special.card < F.card + E.endpointCount u := by
    by_cases he : Even (1 + ((F.biUnion P).image Subtype.val).card)
    · have hp := hcentreEven he
      rw [hEu]
      omega
    · simp only [he,ite_false] at hreserve
      omega
  have hround : 0 < E.endpointCount u ∨ Odd B.card := by
    by_cases he : Even (1 + ((F.biUnion P).image Subtype.val).card)
    · left; rw [hEu]; exact hcentreEven he
    · right
      have ho := Nat.not_even_iff_odd.mp he
      simpa only [B,Finset.card_insert_of_notMem hxnot,Nat.add_comm] using ho
  refine ⟨special,P,mates,hP,hregular,hspecial,?_,?_,E,?_,hhE,hrec,hdonor,?_,hstrict,hround⟩
  · intro C hC e he
    exact ⟨((hm C hC).2.1 e he).2.2.2.1,((hm C hC).2.1 e he).2.2.2.2⟩
  · intro C hC e he
    obtain ⟨a,ha,hap,_,_⟩ := (hm C hC).2.2 e he
    exact ⟨a,ha,hap⟩
  · rw [hED]; exact hsize
  · apply ordinary_assembled_restored_full_neighbourhood_positive u h x S F P mates
      htouched hcover hdonor hclass
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hxu
      · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
        exact hS a (Finset.mem_filter.mp (hP C hC ha)).1
    · omega
    · intro e he
      have hr := hrec e he
      omega

end Gallai.TwoException
