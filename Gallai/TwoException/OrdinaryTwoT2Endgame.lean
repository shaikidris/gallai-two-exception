/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeRestoration
public import Gallai.TwoException.OrdinaryPreparedStarRestoration

@[expose] public section

/-! # The native two-T2 ordinary contact endgame -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance twoT2ComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A nonempty ordinary contact family cannot occur in the hub-only
endgame of a bare minimum counterexample. All preparations and
decompositions are constructed from the original graph. -/
theorem bare_ordinary_hub_contact_family_false
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
    False := by
  classical
  obtain ⟨special,P,mates,hP,hcover,hspecial,havoid,hlabels,
    D,hsize,hh,hrec,_,hpositive,hstrict,hDu⟩ :=
    bare_ordinary_native_mate_restoration h x H u hu hxu S hS hSh F hF hx htouched hclass hFnon
  have hadj : ∀ t ∈ insert (x : V) ((F.biUnion P).image Subtype.val), G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hxu
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
      exact hS a (Finset.mem_filter.mp (hP C hC ha)).1
  obtain ⟨E,hED,hend⟩ := bare_ordinary_prepared_star_restore h x H u S F special P mates
    hF hx hP hSh hadj hcover havoid hlabels hspecial D hstrict hrec hpositive hDu
  have hhu : h ≠ u := by
    intro he
    have hhEven := H.counterexample.1.2.2.2.1
    rw [he] at hhEven
    exact (Nat.not_even_iff_odd.mpr hu) hhEven
  have hhB : h ∉ insert (x : V) ((F.biUnion P).image Subtype.val) := by
    intro ht
    rcases Finset.mem_insert.mp ht with he | ht
    · exact H.counterexample.1.2.1 he
    · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,ha⟩ := Finset.mem_biUnion.mp ha
      exact hSh a (Finset.mem_filter.mp (hP C hC ha)).1 he
  apply H.counterexample.2
  refine ⟨E,?_,?_⟩
  · rw [hED]; exact hsize
  · rw [hend h hhu hhB]; exact hh

/-- Canonical only-hub dispatch: choose all even contacts other than x,h
and their actual components. No contact family or preparation is supplied. -/
theorem bare_hub_contact_reducible
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (hu : Odd (G.degree u)) (hxu : G.Adj u x)
    (honly : ∀ w : evenVertices G, G.Adj u w → (w : V) ≠ h → (w : V) ≠ (x : V) →
      x ∉ ((evenSubgraph G).connectedComponentMk w).supp)
    (hordinary : ∃ w : evenVertices G, G.Adj u w ∧ (w : V) ≠ h ∧ (w : V) ≠ (x : V)) :
    False := by
  classical
  let S := Finset.univ.filter (fun w : evenVertices G =>
    G.Adj u w ∧ (w : V) ≠ h ∧ (w : V) ≠ (x : V))
  let F := S.image (evenSubgraph G).connectedComponentMk
  have hS : ∀ w ∈ S, G.Adj u w := fun w hw => (Finset.mem_filter.mp hw).2.1
  have hSh : ∀ w ∈ S, (w : V) ≠ h := fun w hw => (Finset.mem_filter.mp hw).2.2.1
  have hx : ∀ C ∈ F, x ∉ C.supp := by
    intro C hC
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hC
    have hn := honly w (hS w hw) (hSh w hw) (Finset.mem_filter.mp hw).2.2.2
    rwa [he] at hn
  have hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S := by
    intro t hat ht
    by_cases he : t = (x : V)
    · exact Or.inl he
    · by_cases hh : t = h
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hat,hh,he⟩))
  have hFnon : F.Nonempty := by
    obtain ⟨w,hw,hwh,hwx⟩ := hordinary
    exact ⟨(evenSubgraph G).connectedComponentMk w,
      Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,hwh,hwx⟩,rfl⟩⟩
  exact bare_ordinary_hub_contact_family_false h x H u hu hxu S hS hSh F
    (by rfl) hx (fun w hw => Finset.mem_image.mpr ⟨w,hw,rfl⟩) hclass hFnon

/-- The two-T2 result is retained as a consequence of the full family result. -/
theorem bare_ordinary_two_t2_endgame_false
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
    (htwo : 2 ≤ (F.filter (fun C => (ordinaryComponentPacket G S C).card = 2)).card) :
    False := by
  apply bare_ordinary_hub_contact_family_false h x H u hu hxu S hS hSh F hF hx htouched hclass
  apply Finset.card_pos.mp
  have hle := Finset.card_le_card (Finset.filter_subset
    (fun C => (ordinaryComponentPacket G S C).card = 2) F)
  omega

end Gallai.TwoException
