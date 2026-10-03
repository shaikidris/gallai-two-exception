/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparationFamily

@[expose] public section

/-! # Orienting ordinary mates away from retained contacts -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A contact is the recipient, never the donor, when the mate has only
one contact endpoint. This changes orientation, not the deleted edge. -/
noncomputable def orientOrdinaryMate (S : Finset (evenVertices G))
    (e : evenVertices G × evenVertices G) : evenVertices G × evenVertices G :=
  if e.2 ∈ S then (e.2, e.1) else e

/-- Every regular mate has a noncontact endpoint: its third triangle
vertex is already a contact in the deleted packet. -/
theorem ordinary_regular_mate_has_noncontact
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (P : Finset (evenVertices G))
    (M : List (evenVertices G × evenVertices G))
    (hP : P ⊆ ordinaryComponentPacket G S C)
    (hcount : #P = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0))
    (havoid : ∀ e ∈ M, e.1 ∉ P ∧ e.2 ∉ P)
    (hadj : ∀ e ∈ M, G.Adj e.1 e.2)
    (hlabels : ∀ e ∈ M, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) :
    ∀ e ∈ M, e.1 ∉ S ∨ e.2 ∉ S := by
  classical
  intro e he
  obtain ⟨a,hs,ha,hab,hca⟩ := hlabels e he
  have haS := (Finset.mem_filter.mp (hP ha)).1
  by_contra hf
  have hb : e.1 ∈ S := by aesop
  have hc : e.2 ∈ S := by aesop
  have hbc : G.Adj e.1 e.2 := hadj e he
  have hpacket : #(ordinaryComponentPacket G S C) = 3 := by
    rw [ordinary_triangle_contact_count S C a e.1 e.2 hs hab hbc hca haS]
    simp [hb,hc]
  have hPsub : P ⊆ {a} := by
    intro t ht
    have htC := (Finset.mem_filter.mp (hP ht)).2
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at htC
    rcases htC with rfl | rfl | rfl
    · simp
    · exact False.elim ((havoid e he).1 ht)
    · exact False.elim ((havoid e he).2 ht)
  have hle := Finset.card_le_card hPsub
  simp only [Finset.card_singleton] at hle
  rw [hpacket] at hcount
  simp only [ite_true] at hcount
  omega

/-- Orientation preserves triangle support and packet avoidance, while
ensuring the donor is outside the contact set. -/
theorem orientOrdinaryMate_data
    (S P : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (e : evenVertices G × evenVertices G)
    (hn : e.1 ∉ S ∨ e.2 ∉ S)
    (he : G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
      e.1 ∉ P ∧ e.2 ∉ P)
    (hl : ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) :
    let f := orientOrdinaryMate S e
    G.Adj f.1 f.2 ∧ f.1 ∈ C.supp ∧ f.2 ∈ C.supp ∧
      f.1 ∉ P ∧ f.2 ∉ P ∧ f.2 ∉ S ∧
      ∃ a : evenVertices G,
        C.supp = {a,f.1,f.2} ∧ a ∈ P ∧ G.Adj a f.1 ∧ G.Adj f.2 a := by
  classical
  obtain ⟨a,hs,ha,hab,hca⟩ := hl
  by_cases hc : e.2 ∈ S
  · have hb : e.1 ∉ S := hn.resolve_right (not_not.mpr hc)
    simp only [orientOrdinaryMate, ite_eq_left hc]
    refine ⟨he.1.symm,he.2.2.1,he.2.1,he.2.2.2.2,he.2.2.2.1,hb,
      a,?_,ha,hca.symm,hab.symm⟩
    rw [hs]
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  · simpa only [orientOrdinaryMate, ite_eq_right hc] using
      And.intro he.1 ⟨he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2,hc,
        a,hs,ha,hab,hca⟩

/-- Reorientation leaves the unordered endpoints, hence the puncture,
unchanged. -/
theorem orientOrdinaryMate_endpoints
    (S : Finset (evenVertices G)) (e : evenVertices G × evenVertices G)
    (t : evenVertices G) :
    (t = (orientOrdinaryMate S e).1 ∨ t = (orientOrdinaryMate S e).2) ↔
      (t = e.1 ∨ t = e.2) := by
  classical
  by_cases hc : e.2 ∈ S <;>
    simp [orientOrdinaryMate,hc,or_comm]

/-- Normalize a complete regular packet interface without altering its
spokes, mate count, or coverage. The additional donor guard is suitable
for the retained-neighbour positivity argument after mate restoration. -/
theorem ordinary_regular_preparation_oriented
    (S P : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (M : List (evenVertices G × evenVertices G))
    (hP : P ⊆ ordinaryComponentPacket G S C)
    (hcount : #P = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0))
    (hcover : ∀ t, t ∈ C.supp → t ∈ P ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2)
    (hm : ∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
      e.1 ∉ P ∧ e.2 ∉ P)
    (hl : ∀ e ∈ M, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) :
    let M' := M.map (orientOrdinaryMate S)
    M'.length = M.length ∧
      (∀ t, t ∈ C.supp → t ∈ P ∨ ∃ e ∈ M', t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M', G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P ∧ e.2 ∉ P ∧ e.2 ∉ S ∧
        ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P ∧ G.Adj a e.1 ∧ G.Adj e.2 a) := by
  classical
  have hn := ordinary_regular_mate_has_noncontact S C P M hP hcount
    (fun e he => ⟨(hm e he).2.2.2.1,(hm e he).2.2.2.2⟩)
    (fun e he => (hm e he).1) hl
  refine ⟨by simp only [List.length_map],?_,?_⟩
  · intro t ht
    rcases hcover t ht with hp | ⟨e,he,ht⟩
    · exact Or.inl hp
    · exact Or.inr ⟨orientOrdinaryMate S e,
        List.mem_map.mpr ⟨e,he,rfl⟩,
        (orientOrdinaryMate_endpoints S e t).mpr ht⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact orientOrdinaryMate_data S P C f (hn f hf) (hm f hf) (hl f hf)

end Gallai.TwoException
