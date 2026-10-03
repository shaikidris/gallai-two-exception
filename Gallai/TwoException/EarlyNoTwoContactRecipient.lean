/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrientedMixedFamily

@[expose] public section

/-! # Recipient avoidance when two-contact packets are absent -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A mate recipient cannot be an original contact in a triangle whose
donor is not a contact, unless that triangle has exactly two contacts. -/
theorem early_mate_recipient_not_contact
    (S Q : Finset (evenVertices G))
    (C : (evenSubgraph G).ConnectedComponent)
    (a b c : evenVertices G)
    (hsupp : C.supp = {a,b,c})
    (ha : a ∈ Q) (hb : b ∉ Q) (hc : c ∉ S)
    (hQ : Q ⊆ ordinaryComponentPacket G S C)
    (hnotTwo : #(ordinaryComponentPacket G S C) ≠ 2) : b ∉ S := by
  classical
  intro hbS
  have haPacket := hQ ha
  have haS := (Finset.mem_filter.mp haPacket).1
  have hab : a ≠ b := by
    intro heq
    exact hb (heq ▸ ha)
  have hpacket : ordinaryComponentPacket G S C = {a,b} := by
    ext t
    constructor
    · intro ht
      obtain ⟨htS,htC⟩ := Finset.mem_filter.mp ht
      rw [hsupp] at htC
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
      rcases htC with rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (hc htS)
    · intro ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact haPacket
      · apply Finset.mem_filter.mpr
        refine ⟨hbS,?_⟩
        rw [hsupp]
        simp
  apply hnotTwo
  rw [hpacket]
  simp [hab]

/-- The local two-contact exclusion applies simultaneously to every
ordinary mate in the flattened family. -/
theorem early_no_two_contact_family_noncontact
    (u x h : V) (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hQ : ∀ C ∈ F, Q C ⊆ ordinaryComponentPacket G S C)
    (hnotTwo : ∀ C ∈ F, #(ordinaryComponentPacket G S C) ≠ 2)
    (hdata : ∀ C ∈ F, ∀ e ∈ mates C,
      e.1 ∉ Q C ∧ e.2 ∉ S ∧
      ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ Q C)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = x ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (havoid : ∀ C ∈ F, ∀ e ∈ mates C, (e.1 : V) ≠ x ∧ (e.1 : V) ≠ h) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ e ∈ O, ¬ G.Adj e.1 u := by
  classical
  intro O e he hadj
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨C,hC,hf⟩ := List.mem_flatMap.mp hf
  have hCF : C ∈ F := Finset.mem_toList.mp hC
  obtain ⟨hb,hc,a,hsupp,ha⟩ := hdata C hCF f hf
  have hnotS := early_mate_recipient_not_contact S (Q C) C a f.1 f.2
    hsupp ha hb hc (hQ C hCF) (hnotTwo C hCF)
  rcases hclass f.1 hadj.symm f.1.property with hx | hh | hS
  · exact (havoid C hCF f hf).1 hx
  · exact (havoid C hCF f hf).2 hh
  · exact hnotS hS

end Gallai.TwoException
