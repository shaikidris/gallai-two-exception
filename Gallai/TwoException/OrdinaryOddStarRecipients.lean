/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeSpokeFamily

@[expose] public section

/-! # Recipient noncontact in the odd-star ordinary preparation regime -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance oddStarRecipientsEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A contact recipient with a noncontact donor is exactly a regular T2.
The native parity rule excludes such a mate when the deleted star is odd. -/
theorem ordinary_odd_star_recipients_noncontact
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hm : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∉ P C ∧
      ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧
        G.Adj a e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.2 a)
    (hdonor : ∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S)
    (hspecial : ∀ C ∈ F, C ∈ special → P C = ordinaryComponentPacket G S C)
    (k : ℕ) (hk : Odd k)
    (heven : (F.filter (fun C => #(ordinaryComponentPacket G S C) = 2) \ special).Nonempty →
      Even k) :
    ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∉ S := by
  classical
  intro C hC e he hcontact
  obtain ⟨havoid,a,hs,ha,hab,hbc,hca⟩ := hm C hC e he
  have haS := (Finset.mem_filter.mp (hP C hC ha)).1
  have htwo : #(ordinaryComponentPacket G S C) = 2 := by
    rw [ordinary_triangle_contact_count S C a e.1 e.2 hs hab hbc hca haS]
    simp [hcontact,hdonor C hC e he]
  have hn : C ∉ special := by
    intro hCs
    have hp : e.1 ∈ ordinaryComponentPacket G S C :=
      Finset.mem_filter.mpr ⟨hcontact,by simp [hs]⟩
    rw [← hspecial C hC hCs] at hp
    exact havoid hp
  have hke := heven ⟨C,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hC,htwo⟩,hn⟩⟩
  exact (Nat.not_even_iff_odd.mpr hk) hke

/-- A noncontact ordinary mate recipient is not adjacent to the centre:
the classified exceptional alternatives are excluded by its component and
by the prescribed bare vertex's zero E-degree. -/
theorem bare_ordinary_noncontact_recipient_nonadjacent
    (h u : V) (x b c : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hb : b ∈ C.supp) (hbc : G.Adj b c) (hbS : b ∉ S)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S) :
    ¬ G.Adj b u := by
  intro hbu
  rcases hclass b hbu.symm b.property with he | he | hs
  · have he' : b = x := Subtype.ext he
    exact hx (he' ▸ hb)
  · have hbare := H.counterexample.1.2.2.2.2.2.1
    have hempty : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hbare
    have ha : G.Adj h c := by simpa only [he] using hbc
    have hc := (mem_evenNeighbors (G := G) h c).mpr ⟨ha,c.property⟩
    rw [hempty] at hc
    simpa using hc
  · exact hbS hs

end Gallai.TwoException
