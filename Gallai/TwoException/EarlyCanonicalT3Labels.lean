/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalZeroOrT3
public import Gallai.TwoException.OrdinaryContactShapes

@[expose] public section

/-! # Original triangle labels for the canonical T3 branch -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalT3LabelComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- A canonical T3 packet supplies three genuine triangle vertices, their
full even-component support and all three original centre contacts. -/
theorem bare_canonical_t3_labels
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (Z : (evenSubgraph G).ConnectedComponent)
    (hZ : Z ∈ earlyOrdinaryContactComponents G h x u)
    (hthree : #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 3) :
    ∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      G.Adj u a ∧ G.Adj u b ∧ G.Adj u c ∧
      (a : V) ≠ h ∧ (b : V) ≠ h ∧ (c : V) ≠ h := by
  classical
  obtain ⟨hF,hx,_,hS,_⟩ := bare_early_canonical_contact_guards h u x H
  obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp (hF hZ)
  have haZ : a ∈ Z.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff Z a).mpr heq
  rcases bare_ordinary_contact_shapes h x a H (earlyOriginalContacts G h x u) Z
    (hx Z hZ) haZ ha with hi | ⟨b,c,hs,hab,hbc,hca,hpacket⟩
  · rw [hi.2] at hthree
    simp only [Finset.card_singleton] at hthree
    omega
  · have hfull : ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z =
        {a,b,c} := by
      rcases hpacket with hp | hp | hp | hp
      · rw [hp] at hthree
        simp only [Finset.card_singleton] at hthree
        omega
      · have hle : #({a,b} : Finset _) ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        rw [hp] at hthree
        omega
      · have hle : #({a,c} : Finset _) ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        rw [hp] at hthree
        omega
      · exact hp
    have hcontact : ∀ t ∈ ({a,b,c} : Finset _), G.Adj u t ∧ (t : V) ≠ h := by
      intro t ht
      have htP : t ∈ ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z :=
        hfull.symm ▸ ht
      exact hS t (Finset.mem_filter.mp htP).1
    have haC := hcontact a (by simp)
    have hbC := hcontact b (by simp)
    have hcC := hcontact c (by simp)
    exact ⟨a,b,c,hs,hab,hbc,hca,haC.1,hbC.1,hcC.1,haC.2,hbC.2,hcC.2⟩

end Gallai.TwoException
