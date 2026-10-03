/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.CliqueComponents
public import Gallai.Structure.EvenSubgraph

@[expose] public section

/-! # Actual labels for a touched three-vertex component

The marked predicate is hub adjacency. Labels put a marked vertex first and,
unless all three are marked, an unmarked vertex last. Thus the only incidence
patterns are one, two, or three initial marked vertices. No ordering witness
is assumed by the component consumer.
-/

namespace Gallai

variable {V : Type*} [DecidableEq V]

/-- A touched three-element set admits labels with its marked vertices first. -/
theorem three_set_marked_labels (T : Finset V) (P : V → Prop)
    (hcard : T.card = 3) (htouch : ∃ a ∈ T, P a) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ T = {a, b, c} ∧ P a ∧ (P c → P b) := by
  classical
  by_cases hall : ∀ v ∈ T, P v
  · obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := Finset.card_eq_three.mp hcard
    refine ⟨a, b, c, hab, hac, hbc, hT, ?_, ?_⟩
    · exact hall a (by simp [hT])
    · intro _
      exact hall b (by simp [hT])
  · obtain ⟨a, ha, hPa⟩ := htouch
    push Not at hall
    obtain ⟨c, hc, hPc⟩ := hall
    have hac : a ≠ c := fun h => hPc (h ▸ hPa)
    have hca : c ∈ T.erase a := Finset.mem_erase.mpr ⟨hac.symm, hc⟩
    have h₁ := Finset.card_erase_add_one ha
    have h₂ := Finset.card_erase_add_one hca
    have hn : 0 < ((T.erase a).erase c).card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hn
    obtain ⟨hbc, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hb
    have heq : ({a, b, c} : Finset V) = T := by
      apply Finset.eq_of_subset_of_card_le
      · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          And.intro ha (And.intro hb hc)
      · simp [hba.symm, hac, hbc, hcard]
    exact ⟨a, b, c, hba.symm, hac, hbc, heq.symm, hPa, fun h => (hPc h).elim⟩

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A genuine triangle component touched by a hub supplies ordered labels,
all three triangle edges, and exact component membership. -/
theorem even_triangle_hub_labels (u : V)
    (C : (evenSubgraph G).ConnectedComponent)
    (hcard : C.supp.ncard = 3) (hcomplete : C.toSimpleGraph = ⊤)
    (htouch : ∃ v : evenVertices G, v ∈ C.supp ∧ G.Adj u v) :
    ∃ a b c : evenVertices G,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (∀ v, v ∈ C.supp ↔ v = a ∨ v = b ∨ v = c) ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      G.Adj u a ∧ (G.Adj u c → G.Adj u b) := by
  classical
  have hc : C.supp.toFinset.card = 3 := by
    simpa only [Set.ncard_eq_toFinset_card'] using hcard
  have ht : ∃ v ∈ C.supp.toFinset, G.Adj u v := by
    simpa using htouch
  obtain ⟨a, b, c, hab, hac, hbc, hT, hua, horder⟩ :=
    three_set_marked_labels C.supp.toFinset (fun v => G.Adj u v) hc ht
  have hm : ∀ v, v ∈ C.supp ↔ v = a ∨ v = b ∨ v = c := by
    intro v
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_toFinset] using
      Iff.of_eq (congrArg (fun T => v ∈ T) hT)
  have ha : a ∈ C.supp := (hm a).mpr (Or.inl rfl)
  have hb : b ∈ C.supp := (hm b).mpr (Or.inr (Or.inl rfl))
  have hc' : c ∈ C.supp := (hm c).mpr (Or.inr (Or.inr rfl))
  have hedge : ∀ v w : evenVertices G, v ∈ C.supp → w ∈ C.supp → v ≠ w →
      G.Adj v w := by
    intro v w hv hw hn
    have hh : C.toSimpleGraph.Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
      rw [hcomplete]
      exact fun h => hn (congrArg Subtype.val h)
    exact hh
  exact ⟨a, b, c, hab, hac, hbc, hm, hedge a b ha hb hab,
    hedge a c ha hc' hac, hedge b c hb hc' hbc, hua, horder⟩

end Gallai
