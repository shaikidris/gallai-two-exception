/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyMixedSeparation
public import Gallai.TwoException.EarlySingleSpokeBudget

@[expose] public section

/-! # Mixed packet coverage in the actual auxiliary budget interface -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance coverageComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Native mixed packet labels imply the separated regular-or-special
component alternatives required by the actual single-spoke budget. -/
theorem early_mixed_auxiliary_component_guards
    (u : V) (huOdd : Odd (G.degree u)) (x q : evenVertices G)
    (hxq : G.Adj x q) (B : Finset V) (S : Finset (evenVertices G))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (M : List (V × V))
    (hM : M = ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V))))
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hselected : ∀ C ∈ F, ∀ t ∈ Q C, (t : V) ∈ B)
    (hfull : ∀ C ∈ special, Q C = ordinaryComponentPacket G S C)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ Q C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hmates : ∀ C ∈ F, C ∉ special → ∀ e ∈ mates C,
      e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hspecial : ∀ C ∈ special, ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S C = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u) :
    (∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ≠ x ∧ (t : V) ≠ q) ∧
    (∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u) := by
  classical
  have hne : ∀ v : evenVertices G, (v : V) ≠ u := by
    intro v he
    have heven : Even (G.degree u) := he ▸ v.property
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at huOdd
    omega
  refine ⟨fun C hC => early_ordinary_component_spoke_separation x q hxq C (hx C hC),?_⟩
  intro C hC
  by_cases hs : C ∈ special
  · obtain ⟨a,b,c,hCeq,hab,hbc,hca,hpacket,hcS,hcu⟩ := hspecial C hs
    have hQ : Q C = {a,b} := (hfull C hs).trans hpacket
    have ha : a ∈ Q C := by rw [hQ]; simp
    have hb : b ∈ Q C := by rw [hQ]; simp
    have hc : c ∈ C.supp := by rw [hCeq]; simp
    refine Or.inr ⟨a,b,c,hCeq,hselected C hC a ha,hselected C hC b hb,
      hca.symm,hbc,hne a,hne b,hne c,?_,hcu⟩
    rw [hM]
    exact early_special_vertex_avoids_regular_mates F special mates hmates C hs c hc
  · apply Or.inl
    intro t ht
    rcases hregular C hC hs t ht with hp | ⟨e,he,heq⟩
    · exact Or.inl (hselected C hC t hp)
    · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
      · rw [hM]
        exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
          ⟨C,Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hC,hs⟩),he⟩,rfl⟩
      · exact heq.elim (fun h => Or.inl (congrArg Subtype.val h))
          (fun h => Or.inr (congrArg Subtype.val h))

end Gallai.TwoException
