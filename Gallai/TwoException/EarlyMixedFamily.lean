/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlySpecialFamily
public import Gallai.TwoException.OrdinarySpokeAssembly

@[expose] public section

/-! # A single packet function combining special and regular components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance mixedFamilyComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Build the ordinary part of the early auxiliary with mates only from
regular components. Special components retain their full original contact
packet and its noncontact witness. -/
theorem bare_early_mixed_family
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hsub : special ⊆ F)
    (hspecial : ∀ C ∈ special, ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      ordinaryComponentPacket G S C = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u) :
    ∃ Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ C ∈ F, (Q C).Nonempty ∧ Q C ⊆ ordinaryComponentPacket G S C ∧
        ∀ t ∈ Q C, t ∈ C.supp) ∧
      (∀ C ∈ F, C ∉ special →
        (∀ t, t ∈ C.supp → t ∈ Q C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ Q C ∧ e.2 ∉ Q C) ∧ (mates C).length ≤ 1 ∧
        #(Q C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0)) ∧
      (∀ C ∈ special, Q C = ordinaryComponentPacket G S C) ∧
      (let O := ((F \ special).toList.flatMap mates).map
        (fun e => ((e.1 : V),(e.2 : V)));
        O.Pairwise (fun e g =>
          e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
        ∀ C ∈ F, C ∉ special →
          (∃ a : evenVertices G, (Q C).image Subtype.val = {(a : V)} ∧
            ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
          (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
            (Q C).image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
          (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
            G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
            (Q C).image Subtype.val = {(a : V),(b : V),(c : V)})) := by
  classical
  obtain ⟨P,mates,hdata,hglobal⟩ := bare_early_ordinary_family h x H S (F \ special)
    (fun C hC => hF (Finset.mem_sdiff.mp hC).1)
    (fun C hC => hx C (Finset.mem_sdiff.mp hC).1)
  let Q := fun C => if C ∈ special then ordinaryComponentPacket G S C else P C
  have hregular : ∀ C, C ∉ special → Q C = P C := by
    intro C hC
    simp only [Q,if_neg hC]
  refine ⟨Q,mates,?_,?_,?_,?_⟩
  · intro C hC
    by_cases hs : C ∈ special
    · obtain ⟨a,b,c,_,_,_,_,hp,_,_⟩ := hspecial C hs
      have hQ : Q C = ordinaryComponentPacket G S C := by simp [Q,hs]
      refine ⟨?_,by rw [hQ],?_⟩
      · rw [hQ,hp]; simp
      · intro t ht
        rw [hQ] at ht
        exact (Finset.mem_filter.mp ht).2
    · have hd := hdata C (Finset.mem_sdiff.mpr ⟨hC,hs⟩)
      rw [hregular C hs]
      exact ⟨hd.1,hd.2.1,hd.2.2.1⟩
  · intro C hC hs
    rw [hregular C hs]
    have hd := hdata C (Finset.mem_sdiff.mpr ⟨hC,hs⟩)
    exact ⟨hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2⟩
  · intro C hC
    simp only [Q,if_pos hC]
  · dsimp only at hglobal ⊢
    refine ⟨hglobal.1,?_⟩
    intro C hC hs
    rw [hregular C hs]
    exact hglobal.2 C (Finset.mem_sdiff.mpr ⟨hC,hs⟩)

/-- The merged packet family has the exact ambient deletion count used
by the parity selector, including the one extra contact per special T2. -/
theorem early_mixed_spokes_count
    (S : Finset (evenVertices G))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hsub : special ⊆ F)
    (hsupp : ∀ C ∈ F, ∀ t ∈ Q C, t ∈ C.supp)
    (hregular : ∀ C ∈ F, C ∉ special →
      #(Q C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0))
    (hspecial : ∀ C ∈ special,
      #(ordinaryComponentPacket G S C) = 2 ∧ #(Q C) = 2) :
    #((F.biUnion Q).image Subtype.val) = #F +
      2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) + #special := by
  classical
  apply ordinary_selected_spokes_count G F
    (F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) special Q
    (Finset.filter_subset _ _) hsub hsupp
  intro C hC
  by_cases hs : C ∈ special
  · obtain ⟨hsize,hQ⟩ := hspecial C hs
    simp only [Finset.mem_filter,hsize]
    simp [hs,hQ]
  · have ht : C ∈ F.filter (fun C => #(ordinaryComponentPacket G S C) = 3) ↔
        #(ordinaryComponentPacket G S C) = 3 := by simp [hC]
    simpa only [ht,if_neg hs,Nat.add_zero] using hregular C hC hs

end Gallai.TwoException
