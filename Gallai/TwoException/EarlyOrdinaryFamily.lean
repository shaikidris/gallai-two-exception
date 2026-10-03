/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrdinaryPacketGuards
public import Gallai.TwoException.OrdinaryPreparationFamily
public import Gallai.TwoException.OrdinaryFiniteMateAssembly

@[expose] public section

/-! # Native regular family for early restoration -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance earlyFamilyComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Choose regular packets simultaneously, retaining global mate
disjointness and the structural recipient guards for the flattened list. -/
theorem bare_early_ordinary_family
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ C ∈ F, (P C).Nonempty ∧ P C ⊆ ordinaryComponentPacket G S C ∧
        (∀ t ∈ P C, t ∈ C.supp) ∧
        (∀ t, t ∈ C.supp → t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (mates C).length ≤ 1 ∧
        #(P C) = 1 + 2 * (if #(ordinaryComponentPacket G S C) = 3 then 1 else 0)) ∧
      (let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)));
        O.Pairwise (fun e g =>
          e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
        ∀ C ∈ F,
          (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
            ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
          (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
            (P C).image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
          (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
            G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
            (P C).image Subtype.val = {(a : V),(b : V),(c : V)})) := by
  classical
  obtain ⟨P,mates,hdata⟩ :=
    bare_ordinary_regular_preparation_family h x H S F hF hx
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp := by
    intro C hC t ht
    exact (Finset.mem_filter.mp ((hdata C hC).2.1 ht)).2
  have hmates := fun C hC => (hdata C hC).2.2.2.1
  have hlen := fun C hC => (hdata C hC).2.2.2.2.1
  refine ⟨P,mates,?_,?_⟩
  · intro C hC
    obtain ⟨hnon,hsub,hcover,hm,hl,_,hcount,_⟩ := hdata C hC
    exact ⟨hnon,hsub,hsupp C hC,hcover,hm,hl,hcount⟩
  · dsimp only
    refine ⟨(ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx).1,?_⟩
    intro C hC
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF hC)
    have hwC : w ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr he
    apply bare_early_ordinary_regular_guard h x w H S C (hx C hC) hwC hw
      (P C) (mates C) _ (hsupp C hC) ((hdata C hC).2.2.1)
    · intro e he
      exact ⟨(hmates C hC e he).2.2.2.1,(hmates C hC e he).2.2.2.2⟩
    · intro e he
      obtain ⟨a,hs,ha,_,_⟩ := (hdata C hC).2.2.2.2.2.2.2 e he
      exact ⟨a,hs,ha⟩
    · intro e he
      exact ordinary_flattened_recipient_mem F.toList mates C
        (Finset.mem_toList.mpr hC) e he

end Gallai.TwoException
