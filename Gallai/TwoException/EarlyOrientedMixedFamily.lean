/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyMixedFamily
public import Gallai.TwoException.EarlyOrientedFamily

@[expose] public section

/-! # Oriented mixed packets retaining native restoration labels -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance orientedMixedComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Mix special T2 contacts with oriented regular mates. Donor avoidance
and genuine triangle labels remain available to the actual auxiliary. -/
theorem bare_early_oriented_mixed_family
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
          e.1 ∉ Q C ∧ e.2 ∉ Q C ∧ e.2 ∉ S ∧
          ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ Q C ∧
            G.Adj a e.1 ∧ G.Adj e.2 a) ∧ (mates C).length ≤ 1 ∧
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
  obtain ⟨P,mates,hdata⟩ := bare_early_oriented_regular_family h x H S (F \ special)
    (fun C hC => hF (Finset.mem_sdiff.mp hC).1)
    (fun C hC => hx C (Finset.mem_sdiff.mp hC).1)
  have hsupp := fun C hC => (hdata C hC).2.2.1
  have hlen := fun C hC => (hdata C hC).2.2.2.2.1
  have hmates : ∀ C ∈ F \ special, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P C ∧ e.2 ∉ P C := by
    intro C hC e he
    have hm := (hdata C hC).2.2.2.2.2.2 e he
    exact ⟨hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2.1⟩
  let O := ((F \ special).toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hglobal : O.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
      ∀ C ∈ F \ special,
        (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
          ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
        (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
          (P C).image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
        (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
          G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
          (P C).image Subtype.val = {(a : V),(b : V),(c : V)}) := by
    refine ⟨(ordinary_finite_mate_assembly G (F \ special) P mates hsupp hlen
      hmates x (fun C hC => hx C (Finset.mem_sdiff.mp hC).1)).1,?_⟩
    intro C hC
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (hF (Finset.mem_sdiff.mp hC).1)
    have hwC : w ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mpr he
    apply bare_early_ordinary_regular_guard h x w H S C
      (hx C (Finset.mem_sdiff.mp hC).1) hwC hw (P C) (mates C) O
      (hsupp C hC) ((hdata C hC).2.2.2.1)
    · intro e he
      exact ⟨(hmates C hC e he).2.2.2.1,(hmates C hC e he).2.2.2.2⟩
    · intro e he
      obtain ⟨a,hs,ha,_,_⟩ := ((hdata C hC).2.2.2.2.2.2 e he).2.2.2.2.2.2
      exact ⟨a,hs,ha⟩
    · intro e he
      exact ordinary_flattened_recipient_mem (F \ special).toList mates C
        (Finset.mem_toList.mpr hC) e he
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
    exact ⟨hd.2.2.2.1,hd.2.2.2.2.2.2,hd.2.2.2.2.1,hd.2.2.2.2.2.1⟩
  · intro C hC
    simp only [Q,if_pos hC]
  · dsimp only at hglobal ⊢
    refine ⟨hglobal.1,?_⟩
    intro C hC hs
    rw [hregular C hs]
    exact hglobal.2 C (Finset.mem_sdiff.mpr ⟨hC,hs⟩)


/-- A contact in a touched ordinary component is selected or an oriented
recipient. Contacts in the hub component need not belong to the ordinary
component family. -/
theorem early_mixed_recipient_coverage_at
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hfull : ∀ C ∈ special, Q C = ordinaryComponentPacket G S C)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ Q C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hdonor : ∀ C ∈ F, C ∉ special → ∀ e ∈ mates C, e.2 ∉ S)
    (t : evenVertices G) (ht : t ∈ S)
    (htouched : (evenSubgraph G).connectedComponentMk t ∈ F) :
    (t : V) ∈ (F.biUnion Q).image Subtype.val ∨
      ∃ e ∈ ((F \ special).toList.flatMap mates).map
        (fun e => ((e.1 : V),(e.2 : V))), (t : V) = e.1 := by
  classical
  let C := (evenSubgraph G).connectedComponentMk t
  have hC : C ∈ F := htouched
  have htC : t ∈ C.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mpr rfl
  have hselected : t ∈ Q C → (t : V) ∈ (F.biUnion Q).image Subtype.val := by
    intro hp
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,hp⟩,rfl⟩
  by_cases hs : C ∈ special
  · apply Or.inl
    apply hselected
    rw [hfull C hs]
    exact Finset.mem_filter.mpr ⟨ht,htC⟩
  · rcases hregular C hC hs t htC with hp | ⟨e,he,heq⟩
    · exact Or.inl (hselected hp)
    · rcases heq with heq | heq
      · exact Or.inr ⟨((e.1 : V),(e.2 : V)),List.mem_map.mpr
          ⟨e,List.mem_flatMap.mpr ⟨C,Finset.mem_toList.mpr
            (Finset.mem_sdiff.mpr ⟨hC,hs⟩),he⟩,rfl⟩,
          congrArg Subtype.val heq⟩
      · exact False.elim (hdonor C hC hs e he (heq ▸ ht))

/-- Mixed contacts are either selected or an oriented regular recipient;
special components need no mate and contribute their entire contact set. -/
theorem early_mixed_recipient_coverage
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hfull : ∀ C ∈ special, Q C = ordinaryComponentPacket G S C)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ Q C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hdonor : ∀ C ∈ F, C ∉ special → ∀ e ∈ mates C, e.2 ∉ S) :
    ∀ t ∈ S, (t : V) ∈ (F.biUnion Q).image Subtype.val ∨
      ∃ e ∈ ((F \ special).toList.flatMap mates).map
        (fun e => ((e.1 : V),(e.2 : V))), (t : V) = e.1 := by
  intro t ht
  exact early_mixed_recipient_coverage_at S F special Q mates hfull hregular
    hdonor t ht (htouched t ht)

/-- Every flattened regular mate keeps its triangle label and an anchor
in the merged ambient spoke set, in the form required by prefix payment. -/
theorem early_mixed_flattened_labels
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hlabels : ∀ C ∈ F, C ∉ special → ∀ e ∈ mates C,
      ∃ a : evenVertices G, C.supp = {a,e.1,e.2} ∧ a ∈ Q C) :
    ∀ e ∈ ((F \ special).toList.flatMap mates).map
      (fun e => ((e.1 : V),(e.2 : V))),
      ∃ (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G),
        e = ((b : V),(c : V)) ∧ C.supp = {a,b,c} ∧
        (a : V) ∈ (F.biUnion Q).image Subtype.val := by
  classical
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
  obtain ⟨hCF,hCS⟩ := Finset.mem_sdiff.mp (Finset.mem_toList.mp hC)
  obtain ⟨a,hs,ha⟩ := hlabels C hCF hCS f hfC
  exact ⟨C,a,f.1,f.2,rfl,hs,Finset.mem_image.mpr
    ⟨a,Finset.mem_biUnion.mpr ⟨C,hCF,ha⟩,rfl⟩⟩

end Gallai.TwoException
