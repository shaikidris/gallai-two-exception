/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.BareAmbientCorridor
public import Gallai.TwoException.OrdinaryFiniteMateAssembly

@[expose] public section

/-! # Actual ordinary preparations at the second corridor endpoint -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance longPreparationComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Construct one coherent regular family from all actual ordinary contacts
of the second corridor vertex. The selected star and flattened mate list
avoid the entire windmill component and preserve the protected vertex.
The empty family is allowed; no positive contact count is required. -/
theorem bare_long_ordinary_preparation_family
    (h v : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (hsep : ∀ t ∈ Subtype.val '' C.supp, ¬ G.Adj v t) :
    let S : Finset (evenVertices G) :=
      Finset.univ.filter (fun t => G.Adj v t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ Z ∈ F, P Z ⊆ ordinaryComponentPacket G S Z) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 3)) ∧
      (∀ Z ∈ F, (mates Z).length ≤ 1 ∧
        (∀ e ∈ mates Z, G.Adj e.1 e.2 ∧ e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
          e.1 ∉ P Z ∧ e.2 ∉ P Z) ∧
        (∀ e ∈ mates Z, ∃ a : evenVertices G,
          Z.supp = {a,e.1,e.2} ∧ a ∈ P Z ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ Z ∈ F, ∀ t ∈ Z.supp,
        t ∈ P Z ∨ ∃ e ∈ mates Z, t = e.1 ∨ t = e.2) ∧
      (∀ Z ∈ F, ∀ e ∈ mates Z, e.2 ∉ S) ∧
      let B := (F.biUnion P).image Subtype.val
      let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
      (∀ t ∈ B, G.Adj v t ∧ Even (G.degree t) ∧ t ≠ h ∧
        t ∉ Subtype.val '' C.supp) ∧
      M.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
        e.1 ∉ B ∧ e.2 ∉ B ∧ h ≠ e.1 ∧ h ≠ e.2 ∧
        e.1 ∉ Subtype.val '' C.supp ∧ e.2 ∉ Subtype.val '' C.supp) ∧
      (∀ t, G.Adj v t → Even (G.degree t) → t ≠ h →
        t ∈ B ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) := by
  classical
  let S : Finset (evenVertices G) :=
    Finset.univ.filter (fun t => G.Adj v t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  have hfamily := ordinary_outside_hub_contact_family G x C hxC v h
  change (∀ Z ∈ F, x ∉ Z.supp) ∧
    (∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F) ∧
    (∀ t ∈ S, G.Adj v t.val ∧ t ∉ C.supp ∧ t.val ≠ h) at hfamily
  obtain ⟨hx,htouched,hS⟩ := hfamily
  obtain ⟨P,mates,hP,hcount,_,hdata,hcover,hdonor⟩ :=
    bare_ordinary_native_even_preparation h x H S F (by rfl) hx #F ⟨#F,rfl⟩
  let B := (F.biUnion P).image Subtype.val
  let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hsupp : ∀ Z ∈ F, ∀ t ∈ P Z, t ∈ Z.supp := by
    intro Z hZ t ht
    exact (Finset.mem_filter.mp (hP Z hZ ht)).2
  obtain ⟨hdis,hm⟩ := ordinary_finite_mate_assembly G F P mates hsupp
    (fun Z hZ => (hdata Z hZ).1) (fun Z hZ => (hdata Z hZ).2.1) x hx
  have heven : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    exact ⟨(hm e he).1,(hm e he).2.1,(hm e he).2.2.1⟩
  have hhavoid := even_ended_deletions_avoid_bare_vertex G h
    H.counterexample.1.2.2.2.2.2.1 M heven
  have houtside : ∀ Z ∈ F, ∀ t ∈ Z.supp, (t : V) ∉ Subtype.val '' C.supp := by
    intro Z hZ t ht
    rintro ⟨w,hw,hwt⟩
    have hwt' : w = t := Subtype.val_injective hwt
    have htC : t ∈ C.supp := hwt' ▸ hw
    have hZC := SimpleGraph.ConnectedComponent.eq_of_common_vertex ht htC
    exact hx Z hZ (hZC.symm ▸ hxC)
  refine ⟨P,mates,hP,hcount,hdata,hcover,hdonor,?_,hdis,?_,?_⟩
  · intro t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨Z,hZ,haP⟩ := Finset.mem_biUnion.mp ha
    have haS := (Finset.mem_filter.mp (hP Z hZ haP)).1
    obtain ⟨hva,_,hah⟩ := hS a haS
    exact ⟨hva,a.property,hah,houtside Z hZ a (hsupp Z hZ a haP)⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨Z,hZ,hfZ⟩ := List.mem_flatMap.mp hf
    have hZF := Finset.mem_toList.mp hZ
    have hguard := hm ((f.1 : V),(f.2 : V)) he
    obtain ⟨_,hl,hr,_,_⟩ := (hdata Z hZF).2.1 f hfZ
    obtain ⟨hhl,hhr⟩ := hhavoid ((f.1 : V),(f.2 : V)) he
    refine ⟨hguard.1,f.1.property,f.2.property,?_,?_,hhl,hhr,
      houtside Z hZF f.1 hl,houtside Z hZF f.2 hr⟩
    · exact fun hb => hguard.2.2.2.1 (Finset.mem_insert_of_mem hb)
    · exact fun hb => hguard.2.2.2.2 (Finset.mem_insert_of_mem hb)
  · intro t hvt he hth
    have htoutside : (⟨t,he⟩ : evenVertices G) ∉ C.supp := by
      intro htC
      exact hsep t ⟨⟨t,he⟩,htC,rfl⟩ hvt
    have htS : (⟨t,he⟩ : evenVertices G) ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvt,htoutside,hth⟩
    let Z := (evenSubgraph G).connectedComponentMk (⟨t,he⟩ : evenVertices G)
    have htZ : (⟨t,he⟩ : evenVertices G) ∈ Z.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff Z _).mpr rfl
    have hZF : Z ∈ F := htouched _ htS
    rcases hcover Z hZF ⟨t,he⟩ htZ with hp | ⟨e,heM,hends⟩
    · exact Or.inl (Finset.mem_image.mpr
        ⟨⟨t,he⟩,Finset.mem_biUnion.mpr ⟨Z,hZF,hp⟩,rfl⟩)
    · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
      · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
          ⟨Z,Finset.mem_toList.mpr hZF,heM⟩,rfl⟩
      · rcases hends with hl | hr
        · exact Or.inl (congrArg Subtype.val hl)
        · exact Or.inr (congrArg Subtype.val hr)

end Gallai.TwoException
