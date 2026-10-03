/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryMateFlattening

@[expose] public section

/-! # Concrete ambient mate list from a finite component family -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance finiteMateComponentEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- The canonical finite component list supplies a vertex-disjoint ambient
mate list with genuine edges, even endpoints and global spoke avoidance. -/
theorem ordinary_finite_mate_assembly
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hlen : ∀ C ∈ F, (mates C).length ≤ 1)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (x : evenVertices G) (hx : ∀ C ∈ F, x ∉ C.supp) :
    let M := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    M.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
    (∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
      e.1 ∉ insert (x : V) ((F.biUnion P).image Subtype.val) ∧
      e.2 ∉ insert (x : V) ((F.biUnion P).image Subtype.val)) := by
  classical
  dsimp only
  constructor
  · apply ordinary_flattened_mates_pairwise_disjoint F.toList mates
      (List.nodup_iff_pairwise_ne.mp F.nodup_toList)
    · intro C hC
      exact hlen C (Finset.mem_toList.mp hC)
    · intro C hC e he
      obtain ⟨_,hl,hr,_,_⟩ := hmates C (Finset.mem_toList.mp hC) e he
      exact ⟨hl,hr⟩
  · have hav := ordinary_mates_avoid_assembled_spokes G F P mates hsupp
      (fun C hC e he => (hmates C hC e he).2) x hx
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨hedge,_,_,_,_⟩ := hmates C hCF f hfC
    obtain ⟨hl,hr⟩ := hav C hCF f hfC
    exact ⟨hedge,f.1.property,f.2.property,hl,hr⟩

/-- The concrete ordinary list concatenates with hub-component deletions.
This includes a reserved hub spoke in the latter list. -/
theorem ordinary_finite_hub_mate_assembly
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hlen : ∀ C ∈ F, (mates C).length ≤ 1)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (x : evenVertices G) (hx : ∀ C ∈ F, x ∉ C.supp)
    (N : List (V × V))
    (hNdis : N.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    (O ++ N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by
  classical
  dsimp only
  have hO := (ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx).1
  apply ordinary_hub_mate_families_disjoint x _ N hO hNdis ?_ hN
  intro e he
  obtain ⟨f,hf,heq⟩ := List.mem_map.mp he
  subst e
  obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
  have hCF := Finset.mem_toList.mp hC
  obtain ⟨_,hl,hr,_,_⟩ := hmates C hCF f hfC
  exact ⟨C,f.1,f.2,rfl,hx C hCF,hl,hr⟩

/-- Triangle labels and selected spoke membership survive flattening and
the ambient endpoint map, in the literal form used by mate restoration. -/
theorem ordinary_finite_mate_labels
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hlabels : ∀ C ∈ F, ∀ e ∈ mates C, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P C) (x : V) :
    ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
    ∃ (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G),
      e = ((b : V),(c : V)) ∧ C.supp = {a,b,c} ∧
      (a : V) ∈ insert x ((F.biUnion P).image Subtype.val) := by
  classical
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
  have hCF := Finset.mem_toList.mp hC
  obtain ⟨a,hs,ha⟩ := hlabels C hCF f hfC
  refine ⟨C,a,f.1,f.2,rfl,hs,?_⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hCF,ha⟩,rfl⟩

/-- Local actual-contact coverage transports to the assembled ambient
spoke set and concrete mate list. This is the cap consumer's coverage
interface, rather than a newly assumed parity profile. -/
theorem ordinary_finite_contact_coverage
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) (x : V) :
    ∀ t ∈ S, (t : V) ∈ insert x ((F.biUnion P).image Subtype.val) ∨
      ∃ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
        (t : V) = e.1 ∨ (t : V) = e.2 := by
  classical
  intro t ht
  let C := (evenSubgraph G).connectedComponentMk t
  have hC : C ∈ F := htouched t ht
  have htC : t ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mpr rfl
  have htPacket : t ∈ ordinaryComponentPacket G S C := Finset.mem_filter.mpr ⟨ht,htC⟩
  rcases hcover C hC t htPacket with htP | hmate
  · left
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,htP⟩,rfl⟩
  · right
    obtain ⟨e,he,hte⟩ := hmate
    refine ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
    · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
        ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
    · rcases hte with hl | hr
      · exact Or.inl (congrArg Subtype.val hl)
      · exact Or.inr (congrArg Subtype.val hr)

/-- Whole-component local coverage transfers to the concrete ambient
puncture, including vertices which were not neighbours of the centre.
It is used for regular components, not the special T2. -/
theorem ordinary_finite_component_coverage
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (C : (evenSubgraph G).ConnectedComponent) (hC : C ∈ F)
    (hcover : ∀ t, t ∈ C.supp → t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (x : V) :
    ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ insert x ((F.biUnion P).image Subtype.val) ∨
      ∃ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
        (t : V) = e.1 ∨ (t : V) = e.2 := by
  classical
  intro t ht
  rcases hcover t ht with htP | hmate
  · left
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,htP⟩,rfl⟩
  · right
    obtain ⟨e,he,hte⟩ := hmate
    refine ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
    · exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
        ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
    · rcases hte with hl | hr
      · exact Or.inl (congrArg Subtype.val hl)
      · exact Or.inr (congrArg Subtype.val hr)

/-- Actual ordinary contacts are covered by the actual star union or the
combined deletion list. No retained hub contact is silently counted as deleted. -/
theorem ordinary_finite_auxiliary_contact_coverage
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (htouched : ∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F)
    (hcover : ∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (K : Finset V) (N : List (V × V)) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ t ∈ S,
      (t : V) ∈ K ∪ ((F.biUnion P).image Subtype.val) ∨
      ∃ e ∈ O ++ N, (t : V) = e.1 ∨ (t : V) = e.2 := by
  classical
  dsimp only
  intro t ht
  let C := (evenSubgraph G).connectedComponentMk t
  have hC : C ∈ F := htouched t ht
  have htC : t ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mpr rfl
  rcases hcover C hC t (Finset.mem_filter.mpr ⟨ht,htC⟩) with htP | ⟨e,he,hte⟩
  · exact Or.inl (Finset.mem_union_right K (Finset.mem_image.mpr
      ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,htP⟩,rfl⟩))
  · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
        ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
    · rcases hte with hl | hr
      · exact Or.inl (congrArg Subtype.val hl)
      · exact Or.inr (congrArg Subtype.val hr)

/-- Regular native packets cover each original ordinary component in the
actual combined star/mate interface, without inserting a fictitious hub leaf. -/
theorem ordinary_finite_auxiliary_component_coverage
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hcover : ∀ C ∈ F, ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (K : Finset V) (N : List (V × V)) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ K ∪ ((F.biUnion P).image Subtype.val) ∨
      ∃ e ∈ O ++ N, (t : V) = e.1 ∨ (t : V) = e.2 := by
  classical
  dsimp only
  intro C hC t ht
  rcases hcover C hC t ht with htP | ⟨e,he,hte⟩
  · exact Or.inl (Finset.mem_union_right K (Finset.mem_image.mpr
      ⟨t,Finset.mem_biUnion.mpr ⟨C,hC,htP⟩,rfl⟩))
  · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr
        ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩
    · rcases hte with hl | hr
      · exact Or.inl (congrArg Subtype.val hl)
      · exact Or.inr (congrArg Subtype.val hr)

/-- A component with no selected mate is untouched by the whole flattened
mate family, since every listed endpoint lies in its own original component. -/
theorem ordinary_empty_component_avoids_finite_mates
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ D ∈ F, ∀ e ∈ mates D, e.1 ∈ D.supp ∧ e.2 ∈ D.supp)
    (C : (evenSubgraph G).ConnectedComponent) (hempty : mates C = [])
    (t : evenVertices G) (htC : t ∈ C.supp) :
    ∀ e ∈ (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))),
      (t : V) ≠ e.1 ∧ (t : V) ≠ e.2 := by
  classical
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨D,hD,hfD⟩ := List.mem_flatMap.mp hf
  obtain ⟨hl,hr⟩ := hsupp D (Finset.mem_toList.mp hD) f hfD
  have hne : D ≠ C := by
    intro h
    rw [h,hempty] at hfD
    exact List.not_mem_nil hfD
  constructor
  · intro h
    have ht : t = f.1 := Subtype.val_injective h
    have htD : t ∈ D.supp := ht ▸ hl
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex htD htC)
  · intro h
    have ht : t = f.2 := Subtype.val_injective h
    have htD : t ∈ D.supp := ht ▸ hr
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex htD htC)

/-- Even mate endpoints cannot be the originally odd restoration centre. -/
theorem ordinary_even_mates_avoid_odd_centre
    (M : List (V × V)) (u : V) (hu : Odd (G.degree u))
    (heven : ∀ e ∈ M, Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u := by
  intro e he
  obtain ⟨hl,hr⟩ := heven e he
  have hn : ¬ Even (G.degree u) := Nat.not_even_iff_odd.mpr hu
  constructor
  · intro h
    exact hn (h ▸ hl)
  · intro h
    exact hn (h ▸ hr)

/-- Original component separation makes both deletion families avoid the
combined selected private and ordinary contact star. -/
theorem ordinary_finite_hub_mates_avoid_contact_union
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hmates : ∀ C ∈ F, ∀ e ∈ mates C,
      e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧ e.1 ∉ P C ∧ e.2 ∉ P C)
    (x : evenVertices G) (hx : ∀ C ∈ F, x ∉ C.supp)
    (K : Finset V)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a)
    (N : List (V × V))
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hNK : ∀ e ∈ N, e.1 ∉ K ∧ e.2 ∉ K) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ e ∈ O ++ N,
      e.1 ∉ K ∪ ((F.biUnion P).image Subtype.val) ∧
      e.2 ∉ K ∪ ((F.biUnion P).image Subtype.val) := by
  classical
  dsimp only
  have hsep : ∀ C ∈ F, ∀ a b : evenVertices G,
      a ∈ C.supp → (evenSubgraph G).Reachable x b → (a : V) ≠ b := by
    intro C hC a b ha hr he
    have hab : a = b := Subtype.val_injective he
    subst b
    apply hx C hC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans ha
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨f,hf,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨hl,hr,hlP,hrP⟩ := hmates C hCF f hfC
    have havK : ∀ a : evenVertices G, a ∈ C.supp → (a : V) ∉ K := by
      intro a ha hm
      obtain ⟨b,hb,hreach⟩ := hK a hm
      exact hsep C hCF a b ha hreach hb.symm
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨havK f.1 hl,ordinary_component_vertex_avoids_spoke_union
      G F P hsupp C f.1 hl hlP⟩,
      ⟨havK f.2 hr,ordinary_component_vertex_avoids_spoke_union
      G F P hsupp C f.2 hr hrP⟩⟩
  · obtain ⟨a,b,heq,ha,hb⟩ := hN e he
    obtain ⟨hlK,hrK⟩ := hNK e he
    subst e
    have havO : ∀ a : evenVertices G, (evenSubgraph G).Reachable x a →
        (a : V) ∉ (F.biUnion P).image Subtype.val := by
      intro a hr hm
      obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp hm
      obtain ⟨C,hC,hvP⟩ := Finset.mem_biUnion.mp hv
      exact hsep C hC v a (hsupp C hC v hvP) hr hva
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨hlK,havO a ha⟩,⟨hrK,havO b hb⟩⟩

/-- Native ordinary-selector parity is the parity of the actual combined
deletion star once the private selection has its exact ambient count. -/
theorem ordinary_private_union_deletion_parity
    (K L : Finset V) (offset : ℕ) (hKL : Disjoint K L)
    (hK : #K = offset) (hparity : Even (offset + #L)) :
    Even #(K ∪ L) := by
  rw [Finset.card_union_of_disjoint hKL,hK]
  exact hparity

/-- In the odd ordinary-component regime, the native selector yields
regular packets and an even actual deletion star with one private leaf. -/
theorem bare_delayed_odd_component_preparation
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) (hodd : Odd #F)
    (K : Finset V) (hKcard : #K = 1)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      Even #(K ∪ ((F.biUnion P).image Subtype.val)) ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, ∀ t ∈ C.supp,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) := by
  classical
  have heven : Even (1 + #F) := by
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨P,mates,hP,hcount,hpar,hdata,hcover,hdonor⟩ :=
    bare_ordinary_native_even_preparation h x H S F hF hx 1 heven
  have hdis : Disjoint K ((F.biUnion P).image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro t ht hm
    obtain ⟨a,hat,hr⟩ := hK t ht
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hm
    obtain ⟨C,hC,hbP⟩ := Finset.mem_biUnion.mp hb
    have hab : a = b := Subtype.val_injective (hat.trans hbt.symm)
    subst b
    have haC := (Finset.mem_filter.mp (hP C hC hbP)).2
    apply hx C hC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans haC
  exact ⟨P,mates,hP,
    ordinary_private_union_deletion_parity K _ 1 hdis hKcard hpar,
    hdata,hcover,hdonor,hcount⟩

/-- A parity-compatible private offset admits a native regular preparation
without a special packet. -/
theorem bare_delayed_component_preparation
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) (offset : ℕ)
    (heven : Even (offset + #F))
    (K : Finset V) (hKcard : #K = offset)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      Even #(K ∪ ((F.biUnion P).image Subtype.val)) ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, ∀ t ∈ C.supp,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) := by
  classical
  obtain ⟨P,mates,hP,hcount,hpar,hdata,hcover,hdonor⟩ :=
    bare_ordinary_native_even_preparation h x H S F hF hx offset heven
  have hdis : Disjoint K ((F.biUnion P).image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro t ht hm
    obtain ⟨a,hat,hr⟩ := hK t ht
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hm
    obtain ⟨C,hC,hbP⟩ := Finset.mem_biUnion.mp hb
    have hab : a = b := Subtype.val_injective (hat.trans hbt.symm)
    subst b
    have haC := (Finset.mem_filter.mp (hP C hC hbP)).2
    apply hx C hC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans haC
  exact ⟨P,mates,hP,
    ordinary_private_union_deletion_parity K _ offset hdis hKcard hpar,
    hdata,hcover,hdonor,hcount⟩

/-- Odd private offset and even ordinary count force exactly one special
two-contact packet when such a packet exists. The same selected family
supplies the deletion parity, mate labels and contact coverage. -/
theorem bare_delayed_special_component_preparation
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) (offset : ℕ)
    (hodd : Odd offset) (heven : Even #F)
    (hT2 : (F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)).Nonempty)
    (K : Finset V) (hKcard : #K = offset)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      special ⊆ F.filter (fun C => #(ordinaryComponentPacket G S C) = 2) ∧
      #special = 1 ∧
      (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      Even #(K ∪ ((F.biUnion P).image Subtype.val)) ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, ∀ t ∈ ordinaryComponentPacket G S C,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ special, P C = ordinaryComponentPacket G S C ∧ mates C = []) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) + 1 := by
  classical
  obtain ⟨special,P,mates,hs,hsize,hP,hcount,hpar,_,hdata,hcover,hregular,hspec,hdonor⟩ :=
    bare_ordinary_native_spoke_family h x H S F hF hx offset
  have hsOne : #special = 1 := by
    by_contra hn
    have hz : #special = 0 := by omega
    have hEmpty := Finset.card_eq_zero.mp hz
    have hp := hpar (by simpa only [hEmpty,Finset.sdiff_empty] using hT2)
    rw [hcount,hz] at hp
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff] at heven hp
    omega
  have hparity : Even (offset + #((F.biUnion P).image Subtype.val)) := by
    rw [hcount,hsOne]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff] at heven ⊢
    omega
  have hdis : Disjoint K ((F.biUnion P).image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro t ht hm
    obtain ⟨a,hat,hr⟩ := hK t ht
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hm
    obtain ⟨C,hC,hbP⟩ := Finset.mem_biUnion.mp hb
    have hab : a = b := Subtype.val_injective (hat.trans hbt.symm)
    subst b
    have haC := (Finset.mem_filter.mp (hP C hC hbP)).2
    apply hx C hC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans haC
  refine ⟨special,P,mates,hs,hsOne,hP,?_,hdata,hcover,hregular,hspec,hdonor,?_⟩
  · rw [Finset.card_union_of_disjoint hdis,hKcard]
    exact hparity
  · simpa only [hsOne] using hcount

/-- Actual contacts outside the hub determine the ordinary family. -/
theorem ordinary_outside_hub_contact_family
    (x : evenVertices G) (C : (evenSubgraph G).ConnectedComponent)
    (hxC : x ∈ C.supp) (u h : V) :
    let S : Finset (evenVertices G) :=
      Finset.univ.filter (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    (∀ D ∈ F, x ∉ D.supp) ∧
      (∀ a ∈ S, (evenSubgraph G).connectedComponentMk a ∈ F) ∧
      (∀ a ∈ S, G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro D hD hxd
    obtain ⟨a,ha,haD⟩ := Finset.mem_image.mp hD
    have haSupp : a ∈ D.supp := by
      rw [← haD]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    have hDC : D = C := SimpleGraph.ConnectedComponent.eq_of_common_vertex hxd hxC
    exact (Finset.mem_filter.mp ha).2.2.1 (hDC ▸ haSupp)
  · intro a ha
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

/-- A bare protected vertex cannot be an endpoint of any genuine
even-ended deletion edge. This applies to the complete combined family. -/
theorem even_ended_deletions_avoid_bare_vertex
    (h : V) (hbare : eDegree G h = 0) (M : List (V × V))
    (hedges : ∀ e ∈ M,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2 := by
  have hnone : ∀ v, G.Adj h v → Even (G.degree v) → False := by
    intro v hv he
    have hm := (mem_evenNeighbors (G := G) h v).mpr ⟨hv,he⟩
    have hp := Finset.card_pos.mpr ⟨v,hm⟩
    change #(evenNeighbors G h) = 0 at hbare
    omega
  intro e he
  obtain ⟨ha,hl,hr⟩ := hedges e he
  constructor
  · intro hh
    exact hnone e.2 (hh ▸ ha) hr
  · intro hh
    exact hnone e.1 (hh ▸ ha.symm) hl

/-- Native parity-compatible preparation assembles the actual star and
deletion guards, preserving the original bare vertex and odd centre. -/
theorem bare_delayed_native_deletion_bundle
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ C ∈ F, x ∉ C.supp) (offset : ℕ)
    (heven : Even (offset + #F)) (hu : Odd (G.degree u))
    (K : Finset V) (hKcard : #K = offset)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a)
    (N : List (V × V))
    (hNdis : N.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hNE : ∀ e ∈ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hNK : ∀ e ∈ N, e.1 ∉ K ∧ e.2 ∉ K) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    let B := K ∪ ((F.biUnion P).image Subtype.val)
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
    (∀ C ∈ F, (mates C).length ≤ 1 ∧
      (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P C ∧ e.2 ∉ P C) ∧
      (∀ e ∈ mates C, ∃ a : evenVertices G,
        C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
    (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
    (∀ C ∈ F, ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
    Even #B ∧
      (O ++ N).Pairwise (fun e f =>
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ O ++ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
      (∀ e ∈ O ++ N, e.1 ∉ B ∧ e.2 ∉ B) ∧
      (∀ e ∈ O ++ N, e.1 ≠ u ∧ e.2 ≠ u) ∧
      (∀ e ∈ O ++ N, h ≠ e.1 ∧ h ≠ e.2) ∧
      (∀ C ∈ F, ∀ t : evenVertices G, t ∈ C.supp →
        (t : V) ∈ B ∨ ∃ e ∈ O ++ N, (t : V) = e.1 ∨ (t : V) = e.2) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) := by
  classical
  obtain ⟨P,mates,hP,hEven,hdata,hcover,hdonor,hcount⟩ :=
    bare_delayed_component_preparation G h x H S F hF hx offset heven K hKcard hK
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp := by
    intro C hC t ht
    exact (Finset.mem_filter.mp (hP C hC ht)).2
  have hlen := fun C hC => (hdata C hC).1
  have hmates := fun C hC => (hdata C hC).2.1
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hOE := (ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx).2
  have hE : ∀ e ∈ O ++ N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨(hOE e he).1,(hOE e he).2.1,(hOE e he).2.2.1⟩
    · exact hNE e he
  have hhbare : eDegree G h = 0 := H.counterexample.1.2.2.2.2.2.1
  refine ⟨P,mates,hP,hdata,hdonor,hcover,hEven,?_,hE,?_,?_,?_,?_⟩
  · exact ordinary_finite_hub_mate_assembly G F P mates hsupp hlen hmates x hx N hNdis hN
  · exact ordinary_finite_hub_mates_avoid_contact_union G F P mates hsupp
      (fun C hC e he => (hmates C hC e he).2) x hx K hK N hN hNK
  · exact ordinary_even_mates_avoid_odd_centre G (O ++ N) u hu
      (fun e he => (hE e he).2)
  · exact even_ended_deletions_avoid_bare_vertex G h hhbare (O ++ N) hE
  · exact ⟨ordinary_finite_auxiliary_component_coverage G F P mates hcover K N,hcount⟩

/-- The special delayed preparation gives an actual disjoint deletion list
and contact coverage. Unlike regular packets, no full-component coverage
is demanded of the retained vertex in the special triangle. -/
theorem bare_delayed_special_deletion_bundle
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (htouched : ∀ a ∈ S, (evenSubgraph G).connectedComponentMk a ∈ F)
    (hx : ∀ C ∈ F, x ∉ C.supp) (offset : ℕ)
    (hodd : Odd offset) (heven : Even #F)
    (hT2 : (F.filter (fun C => #(ordinaryComponentPacket G S C) = 2)).Nonempty)
    (hu : Odd (G.degree u))
    (K : Finset V) (hKcard : #K = offset)
    (hK : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a)
    (N : List (V × V))
    (hNdis : N.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hNE : ∀ e ∈ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hNK : ∀ e ∈ N, e.1 ∉ K ∧ e.2 ∉ K) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    let B := K ∪ ((F.biUnion P).image Subtype.val)
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    special ⊆ F.filter (fun C => #(ordinaryComponentPacket G S C) = 2) ∧
      #special = 1 ∧ (∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C) ∧
      Even #B ∧
      (∀ C ∈ F, (mates C).length ≤ 1 ∧
        (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
          e.1 ∉ P C ∧ e.2 ∉ P C) ∧
        (∀ e ∈ mates C, ∃ a : evenVertices G,
          C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
      (∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
        t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ C ∈ special, P C = ordinaryComponentPacket G S C ∧ mates C = []) ∧
      (∀ C ∈ F, ∀ e ∈ mates C, e.2 ∉ S) ∧
      (O ++ N).Pairwise (fun e f =>
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
      (∀ e ∈ O ++ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
      (∀ e ∈ O ++ N, e.1 ∉ B ∧ e.2 ∉ B) ∧
      (∀ e ∈ O ++ N, e.1 ≠ u ∧ e.2 ≠ u) ∧
      (∀ e ∈ O ++ N, h ≠ e.1 ∧ h ≠ e.2) ∧
      (∀ a ∈ S, (a : V) ∈ B ∨ ∃ e ∈ O ++ N, (a : V) = e.1 ∨ (a : V) = e.2) ∧
      #((F.biUnion P).image Subtype.val) = #F +
        2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) + 1 := by
  classical
  obtain ⟨special,P,mates,hs,hsOne,hP,hEven,hdata,hcover,hregular,hspec,hdonor,hcount⟩ :=
    bare_delayed_special_component_preparation G h x H S F hF hx offset
      hodd heven hT2 K hKcard hK
  have hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp := by
    intro C hC t ht
    exact (Finset.mem_filter.mp (hP C hC ht)).2
  have hlen := fun C hC => (hdata C hC).1
  have hmates := fun C hC => (hdata C hC).2.1
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hOE := (ordinary_finite_mate_assembly G F P mates hsupp hlen hmates x hx).2
  have hE : ∀ e ∈ O ++ N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨(hOE e he).1,(hOE e he).2.1,(hOE e he).2.2.1⟩
    · exact hNE e he
  refine ⟨special,P,mates,hs,hsOne,hP,hEven,hdata,hregular,hspec,hdonor,?_,hE,?_,?_,?_,?_,hcount⟩
  · exact ordinary_finite_hub_mate_assembly G F P mates hsupp hlen hmates x hx N hNdis hN
  · exact ordinary_finite_hub_mates_avoid_contact_union G F P mates hsupp
      (fun C hC e he => (hmates C hC e he).2) x hx K hK N hN hNK
  · exact ordinary_even_mates_avoid_odd_centre G (O ++ N) u hu
      (fun e he => (hE e he).2)
  · exact even_ended_deletions_avoid_bare_vertex G h
      H.counterexample.1.2.2.2.2.2.1 (O ++ N) hE
  · exact ordinary_finite_auxiliary_contact_coverage G S F P mates htouched hcover K N

/-- The native selected packets inherit actual contact edges, original
even parity and protection of h, jointly with the private star selection. -/
theorem ordinary_private_selected_star_guards
    (u h : V) (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hS : ∀ a ∈ S, G.Adj u a.val ∧ a.val ≠ h)
    (K : Finset V)
    (hK : ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h) :
    let B := K ∪ ((F.biUnion P).image Subtype.val)
    u ∉ B ∧ h ∉ B ∧ ∀ t ∈ B, G.Adj u t ∧ Even (G.degree t) := by
  classical
  dsimp only
  have hleaves : ∀ t ∈ K ∪ ((F.biUnion P).image Subtype.val),
      G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hK t ht
    · obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
      have haS := (Finset.mem_filter.mp (hP C hC haP)).1
      obtain ⟨hadj,hah⟩ := hS a haS
      subst t
      exact ⟨hadj,a.property,hah⟩
  refine ⟨fun hu => G.irrefl (hleaves u hu).1,
    fun hh => (hleaves h hh).2.2 rfl,?_⟩
  intro t ht
  exact ⟨(hleaves t ht).1,(hleaves t ht).2.1⟩

/-- Original boundary labels survive flattening and concatenation with
neutral private mates, in the delayed auxiliary's literal endpoint form. -/
theorem ordinary_finite_private_mate_boundary_labels
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (privates : Finset V) (N : List (V × V))
    (hN : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ e ∈ O ++ N, ∀ t, t = e.1 ∨ t = e.2 →
      t ∈ privates ∨ ∃ C ∈ F, ∃ a : evenVertices G, a ∈ C.supp ∧ (a : V) = t := by
  classical
  dsimp only
  intro e he t ht
  rcases List.mem_append.mp he with he | he
  · obtain ⟨f,hf,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨hl,hr⟩ := hsupp C hCF f hfC
    rcases ht with ht | ht
    · exact Or.inr ⟨C,hCF,f.1,hl,ht.symm⟩
    · exact Or.inr ⟨C,hCF,f.2,hr,ht.symm⟩
  · rcases ht with ht | ht
    · exact Or.inl (ht ▸ (hN e he).1)
    · exact Or.inl (ht ▸ (hN e he).2)

/-- A single contacted ordinary component which is not a full three-contact
triangle has a graph-native singleton preparation. The mate and coverage
labels are retained from the same selector. -/
theorem bare_delayed_single_component_selection
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hC : C ∈ S.image (evenSubgraph G).connectedComponentMk)
    (hx : x ∉ C.supp) (hnotThree : #(ordinaryComponentPacket G S C) ≠ 3) :
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      P C ⊆ ordinaryComponentPacket G S C ∧
      #((P C).image Subtype.val) = 1 ∧
      (mates C).length ≤ 1 ∧
      (∀ e ∈ mates C, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P C ∧ e.2 ∉ P C) ∧
      (∀ e ∈ mates C, ∃ a : evenVertices G,
        C.supp = {a,e.1,e.2} ∧ a ∈ P C ∧ G.Adj a e.1 ∧ G.Adj e.2 a) ∧
      (∀ t ∈ C.supp, t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ mates C, e.2 ∉ S) := by
  classical
  obtain ⟨P,mates,hP,hcount,_,hdata,hcover,hdonor⟩ :=
    bare_ordinary_native_even_preparation h x H S {C}
      (by intro D hD; simpa only [Finset.mem_singleton.mp hD] using hC)
      (by intro D hD; simpa only [Finset.mem_singleton.mp hD] using hx)
      1 (by simp)
  have hfilter : ({C} : Finset (evenSubgraph G).ConnectedComponent).filter
      (fun D => #(ordinaryComponentPacket G S D) = 3) = ∅ := by
    ext D
    simp only [Finset.mem_filter,Finset.mem_singleton,Finset.notMem_empty,iff_false]
    rintro ⟨rfl,heq⟩
    exact hnotThree heq
  have hcard : #((P C).image Subtype.val) = 1 := by
    simpa only [Finset.singleton_biUnion,hfilter,Finset.card_empty,
      Finset.card_singleton,Nat.mul_zero,Nat.add_zero] using hcount
  have hd := hdata C (Finset.mem_singleton_self _)
  exact ⟨P,mates,hP C (Finset.mem_singleton_self _),hcard,hd.1,hd.2.1,hd.2.2,
    hcover C (Finset.mem_singleton_self _),hdonor C (Finset.mem_singleton_self _)⟩

end Gallai.TwoException
