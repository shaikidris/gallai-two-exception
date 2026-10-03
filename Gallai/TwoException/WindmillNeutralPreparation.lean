/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactSelection
public import Gallai.TwoException.WindmillContactSets

@[expose] public section

/-! # Native ambient neutral-petal preparation -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Transport any selected pending contact set to the ambient vertex type. -/
theorem windmill_selected_contacts_transport
    (x : evenVertices G)
    (A B K : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (q : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hselected : (A ∩ B.biUnion (fun t => {t,f t})).erase q = K) :
    windmillPrivateSet x A ∩
      (windmillPrivateSet x (B.biUnion (fun t => {t,f t}))).erase q.val.val =
      windmillPrivateSet x K := by
  classical
  have hinj := (windmillPrivateEmbedding x).injective
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,hav⟩ := (mem_windmillPrivateSet x A v).mp (Finset.mem_inter.mp hv).1
    have hrest := (Finset.mem_inter.mp hv).2
    obtain ⟨b,hb,hbv⟩ := (mem_windmillPrivateSet x _ v).mp
      (Finset.mem_of_mem_erase hrest)
    have hab : a = b := hinj (hav.trans hbv.symm)
    have hane : a ≠ q := by
      intro he
      exact (Finset.mem_erase.mp hrest).1
        (hav.symm.trans (congrArg (fun t => t.val.val) he))
    apply (mem_windmillPrivateSet x K v).mpr
    refine ⟨a,?_,hav⟩
    rw [←hselected]
    exact Finset.mem_erase.mpr ⟨hane,Finset.mem_inter.mpr ⟨ha,hab ▸ hb⟩⟩
  · intro hv
    obtain ⟨a,ha,hav⟩ := (mem_windmillPrivateSet x K v).mp hv
    rw [←hselected] at ha
    obtain ⟨hane,haInter⟩ := Finset.mem_erase.mp ha
    obtain ⟨haA,haB⟩ := Finset.mem_inter.mp haInter
    refine Finset.mem_inter.mpr ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,haA,hav⟩,
      Finset.mem_erase.mpr ⟨?_,(mem_windmillPrivateSet x _ _).mpr ⟨a,haB,hav⟩⟩⟩
    intro he
    exact hane (hinj (hav.trans he))

/-- Transport the selected pending contacts to the original vertex type.
The intersection is essential: an uncontacted spare mate is not a deleted
contact even though its petal was selected. -/
theorem windmill_selected_contact_transport
    (x : evenVertices G)
    (A B : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hselected : (A ∩ B.biUnion (fun t => {t,f t})).erase (f p) = {p,r}) :
    windmillPrivateSet x A ∩
      (windmillPrivateSet x (B.biUnion (fun t => {t,f t}))).erase (f p).val.val =
      {p.val.val,r.val.val} := by
  classical
  have hinj := (windmillPrivateEmbedding x).injective
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,hav⟩ := (mem_windmillPrivateSet x A v).mp (Finset.mem_inter.mp hv).1
    have hrest := (Finset.mem_inter.mp hv).2
    obtain ⟨b,hb,hbv⟩ := (mem_windmillPrivateSet x _ v).mp
      (Finset.mem_of_mem_erase hrest)
    have hab : a = b := hinj (hav.trans hbv.symm)
    have hane : a ≠ f p := by
      intro he
      exact (Finset.mem_erase.mp hrest).1 (hav.symm.trans (congrArg (fun t => t.val.val) he))
    have ham : a ∈ (A ∩ B.biUnion (fun t => {t,f t})).erase (f p) :=
      Finset.mem_erase.mpr ⟨hane,Finset.mem_inter.mpr ⟨ha,hab ▸ hb⟩⟩
    rw [hselected] at ham
    rcases Finset.mem_insert.mp ham with he | he
    · exact Finset.mem_insert.mpr (Or.inl (hav.symm.trans (congrArg (fun t => t.val.val) he)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (hav.symm.trans (congrArg (fun t => t.val.val) (Finset.mem_singleton.mp he)))))
  · intro hv
    have hsource : ∃ a ∈ ({p,r} : Finset _), a.val.val = v := by
      rcases Finset.mem_insert.mp hv with he | he
      · exact ⟨p,by simp,he.symm⟩
      · exact ⟨r,by simp,(Finset.mem_singleton.mp he).symm⟩
    obtain ⟨a,ha,hav⟩ := hsource
    rw [←hselected] at ha
    obtain ⟨hane,haInter⟩ := Finset.mem_erase.mp ha
    obtain ⟨haA,haB⟩ := Finset.mem_inter.mp haInter
    refine Finset.mem_inter.mpr ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,haA,hav⟩,
      Finset.mem_erase.mpr ⟨?_,(mem_windmillPrivateSet x _ _).mpr ⟨a,haB,hav⟩⟩⟩
    intro he
    exact hane (hinj (hav.trans he))

/-- The indexed neutral petals supply a concrete ambient mate family with
the genuine-edge, avoidance and even-neighbour labels used in delayed payment. -/
theorem bare_windmill_neutral_mates
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P A B : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hBP : B ⊆ P) (hinv : Function.Involutive f)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b) :
    let chosen := windmillPrivateSet x (B.biUnion (fun r => {r,f r}))
    let Z := (P.filter (fun r => r ∈ A ∨ f r ∈ A)) \ B
    let M := (Z.toList.map (fun r => (r,f r))).map
      (fun e => (e.1.val.val,e.2.val.val))
    M.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    (∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) ∧
      e.1 ∉ chosen ∧ e.2 ∉ chosen ∧ (x : V) ≠ e.1 ∧ (x : V) ≠ e.2) ∧
    (∀ e ∈ M, ∀ t, G.Adj e.2 t → Even (G.degree t) → t = (x : V) ∨ t = e.1) ∧
    (∀ a ∈ A, a.val.val ∈ chosen ∨ ∃ e ∈ M, a.val.val = e.1 ∨ a.val.val = e.2) := by
  classical
  dsimp only
  obtain ⟨hdis,havoid,hcover⟩ := indexed_neutral_petal_preparation f P A B hBP hindex
  have hinj := (windmillPrivateEmbedding x).injective
  refine ⟨?_,?_,?_,?_⟩
  · rw [List.pairwise_map]
    apply hdis.imp
    intro e g hne
    have hn : ∀ a b : {a : evenVertices G // (evenSubgraph G).Adj x a},
        a ≠ b → a.val.val ≠ b.val.val := by
      intro a b hab he
      exact hab (hinj he)
    exact ⟨hn e.1 g.1 hne.1,hn e.1 g.2 hne.2.1,
      hn e.2 g.1 hne.2.2.1,hn e.2 g.2 hne.2.2.2⟩
  · intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨r,hr,hvr⟩ := List.mem_map.mp hv
    subst v
    obtain ⟨hl,hr'⟩ := havoid (r,f r) (List.mem_map.mpr ⟨r,hr,rfl⟩)
    have hav : ∀ a, a ∉ B.biUnion (fun r => {r,f r}) →
        a.val.val ∉ windmillPrivateSet x (B.biUnion (fun r => {r,f r})) := by
      intro a ha hm
      obtain ⟨b,hb,hba⟩ := (mem_windmillPrivateSet x _ _).mp hm
      exact ha ((hinj hba) ▸ hb)
    exact ⟨(hedge r (f r)).mpr rfl,r.val.property,(f r).val.property,
      hav r hl,hav (f r) hr',
      fun he => r.property.ne (Subtype.ext he),
      fun he => (f r).property.ne (Subtype.ext he)⟩
  · intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨r,_,hvr⟩ := List.mem_map.mp hv
    subst v
    simpa only [hinv r] using bare_windmill_private_even_neighbors h x H f hedge (f r)
  · intro a ha
    rcases hcover a ha with hac | ⟨e,he,heq⟩
    · left
      exact (mem_windmillPrivateSet x _ _).mpr ⟨a,hac,rfl⟩
    · right
      refine ⟨(e.1.val.val,e.2.val.val),List.mem_map.mpr ⟨e,he,rfl⟩,?_⟩
      rcases heq with heq | heq
      · exact Or.inl (congrArg (fun a => a.val.val) heq)
      · exact Or.inr (congrArg (fun a => a.val.val) heq)

/-- Releasing the spoke to a chosen private vertex leaves a disjoint
hub-component deletion list, with genuine even-ended edges throughout. -/
theorem bare_windmill_neutral_mates_with_spoke
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P A B : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hBP : B ⊆ P) (hinv : Function.Involutive f)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (q : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hq : q ∈ B.biUnion (fun r => {r,f r})) :
    let Z := (P.filter (fun r => r ∈ A ∨ f r ∈ A)) \ B
    let M := (Z.toList.map (fun r => (r,f r))).map
      (fun e => (e.1.val.val,e.2.val.val))
    let N := ((x : V),q.val.val) :: M
    N.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    (∀ e ∈ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
    (∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b) ∧
    (∀ e ∈ N,
      e.1 ∉ (windmillPrivateSet x (B.biUnion (fun r => {r,f r}))).erase q.val.val ∧
      e.2 ∉ (windmillPrivateSet x (B.biUnion (fun r => {r,f r}))).erase q.val.val) ∧
    (∀ a ∈ A,
      a.val.val ∈ windmillPrivateSet x A ∩
        (windmillPrivateSet x (B.biUnion (fun r => {r,f r}))).erase q.val.val ∨
      ∃ e ∈ N, a.val.val = e.1 ∨ a.val.val = e.2) := by
  classical
  dsimp only
  obtain ⟨hdis,hguards,_,hcover⟩ :=
    bare_windmill_neutral_mates h x H f P A B hBP hinv hindex hedge
  have hqc : q.val.val ∈ windmillPrivateSet x (B.biUnion (fun r => {r,f r})) :=
    (mem_windmillPrivateSet x _ _).mpr ⟨q,hq,rfl⟩
  refine ⟨List.pairwise_cons.mpr ⟨?_,hdis⟩,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨_,_,_,hl,hr,hxl,hxr⟩ := hguards e he
    exact ⟨hxl,hxr,fun heq => hl (heq ▸ hqc),fun heq => hr (heq ▸ hqc)⟩
  · intro e he
    rcases List.mem_cons.mp he with heq | he
    · subst e
      exact ⟨q.property,x.property,q.val.property⟩
    · exact ⟨(hguards e he).1,(hguards e he).2.1,(hguards e he).2.2.1⟩
  · intro e he
    rcases List.mem_cons.mp he with heq | he
    · subst e
      exact ⟨x,q.val,rfl,SimpleGraph.Reachable.refl x,q.property.reachable⟩
    · obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
      subst e
      obtain ⟨r,_,hvr⟩ := List.mem_map.mp hv
      subst v
      exact ⟨r.val,(f r).val,rfl,r.property.reachable,(f r).property.reachable⟩
  · intro e he
    rcases List.mem_cons.mp he with heq | he
    · subst e
      constructor
      · intro hx
        exact hub_not_mem_windmillPrivateSet x _ (Finset.mem_of_mem_erase hx)
      · exact Finset.notMem_erase _ _
    · obtain ⟨_,_,_,hl,hr,_,_⟩ := hguards e he
      exact ⟨fun hm => hl (Finset.mem_of_mem_erase hm),
        fun hm => hr (Finset.mem_of_mem_erase hm)⟩
  · intro a ha
    by_cases haq : a.val.val = q.val.val
    · exact Or.inr ⟨((x : V),q.val.val),List.mem_cons_self ..,Or.inr haq⟩
    · rcases hcover a ha with hac | ⟨e,he,hea⟩
      · exact Or.inl (Finset.mem_inter.mpr
          ⟨(mem_windmillPrivateSet x A _).mpr ⟨a,ha,rfl⟩,
            Finset.mem_erase.mpr ⟨haq,hac⟩⟩)
      · exact Or.inr ⟨e,List.mem_cons_of_mem _ he,hea⟩

/-- A contact-only selected subset inherits adjacency, original even
parity and the private cap needed for the native auxiliary star. -/
theorem bare_windmill_selected_contact_guards
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V) (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (K : Finset V) (hK : K ⊆ windmillPrivateSet x A)
    (hcontact : ∀ a ∈ A, G.Adj u a.val.val) :
    u ∉ K ∧ (x : V) ∉ K ∧
      ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ eDegree G t = 2 := by
  obtain ⟨hu,hadj⟩ := windmillPrivateSet_contact_guards x u A hcontact
  refine ⟨fun hm => hu (hK hm),
    fun hm => hub_not_mem_windmillPrivateSet x A (hK hm),?_⟩
  intro t ht
  exact ⟨hadj t (hK ht),bare_windmillPrivateSet_leaf_guards h x H A t (hK ht)⟩

/-- The double-spare delayed selection supplies exactly three genuine
ambient contact leaves and excludes the unpaid mate. -/
theorem bare_windmill_double_spare_ambient_selection
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hp : p ∈ A) (hfp : f p ≠ p) (hr : r ∈ A) (hfrA : f r ∈ A)
    (hfr : f r ≠ r) (hdis : Disjoint ({p,f p} : Finset _) {r,f r})
    (hcontact : ∀ a ∈ A, G.Adj u a.val.val) :
    let K := windmillPrivateSet x ((A ∩ ({p,f p} ∪ {r,f r})).erase (f p))
    #K = 3 ∧ u ∉ K ∧ (x : V) ∉ K ∧ (f p).val.val ∉ K ∧
      ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ eDegree G t = 2 := by
  classical
  dsimp only
  obtain ⟨_,hc⟩ := reserved_petal_double_spare_count f A p r
    hp hfp hr hfrA hfr hdis
  have hsub : windmillPrivateSet x ((A ∩ ({p,f p} ∪ {r,f r})).erase (f p)) ⊆
      windmillPrivateSet x A := by
    intro t ht
    obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x _ _).mp ht
    exact (mem_windmillPrivateSet x A t).mpr
      ⟨a,(Finset.mem_inter.mp (Finset.mem_of_mem_erase ha)).1,hat⟩
  obtain ⟨hu,hx,hguards⟩ := bare_windmill_selected_contact_guards h x H u A _ hsub hcontact
  refine ⟨?_,hu,hx,?_,hguards⟩
  · rw [windmillPrivateSet_card]
    exact hc
  · intro hm
    obtain ⟨a,ha,he⟩ := (mem_windmillPrivateSet x _ _).mp hm
    have heq : a = f p := (windmillPrivateEmbedding x).injective he
    exact (Finset.mem_erase.mp ha).1 heq

/-- Actual original even contacts split into the retained hub, its private
contacts, and contacts outside the original hub component. -/
theorem bare_windmill_even_contact_partition
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (u : V) :
    let A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
      Finset.univ.filter (fun a => G.Adj u a.val.val)
    let S : Finset (evenVertices G) :=
      Finset.univ.filter (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    ∀ t, G.Adj u t → Even (G.degree t) →
      t = (x : V) ∨ t ∈ windmillPrivateSet x A ∨
      t = h ∨ ∃ a ∈ S, (a : V) = t := by
  classical
  dsimp only
  intro t hut ht
  let a : evenVertices G := ⟨t,ht⟩
  by_cases haC : a ∈ C.supp
  · rcases ((bare_windmill h x H C hxC).1 a).mp haC with hax | hxa
    · exact Or.inl (congrArg Subtype.val hax)
    · refine Or.inr (Or.inl ?_)
      exact (mem_windmillPrivateSet x _ t).mpr
        ⟨⟨a,hxa⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hut⟩,rfl⟩
  · by_cases hth : t = h
    · exact Or.inr (Or.inr (Or.inl hth))
    · exact Or.inr (Or.inr (Or.inr ⟨a,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hut,haC,hth⟩,rfl⟩))

/-- Native private and ordinary coverage combine into the actual auxiliary
contact guard, including the retained protected vertex. -/
theorem bare_delayed_combined_contact_coverage
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (u q : V) (B : Finset V) (M : List (V × V))
    (hprivate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      G.Adj u a.val.val → a.val.val ∈ B ∨
        ∃ e ∈ ((x : V),q) :: M, a.val.val = e.1 ∨ a.val.val = e.2)
    (hordinary : ∀ a : evenVertices G,
      G.Adj u a.val → a ∉ C.supp → a.val ≠ h →
        a.val ∈ B ∨ ∃ e ∈ ((x : V),q) :: M, a.val = e.1 ∨ a.val = e.2) :
    ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ ((x : V),q) :: M, t = e.1 ∨ t = e.2) ∨ t = h := by
  classical
  intro t hut ht
  rcases bare_windmill_even_contact_partition h x H C hxC u t hut ht with
    htx | hpriv | hth | hord
  · exact Or.inr (Or.inl ⟨((x : V),q),List.mem_cons_self ..,Or.inl htx⟩)
  · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x _ t).mp hpriv
    have hua : G.Adj u a.val.val := (Finset.mem_filter.mp ha).2
    rcases hprivate a hua with haB | ⟨e,he,hae⟩
    · exact Or.inl (hat ▸ haB)
    · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)
  · exact Or.inr (Or.inr hth)
  · obtain ⟨a,ha,hat⟩ := hord
    obtain ⟨hua,haC,hah⟩ := (Finset.mem_filter.mp ha).2
    rcases hordinary a hua haC hah with haB | ⟨e,he,hae⟩
    · exact Or.inl (hat ▸ haB)
    · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)

/-- The selected two-contact identity refines the native neutral preparation
to precisely the leaves consumed by offset-two delayed reconstruction. -/
theorem bare_windmill_two_contact_neutral_coverage
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P A B : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hBP : B ⊆ P) (hinv : Function.Involutive f)
    (hindex : ∀ a, ∃! t, t ∈ P ∧ (a = t ∨ a = f t))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hq : f p ∈ B.biUnion (fun t => {t,f t}))
    (hselected : (A ∩ B.biUnion (fun t => {t,f t})).erase (f p) = {p,r}) :
    let Z := (P.filter (fun t => t ∈ A ∨ f t ∈ A)) \ B
    let M := (Z.toList.map (fun t => (t,f t))).map
      (fun e => (e.1.val.val,e.2.val.val))
    let N := ((x : V),(f p).val.val) :: M
    N.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    (∀ e ∈ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
    (∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b) ∧
    (∀ e ∈ N, e.1 ∉ ({p.val.val,r.val.val} : Finset V) ∧
      e.2 ∉ ({p.val.val,r.val.val} : Finset V)) ∧
    (∀ a ∈ A, a.val.val ∈ ({p.val.val,r.val.val} : Finset V) ∨
      ∃ e ∈ N, a.val.val = e.1 ∨ a.val.val = e.2) := by
  classical
  dsimp only
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_neutral_mates_with_spoke
    h x H f P A B hBP hinv hindex hedge (f p) hq
  have heq := windmill_selected_contact_transport x A B f p r hselected
  refine ⟨hdis,hNE,hreach,?_,?_⟩
  · intro e he
    constructor
    · intro hm
      rw [←heq] at hm
      exact (havoid e he).1 (Finset.mem_inter.mp hm).2
    · intro hm
      rw [←heq] at hm
      exact (havoid e he).2 (Finset.mem_inter.mp hm).2
  · intro a ha
    rcases hcover a ha with hm | hm
    · exact Or.inl (heq ▸ hm)
    · exact Or.inr hm

/-- Neutral petals leave the reserved contact and both spare-petal contacts pending. -/
theorem bare_windmill_three_contact_neutral_coverage
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P A B : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hBP : B ⊆ P) (hinv : Function.Involutive f)
    (hindex : ∀ a, ∃! t, t ∈ P ∧ (a = t ∨ a = f t))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hq : f p ∈ B.biUnion (fun t => {t,f t}))
    (hselected : (A ∩ B.biUnion (fun t => {t,f t})).erase (f p) = {p,r,f r}) :
    let Z := (P.filter (fun t => t ∈ A ∨ f t ∈ A)) \ B
    let M := (Z.toList.map (fun t => (t,f t))).map
      (fun e => (e.1.val.val,e.2.val.val))
    let N := ((x : V),(f p).val.val) :: M
    N.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    (∀ e ∈ N, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) ∧
    (∀ e ∈ N, ∃ a b : evenVertices G,
      e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b) ∧
    (∀ e ∈ N, e.1 ∉ ({p.val.val,r.val.val,(f r).val.val} : Finset V) ∧
      e.2 ∉ ({p.val.val,r.val.val,(f r).val.val} : Finset V)) ∧
    (∀ a ∈ A, a.val.val ∈ ({p.val.val,r.val.val,(f r).val.val} : Finset V) ∨
      ∃ e ∈ N, a.val.val = e.1 ∨ a.val.val = e.2) := by
  classical
  dsimp only
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_neutral_mates_with_spoke
    h x H f P A B hBP hinv hindex hedge (f p) hq
  have heq := windmill_selected_contacts_transport x A B {p,r,f r} f (f p) hselected
  have hmap : windmillPrivateSet x ({p,r,f r} : Finset _) =
      {p.val.val,r.val.val,(f r).val.val} := by
    simp only [windmillPrivateSet,Finset.map_insert,Finset.map_singleton]
    rfl
  rw [hmap] at heq
  refine ⟨hdis,hNE,hreach,?_,?_⟩
  · intro e he
    constructor
    · intro hm
      rw [←heq] at hm
      exact (havoid e he).1 (Finset.mem_inter.mp hm).2
    · intro hm
      rw [←heq] at hm
      exact (havoid e he).2 (Finset.mem_inter.mp hm).2
  · intro a ha
    rcases hcover a ha with hm | hm
    · exact Or.inl (heq ▸ hm)
    · exact Or.inr hm

end Gallai.TwoException
