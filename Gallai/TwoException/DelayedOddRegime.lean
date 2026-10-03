/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.DelayedNativeAuxiliary
public import Gallai.TwoException.WindmillNeutralPreparation

@[expose] public section

/-! # Graph-native delayed payment with an odd ordinary-component count -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance delayedOddComponents : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Delayed payment closes the odd multi-component regime and the single
ordinary component with fewer than three contacts. Every preparation and
its cardinality are constructed from the original graph. -/
theorem bare_delayed_odd_or_single_ordinary_regime_false
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    Odd #F → (1 < #F ∨ (#F = 1 ∧
      ∀ D ∈ F, #(ordinaryComponentPacket G S D) ≠ 3)) → False := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro hodd hcount
  obtain ⟨f,R,hinv,hfree,hindex,hedge,_⟩ := bare_windmill_indexed_petals h x H C hxC
  obtain ⟨r,⟨hrR,hpr⟩,_⟩ := hindex p
  let q := f p
  let A := Finset.univ.filter (fun a : {a : evenVertices G // (evenSubgraph G).Adj x a} =>
    G.Adj u a.val.val)
  have hpairset : ({r,f r} : Finset _) = {p,q} := by
    rcases hpr with hpr | hpr
    · subst p; rfl
    · change ({r,f r} : Finset _) = {p,f p}
      rw [hpr,hinv r]
      exact Finset.pair_comm _ _
  have hchosen : windmillPrivateSet x
      (({r} : Finset _).biUnion (fun a => {a,f a})) = {p.val.val,q.val.val} := by
    rw [Finset.singleton_biUnion,hpairset]
    simp only [windmillPrivateSet,Finset.map_insert,Finset.map_singleton]
    rfl
  have hpqne : p.val.val ≠ q.val.val := by
    intro heq
    exact hfree p ((windmillPrivateEmbedding x).injective heq.symm)
  have hchosenErase : (windmillPrivateSet x
      (({r} : Finset _).biUnion (fun a => {a,f a}))).erase q.val.val = {p.val.val} := by
    rw [hchosen]
    ext t
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hne,ht | ht⟩
      · exact ht
      · exact False.elim (hne ht)
    · intro ht
      exact ⟨fun heq => hpqne (ht.symm.trans heq),Or.inl ht⟩
  have hqChosen : q ∈ ({r} : Finset _).biUnion (fun a => {a,f a}) := by
    rw [Finset.singleton_biUnion,hpairset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  let Z := (R.filter (fun a => a ∈ A ∨ f a ∈ A)) \ {r}
  let N := (Z.toList.map (fun a => (a,f a))).map (fun e => (e.1.val.val,e.2.val.val))
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_neutral_mates_with_spoke
    h x H f R A {r} (by simpa using hrR) hinv hindex hedge q hqChosen
  rw [hchosenErase] at havoid hcover
  let privates := windmillPrivateSet x Finset.univ
  have hpriv : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨a,_,hat⟩ := (mem_windmillPrivateSet x _ t).mp ht
    subst t
    exact ⟨a.property.symm,(bare_windmillPrivateSet_leaf_guards h x H Finset.univ
      a.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)).2⟩
  have hNpriv : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates := by
    intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨a,_,hva⟩ := List.mem_map.mp hv
    subst v
    exact ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩,
      (mem_windmillPrivateSet x _ _).mpr ⟨f a,Finset.mem_univ _,rfl⟩⟩
  have hpPriv : p.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ _,rfl⟩
  have hnotH : p.val.val ≠ h := by
    have hbare := H.counterexample.1.2.2.2.2.2.1
    have ha := even_ended_deletions_avoid_bare_vertex G h hbare
      [((x : V),p.val.val)] (by
        intro e he; simp only [List.mem_singleton] at he; subst e
        exact ⟨p.property,x.property,p.val.property⟩)
    exact (ha ((x : V),p.val.val) (by simp)).2.symm
  obtain ⟨hxF,htouched,hS⟩ := ordinary_outside_hub_contact_family G x C hxC u h
  have hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ ({p.val.val} : Finset V) ∨
      (∃ e ∈ ((x : V),q.val.val) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h := by
    intro t hut ht
    rcases bare_windmill_even_contact_partition h x H C hxC u t hut ht with
      htx | hprivate | hth | hord
    · exact Or.inr (Or.inl ⟨((x : V),q.val.val),List.mem_cons_self ..,Or.inl htx⟩)
    · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x A t).mp hprivate
      rcases hcover a ha with hac | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ (Finset.mem_inter.mp hac).2)
      · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr (Or.inr hth))
    · exact Or.inr (Or.inr (Or.inl hord))
  have hevenOffset : Even (1 + #F) := by
    change Odd #F at hodd
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  obtain ⟨P,mates,_,_,_,hpacketCount,_,D,_,_,hreturn⟩ := bare_delayed_native_auxiliary_endpoint G
    h u x p.val q.val H S F (by intro C hC; exact hC) htouched hxF 1 hevenOffset hu
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
    {p.val.val} privates (by simp)
    (by intro t ht; have htP : t = p.val.val := by simpa using ht
        subst t; exact ⟨p.val,rfl,p.property.reachable⟩)
    (by intro t ht; have htP : t = p.val.val := by simpa using ht
        subst t; exact ⟨hup,p.val.property,hnotH⟩)
    (by intro t ht; have htP : t = p.val.val := by simpa using ht
        subst t; exact hpPriv)
    N hdis hreach hNE havoid hNpriv hpriv hcontact p.property
    ((hedge p q).mpr rfl)
    (hpriv p.val.val hpPriv).2
    p.property.reachable
    (fun e he => ⟨fun heq => (havoid e (List.mem_cons_of_mem _ he)).1
      (heq ▸ Finset.mem_singleton_self _),fun heq =>
      (havoid e (List.mem_cons_of_mem _ he)).2 (heq ▸ Finset.mem_singleton_self _)⟩)
  obtain ⟨E,_,_,_,_,_,_,_,_,hfinish⟩ := hreturn (by simp)
    (bare_windmill_private_even_neighbors h x H f hedge p)
  have hready : 1 < #F ∨ #((F.biUnion P).image Subtype.val) = 1 := by
    rcases hcount with hcount | ⟨hone,hnotThree⟩
    · exact Or.inl hcount
    · right
      have hfilter : F.filter (fun D => #(ordinaryComponentPacket G S D) = 3) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro D hD
        exact hnotThree D (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hD).2
      have hc : #((F.biUnion P).image Subtype.val) = #F := by
        simpa only [hfilter,Finset.card_empty,Nat.mul_zero,Nat.add_zero] using hpacketCount
      exact hc.trans hone
  obtain ⟨_,_,_,_,_,T,hsize,hh⟩ := hfinish (by simp) hready
  exact H.counterexample.2 ⟨T,hsize,hh⟩

/-- The odd multi-component delayed regime is a special case of the
combined graph-native return. -/
theorem bare_delayed_odd_ordinary_regime_false
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    Odd #F → 1 < #F → False := by
  dsimp only
  intro hodd hcount
  exact bare_delayed_odd_or_single_ordinary_regime_false h u x H C hxC p hup hu
    hodd (Or.inl hcount)

/-- A disjoint singly contacted spare petal closes delayed payment with a
positive even number of ordinary contact components. All selections are
constructed from original graph contacts. -/
theorem bare_delayed_even_single_spare_regime_false
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hur : G.Adj u r.val.val)
    (hpr : p ≠ r) (hprEdge : ¬ (evenSubgraph G).Adj p.val r.val)
    (hsingle : ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
      G.Adj u a.val → a = x)
    (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    Even #F → 0 < #F → False := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro heven hpositive
  obtain ⟨f,R,hinv,hfree,hindex,hedge,_⟩ := bare_windmill_indexed_petals h x H C hxC
  let q := f p
  let A := Finset.univ.filter (fun a : {a : evenVertices G // (evenSubgraph G).Adj x a} =>
    G.Adj u a.val.val)
  have hpA : p ∈ A := by simp [A,hup]
  have hrA : r ∈ A := by simp [A,hur]
  have hfr : f r ∉ A := by
    intro hm
    have he := hsingle (f r).val ((hedge r (f r)).mpr rfl) (Finset.mem_filter.mp hm).2
    exact (f r).property.ne he.symm
  have hdisPetals : Disjoint ({p,f p} : Finset _) {r,f r} := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha
    · rw [ha] at hb
      rcases hb with he | he
      · exact hpr he
      · exact hprEdge (((hedge r p).mpr he.symm).symm)
    · rw [ha] at hb
      rcases hb with he | he
      · exact hprEdge ((hedge p r).mpr he)
      · exact hpr (hinv.injective he)
  obtain ⟨B,hBR,_,hchosen,hselected⟩ := indexed_reserved_single_spare_selection
    f hinv R A hindex p r hpA (hfree p) hrA hfr hdisPetals
  have hqChosen : q ∈ B.biUnion (fun a => {a,f a}) := by
    rw [hchosen]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let Z := (R.filter (fun a => a ∈ A ∨ f a ∈ A)) \ B
  let N := (Z.toList.map (fun a => (a,f a))).map (fun e => (e.1.val.val,e.2.val.val))
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_two_contact_neutral_coverage
    h x H f R A B hBR hinv hindex hedge p r hqChosen hselected
  let K : Finset V := {p.val.val,r.val.val}
  let privates := windmillPrivateSet x Finset.univ
  have hpriv : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨a,_,hat⟩ := (mem_windmillPrivateSet x _ t).mp ht
    subst t
    exact ⟨a.property.symm,(bare_windmillPrivateSet_leaf_guards h x H Finset.univ
      a.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)).2⟩
  have hNpriv : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates := by
    intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨a,_,hva⟩ := List.mem_map.mp hv
    subst v
    exact ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩,
      (mem_windmillPrivateSet x _ _).mpr ⟨f a,Finset.mem_univ _,rfl⟩⟩
  have hnotH : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ h := by
    intro a
    have hbare := H.counterexample.1.2.2.2.2.2.1
    have ha := even_ended_deletions_avoid_bare_vertex G h hbare
      [((x : V),a.val.val)] (by
        intro e he; simp only [List.mem_singleton] at he; subst e
        exact ⟨a.property,x.property,a.val.property⟩)
    exact (ha ((x : V),a.val.val) (by simp)).2.symm
  have hprV : p.val.val ≠ r.val.val := fun he => hpr ((windmillPrivateEmbedding x).injective he)
  have hKcard : #K = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hprV),Finset.card_singleton]
  have hKlabels : ∀ t ∈ K, ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      t = a.val.val ∧ G.Adj u a.val.val := by
    intro t ht
    rcases Finset.mem_insert.mp ht with he | he
    · exact ⟨p,he,hup⟩
    · exact ⟨r,Finset.mem_singleton.mp he,hur⟩
  obtain ⟨hxF,htouched,hS⟩ := ordinary_outside_hub_contact_family G x C hxC u h
  have hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∨ (∃ e ∈ ((x : V),q.val.val) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h := by
    intro t hut ht
    rcases bare_windmill_even_contact_partition h x H C hxC u t hut ht with
      htx | hprivate | hth | hord
    · exact Or.inr (Or.inl ⟨((x : V),q.val.val),List.mem_cons_self ..,Or.inl htx⟩)
    · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x A t).mp hprivate
      rcases hcover a ha with hac | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ hac)
      · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr (Or.inr hth))
    · exact Or.inr (Or.inr (Or.inl hord))
  have hevenOffset : Even (2 + #F) := by
    change Even #F at heven
    rw [Nat.even_iff] at heven ⊢
    omega
  obtain ⟨P,mates,_,_,_,_,_,D,_,_,hreturn⟩ := bare_delayed_native_auxiliary_endpoint G
    h u x p.val q.val H S F (by intro C hC; exact hC) htouched hxF 2 hevenOffset hu
    (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
    K privates hKcard
    (by intro t ht; obtain ⟨a,rfl,_⟩ := hKlabels t ht
        exact ⟨a.val,rfl,a.property.reachable⟩)
    (by intro t ht; obtain ⟨a,rfl,hua⟩ := hKlabels t ht
        exact ⟨hua,a.val.property,hnotH a⟩)
    (by intro t ht; obtain ⟨a,rfl,_⟩ := hKlabels t ht
        exact (mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)
    N hdis hreach hNE havoid hNpriv hpriv hcontact p.property
    ((hedge p q).mpr rfl)
    (hpriv p.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ _,rfl⟩)).2
    p.property.reachable
    (fun e he => ⟨fun heq => (havoid e (List.mem_cons_of_mem _ he)).1
      (heq ▸ Finset.mem_insert_self _ _),fun heq =>
      (havoid e (List.mem_cons_of_mem _ he)).2 (heq ▸ Finset.mem_insert_self _ _)⟩)
  obtain ⟨E,_,_,_,_,_,_,_,hmixed,_⟩ := hreturn (Finset.mem_insert_self _ _)
    (bare_windmill_private_even_neighbors h x H f hedge p)
  have hstrict : 1 < #(K.erase p.val.val) + #F := by
    have hc := Finset.card_erase_add_one (Finset.mem_insert_self p.val.val {r.val.val})
    change #K = 2 at hKcard
    change 0 < #F at hpositive
    change #(K.erase p.val.val) + 1 = #K at hc
    omega
  obtain ⟨_,_,_,_,_,T,hsize,hh⟩ := hmixed hstrict
  exact H.counterexample.2 ⟨T,hsize,hh⟩

/-- A two-contact ordinary triangle supplies the special packet when the
ordinary-component count is even and at least four. -/
theorem bare_delayed_even_special_ordinary_regime_false
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    Even #F → 4 ≤ #F →
    (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty → False := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro heven hcount hT2
  change 4 ≤ #F at hcount
  obtain ⟨f,R,hinv,hfree,hindex,hedge,_⟩ := bare_windmill_indexed_petals h x H C hxC
  obtain ⟨r,⟨hrR,hpr⟩,_⟩ := hindex p
  let q := f p
  let A := Finset.univ.filter (fun a : {a : evenVertices G // (evenSubgraph G).Adj x a} =>
    G.Adj u a.val.val)
  have hpairset : ({r,f r} : Finset _) = {p,q} := by
    rcases hpr with hpr | hpr
    · subst p; rfl
    · change ({r,f r} : Finset _) = {p,f p}
      rw [hpr,hinv r]
      exact Finset.pair_comm _ _
  have hchosen : windmillPrivateSet x
      (({r} : Finset _).biUnion (fun a => {a,f a})) = {p.val.val,q.val.val} := by
    rw [Finset.singleton_biUnion,hpairset]
    simp only [windmillPrivateSet,Finset.map_insert,Finset.map_singleton]
    rfl
  have hpqne : p.val.val ≠ q.val.val := by
    intro heq
    exact hfree p ((windmillPrivateEmbedding x).injective heq.symm)
  have hchosenErase : (windmillPrivateSet x
      (({r} : Finset _).biUnion (fun a => {a,f a}))).erase q.val.val = {p.val.val} := by
    rw [hchosen]
    ext t
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hne,ht | ht⟩
      · exact ht
      · exact False.elim (hne ht)
    · intro ht
      exact ⟨fun heq => hpqne (ht.symm.trans heq),Or.inl ht⟩
  have hqChosen : q ∈ ({r} : Finset _).biUnion (fun a => {a,f a}) := by
    rw [Finset.singleton_biUnion,hpairset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  let Z := (R.filter (fun a => a ∈ A ∨ f a ∈ A)) \ {r}
  let N := (Z.toList.map (fun a => (a,f a))).map (fun e => (e.1.val.val,e.2.val.val))
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_neutral_mates_with_spoke
    h x H f R A {r} (by simpa using hrR) hinv hindex hedge q hqChosen
  rw [hchosenErase] at havoid hcover
  let privates := windmillPrivateSet x Finset.univ
  have hpriv : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨a,_,hat⟩ := (mem_windmillPrivateSet x _ t).mp ht
    subst t
    exact ⟨a.property.symm,(bare_windmillPrivateSet_leaf_guards h x H Finset.univ
      a.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)).2⟩
  have hNpriv : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates := by
    intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨a,_,hva⟩ := List.mem_map.mp hv
    subst v
    exact ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩,
      (mem_windmillPrivateSet x _ _).mpr ⟨f a,Finset.mem_univ _,rfl⟩⟩
  have hpPriv : p.val.val ∈ privates :=
    (mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ _,rfl⟩
  have hnotH : p.val.val ≠ h := by
    have hbare := H.counterexample.1.2.2.2.2.2.1
    have ha := even_ended_deletions_avoid_bare_vertex G h hbare
      [((x : V),p.val.val)] (by
        intro e he; simp only [List.mem_singleton] at he; subst e
        exact ⟨p.property,x.property,p.val.property⟩)
    exact (ha ((x : V),p.val.val) (by simp)).2.symm
  obtain ⟨hxF,htouched,hS⟩ := ordinary_outside_hub_contact_family G x C hxC u h
  have hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ ({p.val.val} : Finset V) ∨
      (∃ e ∈ ((x : V),q.val.val) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h := by
    intro t hut ht
    rcases bare_windmill_even_contact_partition h x H C hxC u t hut ht with
      htx | hprivate | hth | hord
    · exact Or.inr (Or.inl ⟨((x : V),q.val.val),List.mem_cons_self ..,Or.inl htx⟩)
    · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x A t).mp hprivate
      rcases hcover a ha with hac | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ (Finset.mem_inter.mp hac).2)
      · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr (Or.inr hth))
    · exact Or.inr (Or.inr (Or.inl hord))
  obtain ⟨special,P,mates,_,_,_,_,_,_,_,_,_,D,_,_,hreturn⟩ :=
    bare_delayed_special_native_auxiliary G h u x p.val q.val H C hxC
      S rfl F (by intro D hD; exact hD) htouched hxF 1 (by decide)
      heven hT2 hu {p.val.val} privates (by simp)
      (by intro t ht; have htP : t = p.val.val := by simpa using ht
          subst t; exact ⟨p.val,rfl,p.property.reachable⟩)
      (by intro t ht; have htP : t = p.val.val := by simpa using ht
          subst t; exact ⟨hup,p.val.property,hnotH⟩)
      (by intro t ht; have htP : t = p.val.val := by simpa using ht
          subst t; exact hpPriv)
      N hdis hreach hNE havoid hNpriv hpriv hcontact p.property
      ((hedge p q).mpr rfl) (hpriv p.val.val hpPriv).2 p.property.reachable
      (fun e he => ⟨fun heq => (havoid e (List.mem_cons_of_mem _ he)).1
        (heq ▸ Finset.mem_singleton_self _),fun heq =>
        (havoid e (List.mem_cons_of_mem _ he)).2 (heq ▸ Finset.mem_singleton_self _)⟩)
  obtain ⟨E,_,_,_,_,_,_,hfinish⟩ := hreturn (by simp)
    (bare_windmill_private_even_neighbors h x H f hedge p)
  obtain ⟨_,_,_,_,_,T,hsize,hh⟩ := hfinish (by simpa using (show 2 < #F by omega))
  exact H.counterexample.2 ⟨T,hsize,hh⟩


/-- Two ordinary components, one with two contacts, and a spare double petal
supply the final delayed-payment reduction. -/
theorem bare_delayed_two_special_double_spare_regime_false
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hur : G.Adj u r.val.val)
    (hpr : p ≠ r) (hprEdge : ¬ (evenSubgraph G).Adj p.val r.val)
    (hdouble : ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
      a ≠ x → G.Adj u a.val)
    (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    #F = 2 →
    (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty → False := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro hcount hT2
  change #F = 2 at hcount
  have heven : Even #F := by rw [hcount]; decide
  obtain ⟨f,R,hinv,hfree,hindex,hedge,_⟩ := bare_windmill_indexed_petals h x H C hxC
  let q := f p
  let A := Finset.univ.filter (fun a : {a : evenVertices G // (evenSubgraph G).Adj x a} =>
    G.Adj u a.val.val)
  have hpA : p ∈ A := by simp [A,hup]
  have hrA : r ∈ A := by simp [A,hur]
  have hfrA : f r ∈ A := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hdouble (f r).val ((hedge r (f r)).mpr rfl) (f r).property.ne.symm⟩
  have hdisPetals : Disjoint ({p,f p} : Finset _) {r,f r} := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha
    · rw [ha] at hb
      rcases hb with he | he
      · exact hpr he
      · exact hprEdge (((hedge r p).mpr he.symm).symm)
    · rw [ha] at hb
      rcases hb with he | he
      · exact hprEdge ((hedge p r).mpr he)
      · exact hpr (hinv.injective he)
  obtain ⟨B,hBR,_,hchosen,hselected⟩ := indexed_reserved_double_spare_selection
    f hinv R A hindex p r hpA (hfree p) hrA hfrA (hfree r) hdisPetals
  have hqChosen : q ∈ B.biUnion (fun a => {a,f a}) := by
    rw [hchosen]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let Z := (R.filter (fun a => a ∈ A ∨ f a ∈ A)) \ B
  let N := (Z.toList.map (fun a => (a,f a))).map (fun e => (e.1.val.val,e.2.val.val))
  obtain ⟨hdis,hNE,hreach,havoid,hcover⟩ := bare_windmill_three_contact_neutral_coverage
    h x H f R A B hBR hinv hindex hedge p r hqChosen hselected
  let K : Finset V := {p.val.val,r.val.val,(f r).val.val}
  let privates := windmillPrivateSet x Finset.univ
  have hpriv : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2 := by
    intro t ht
    obtain ⟨a,_,hat⟩ := (mem_windmillPrivateSet x _ t).mp ht
    subst t
    exact ⟨a.property.symm,(bare_windmillPrivateSet_leaf_guards h x H Finset.univ
      a.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)).2⟩
  have hNpriv : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates := by
    intro e he
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨a,_,hva⟩ := List.mem_map.mp hv
    subst v
    exact ⟨(mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩,
      (mem_windmillPrivateSet x _ _).mpr ⟨f a,Finset.mem_univ _,rfl⟩⟩
  have hnotH : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ h := by
    intro a
    have hbare := H.counterexample.1.2.2.2.2.2.1
    have ha := even_ended_deletions_avoid_bare_vertex G h hbare
      [((x : V),a.val.val)] (by
        intro e he; simp only [List.mem_singleton] at he; subst e
        exact ⟨a.property,x.property,a.val.property⟩)
    exact (ha ((x : V),a.val.val) (by simp)).2.symm
  have hprV : p.val.val ≠ r.val.val := fun he => hpr ((windmillPrivateEmbedding x).injective he)
  have hKcard : #K = 3 := by
    have hc := (reserved_petal_double_spare_count f A p r hpA (hfree p)
      hrA hfrA (hfree r) hdisPetals).2
    rw [←hchosen] at hc
    rw [hselected] at hc
    have hm := windmillPrivateSet_card x ({p,r,f r} : Finset _)
    have hmap : windmillPrivateSet x ({p,r,f r} : Finset _) = K := by
      simp only [windmillPrivateSet,Finset.map_insert,Finset.map_singleton]
      rfl
    rw [hmap] at hm
    exact hm.trans hc
  have hKlabels : ∀ t ∈ K, ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      t = a.val.val ∧ G.Adj u a.val.val := by
    intro t ht
    rcases Finset.mem_insert.mp ht with he | he
    · exact ⟨p,he,hup⟩
    rcases Finset.mem_insert.mp he with he | he
    · exact ⟨r,he,hur⟩
    · exact ⟨f r,Finset.mem_singleton.mp he,(Finset.mem_filter.mp hfrA).2⟩
  obtain ⟨hxF,htouched,hS⟩ := ordinary_outside_hub_contact_family G x C hxC u h
  have hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∨ (∃ e ∈ ((x : V),q.val.val) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h := by
    intro t hut ht
    rcases bare_windmill_even_contact_partition h x H C hxC u t hut ht with
      htx | hprivate | hth | hord
    · exact Or.inr (Or.inl ⟨((x : V),q.val.val),List.mem_cons_self ..,Or.inl htx⟩)
    · obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x A t).mp hprivate
      rcases hcover a ha with hac | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ hac)
      · exact Or.inr (Or.inl ⟨e,he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr (Or.inr hth))
    · exact Or.inr (Or.inr (Or.inl hord))
  obtain ⟨special,P,mates,_,_,_,_,_,_,_,_,_,D,_,_,hreturn⟩ :=
    bare_delayed_special_native_auxiliary G h u x p.val q.val H C hxC
      S rfl F (by intro D hD; exact hD) htouched hxF 3 (by decide)
      heven hT2 hu K privates hKcard
    (by intro t ht; obtain ⟨a,rfl,_⟩ := hKlabels t ht
        exact ⟨a.val,rfl,a.property.reachable⟩)
    (by intro t ht; obtain ⟨a,rfl,hua⟩ := hKlabels t ht
        exact ⟨hua,a.val.property,hnotH a⟩)
    (by intro t ht; obtain ⟨a,rfl,_⟩ := hKlabels t ht
        exact (mem_windmillPrivateSet x _ _).mpr ⟨a,Finset.mem_univ _,rfl⟩)
    N hdis hreach hNE havoid hNpriv hpriv hcontact p.property
    ((hedge p q).mpr rfl)
    (hpriv p.val.val ((mem_windmillPrivateSet x _ _).mpr ⟨p,Finset.mem_univ _,rfl⟩)).2
    p.property.reachable
    (fun e he => ⟨fun heq => (havoid e (List.mem_cons_of_mem _ he)).1
      (heq ▸ Finset.mem_insert_self _ _),fun heq =>
      (havoid e (List.mem_cons_of_mem _ he)).2 (heq ▸ Finset.mem_insert_self _ _)⟩)
  obtain ⟨E,_,_,_,_,_,_,hfinish⟩ := hreturn (Finset.mem_insert_self _ _)
    (bare_windmill_private_even_neighbors h x H f hedge p)
  have hstrict : 2 < #(K.erase p.val.val) + #F := by
    have hc := Finset.card_erase_add_one
      (Finset.mem_insert_self p.val.val {r.val.val,(f r).val.val})
    change #(K.erase p.val.val) + 1 = #K at hc
    omega
  obtain ⟨_,_,_,_,_,T,hsize,hh⟩ := hfinish hstrict
  exact H.counterexample.2 ⟨T,hsize,hh⟩

end Gallai.TwoException
