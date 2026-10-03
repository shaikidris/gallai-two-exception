/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactUniverse

@[expose] public section

/-! # Selecting contact preparations from indexed petals -/
namespace Gallai.TwoException
open scoped Finset

/-- The representatives of petals with exactly one selected private vertex. -/
def singleContactPetals {N : Type*} [DecidableEq N]
    (f : N → N) (P A : Finset N) : Finset N :=
  P.filter fun r => (r ∈ A ∧ f r ∉ A) ∨ (r ∉ A ∧ f r ∈ A)

/-- The representatives of petals with both private vertices selected. -/
def doubleContactPetals {N : Type*} [DecidableEq N]
    (f : N → N) (P A : Finset N) : Finset N :=
  P.filter fun r => r ∈ A ∧ f r ∈ A

/-- The five preparations include actual petal witnesses. In the final
case the two representatives are distinct, not two names for one petal. -/
def ContactPreparationCases {N : Type*} [DecidableEq N]
    (f : N → N) (P A : Finset N) (eta : Prop) : Prop :=
  (¬eta ∧ Odd #(singleContactPetals f P A) ∧
    (singleContactPetals f P A).Nonempty) ∨
  (¬eta ∧ Even #(singleContactPetals f P A) ∧
    (doubleContactPetals f P A).Nonempty) ∨
  (eta ∧ Even #(singleContactPetals f P A)) ∨
  (eta ∧ Odd #(singleContactPetals f P A) ∧
    (singleContactPetals f P A).Nonempty) ∨
  (¬eta ∧ Even #(singleContactPetals f P A) ∧
    doubleContactPetals f P A = ∅ ∧
    ∃ r ∈ singleContactPetals f P A,
      ∃ s ∈ singleContactPetals f P A, r ≠ s)

/-- Every nonempty indexed contact has a preparation of type E1--E5. -/
theorem indexed_contact_preparation_cases
    {N : Type*} [Fintype N] [DecidableEq N]
    (f : N → N) (hfree : ∀ a, f a ≠ a) (P A : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (eta : Prop) (hcontact : eta ∨ A.Nonempty) :
    ContactPreparationCases f P A eta := by
  classical
  have hcard : #A = #(singleContactPetals f P A) +
      2 * #(doubleContactPetals f P A) :=
    indexed_petal_contact_card f hfree P A hindex
  have hsingle : Odd #(singleContactPetals f P A) →
      (singleContactPetals f P A).Nonempty := by
    intro ho
    apply Finset.card_pos.mp
    obtain ⟨k, hk⟩ := ho
    omega
  unfold ContactPreparationCases
  rcases Nat.even_or_odd #(singleContactPetals f P A) with he | ho
  · by_cases heta : eta
    · exact Or.inr (Or.inr (Or.inl ⟨heta, he⟩))
    · by_cases hd : (doubleContactPetals f P A).Nonempty
      · exact Or.inr (Or.inl ⟨heta, he, hd⟩)
      · have hzero : doubleContactPetals f P A = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hd
        have hpos : 0 < #A := Finset.card_pos.mpr (hcontact.resolve_left heta)
        have htwo : 1 < #(singleContactPetals f P A) := by
          rw [hzero, Finset.card_empty] at hcard
          obtain ⟨k, hk⟩ := he
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨heta, he, hzero, Finset.one_lt_card.mp htwo⟩)))
  · by_cases heta : eta
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨heta, ho, hsingle ho⟩)))
    · exact Or.inl ⟨heta, ho, hsingle ho⟩

/-- Orient a singly contacted petal at its contacted vertex. -/
theorem single_contact_orientation
    {N : Type*} [DecidableEq N] (f : N → N) (hinv : Function.Involutive f)
    (P A : Finset N) (r : N) (hr : r ∈ singleContactPetals f P A) :
    ∃ p, (p = r ∨ p = f r) ∧ p ∈ A ∧ f p ∉ A := by
  rcases (Finset.mem_filter.mp hr).2 with hr | hr
  · exact ⟨r, Or.inl rfl, hr⟩
  · exact ⟨f r, Or.inr rfl, hr.2, by simpa only [hinv r] using hr.1⟩

/-- Distinct representatives index disjoint pairs of private vertices. -/
theorem indexed_petal_pairs_disjoint
    {N : Type*} [DecidableEq N] (f : N → N) (P : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (r s : N) (hr : r ∈ P) (hs : s ∈ P) (hrs : r ≠ s) :
    Disjoint ({r, f r} : Finset N) {s, f s} := by
  apply Finset.disjoint_left.mpr
  intro a har has
  have har' : a = r ∨ a = f r := by simpa using har
  have has' : a = s ∨ a = f s := by simpa using has
  obtain ⟨t, _, huniq⟩ := hindex a
  exact hrs ((huniq r ⟨hr, har'⟩).trans (huniq s ⟨hs, has'⟩).symm)

/-- The E5 pair can be oriented at its two contacts while keeping the
entire petals disjoint. This supplies all cross-petal inequality guards. -/
theorem two_single_contact_petals
    {N : Type*} [DecidableEq N] (f : N → N) (hinv : Function.Involutive f)
    (P A : Finset N)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hpair : ∃ r ∈ singleContactPetals f P A,
      ∃ s ∈ singleContactPetals f P A, r ≠ s) :
    ∃ p q, p ∈ A ∧ f p ∉ A ∧ q ∈ A ∧ f q ∉ A ∧
      Disjoint ({p, f p} : Finset N) {q, f q} := by
  obtain ⟨r, hr, s, hs, hrs⟩ := hpair
  obtain ⟨p, hp, hpA, hfpA⟩ := single_contact_orientation f hinv P A r hr
  obtain ⟨q, hq, hqA, hfqA⟩ := single_contact_orientation f hinv P A s hs
  have hpp : ({p, f p} : Finset N) = {r, f r} := by
    rcases hp with rfl | rfl
    · rfl
    · simp only [hinv r, Finset.pair_comm]
  have hqq : ({q, f q} : Finset N) = {s, f s} := by
    rcases hq with rfl | rfl
    · rfl
    · simp only [hinv s, Finset.pair_comm]
  refine ⟨p, q, hpA, hfpA, hqA, hfqA, ?_⟩
  rw [hpp, hqq]
  exact indexed_petal_pairs_disjoint f P hindex r s
    (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hs).1 hrs

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Native E1--E5 coverage for the contacts of a vertex with the hub's
windmill. No count or petal witness is supplied by the caller. -/
theorem bare_windmill_contact_preparation_cases
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) (u : V)
    (hcontact : G.Adj u x ∨
      ∃ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, G.Adj u a.val.val) :
    let A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
      Finset.univ.filter (fun a => G.Adj u a.val.val)
    ∃ (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
          {a : evenVertices G // (evenSubgraph G).Adj x a})
      (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a}),
      Function.Involutive f ∧ (∀ a, f a ≠ a) ∧
      (∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) ∧
      (∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b) ∧
      ContactPreparationCases f P A (G.Adj u x) := by
  classical
  dsimp only
  obtain ⟨f, P, hinv, hfree, hindex, hedge, _⟩ :=
    bare_windmill_contact_card h x H C hxC u
  refine ⟨f, P, hinv, hfree, hindex, hedge,
    indexed_contact_preparation_cases f hfree P _ hindex _ ?_⟩
  rcases hcontact with hx | ⟨a, ha⟩
  · exact Or.inl hx
  · exact Or.inr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩

/-- Neutralize every touched petal outside the chosen preparation petals.
The concrete mate list is disjoint, avoids all chosen private vertices and
covers every contact not carried by a chosen petal. -/
theorem indexed_neutral_petal_preparation
    {N : Type*} [DecidableEq N] (f : N → N) (P A B : Finset N) (hBP : B ⊆ P)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r)) :
    let chosen := B.biUnion (fun r => ({r,f r} : Finset N))
    let Z := (P.filter (fun r => r ∈ A ∨ f r ∈ A)) \ B
    let M := Z.toList.map (fun r => (r,f r))
    M.Pairwise (fun e g =>
      e.1 ≠ g.1 ∧ e.1 ≠ g.2 ∧ e.2 ≠ g.1 ∧ e.2 ≠ g.2) ∧
    (∀ e ∈ M, e.1 ∉ chosen ∧ e.2 ∉ chosen) ∧
    (∀ a ∈ A, a ∈ chosen ∨ ∃ e ∈ M, a = e.1 ∨ a = e.2) := by
  classical
  dsimp only
  let Z := (P.filter (fun r => r ∈ A ∨ f r ∈ A)) \ B
  have hZP : Z ⊆ P := fun r hr =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).1
  have hZN : ∀ r ∈ Z, r ∉ B := fun r hr => (Finset.mem_sdiff.mp hr).2
  have hdis : ∀ r ∈ Z, ∀ s ∈ P, r ≠ s →
      Disjoint ({r,f r} : Finset N) {s,f s} := by
    intro r hr s hs hne
    exact indexed_petal_pairs_disjoint f P hindex r s (hZP hr) hs hne
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ (List.nodup_iff_pairwise_ne.mp Z.nodup_toList)
    intro r s hr hs hne
    have hd := hdis r (Finset.mem_toList.mp hr) s
      (hZP (Finset.mem_toList.mp hs)) hne
    have hn : ∀ a ∈ ({r,f r} : Finset N), ∀ b ∈ ({s,f s} : Finset N), a ≠ b := by
      intro a ha b hb he
      exact Finset.disjoint_left.mp hd ha (he ▸ hb)
    exact ⟨hn r (by simp) s (by simp),hn r (by simp) (f s) (by simp),
      hn (f r) (by simp) s (by simp),hn (f r) (by simp) (f s) (by simp)⟩
  · intro e he
    obtain ⟨r,hr,heq⟩ := List.mem_map.mp he
    subst e
    have hrZ := Finset.mem_toList.mp hr
    have hav : ∀ a ∈ ({r,f r} : Finset N), a ∉ B.biUnion (fun s => ({s,f s} : Finset N)) := by
      intro a ha hm
      obtain ⟨s,hsB,has⟩ := Finset.mem_biUnion.mp hm
      have hrs : r ≠ s := fun he => hZN r hrZ (he ▸ hsB)
      obtain ⟨t,_,huniq⟩ := hindex a
      have hrI : r ∈ P ∧ (a = r ∨ a = f r) := ⟨hZP hrZ,by simpa using ha⟩
      have hsP : s ∈ P := hBP hsB
      have hsI : s ∈ P ∧ (a = s ∨ a = f s) := ⟨hsP,by simpa using has⟩
      exact hrs ((huniq r hrI).trans (huniq s hsI).symm)
    exact ⟨hav r (by simp),hav (f r) (by simp)⟩
  · intro a ha
    obtain ⟨r,⟨hrP,har⟩,_⟩ := hindex a
    by_cases hrB : r ∈ B
    · left
      exact Finset.mem_biUnion.mpr ⟨r,hrB,by simpa using har⟩
    · right
      have hrA : r ∈ A ∨ f r ∈ A := by
        rcases har with he | he
        · exact Or.inl (he ▸ ha)
        · exact Or.inr (he ▸ ha)
      have hrZ : r ∈ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hrP,hrA⟩,hrB⟩
      exact ⟨(r,f r),List.mem_map.mpr ⟨r,Finset.mem_toList.mpr hrZ,rfl⟩,har⟩

/-- A reserved contact contributes one leaf; a disjoint contact-only spare
selection contributes exactly its cardinality. The unpaid mate is excluded. -/
theorem reserved_petal_spare_contact_count
    {N : Type*} [DecidableEq N] (f : N → N) (A S : Finset N) (p : N)
    (hp : p ∈ A) (hfree : f p ≠ p) (hSA : S ⊆ A)
    (hpS : p ∉ S) (hqS : f p ∉ S) :
    (A ∩ ({p,f p} ∪ S)).erase (f p) = insert p S ∧
      #((A ∩ ({p,f p} ∪ S)).erase (f p)) = 1 + #S := by
  have heq : (A ∩ ({p,f p} ∪ S)).erase (f p) = insert p S := by
    ext a
    by_cases haq : a = f p
    · subst a
      simp [hfree,hqS]
    · by_cases hap : a = p
      · subst a
        simp [hp,hfree.symm]
      · simp only [Finset.mem_erase,Finset.mem_inter,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton,haq,hap,false_or]
        exact ⟨fun ha => ha.2.2,fun ha => ⟨haq,hSA ha,ha⟩⟩
  refine ⟨heq,?_⟩
  rw [heq,Finset.card_insert_of_notMem hpS]
  omega

/-- A spare single petal supplies exactly one further deleted contact. -/
theorem reserved_petal_single_spare_count
    {N : Type*} [DecidableEq N] (f : N → N) (A : Finset N) (p r : N)
    (hp : p ∈ A) (hfp : f p ≠ p) (hr : r ∈ A) (hfr : f r ∉ A)
    (hdis : Disjoint ({p,f p} : Finset N) {r,f r}) :
    (A ∩ ({p,f p} ∪ {r,f r})).erase (f p) = {p,r} ∧
      #((A ∩ ({p,f p} ∪ {r,f r})).erase (f p)) = 2 := by
  have hpR : p ≠ r := fun he =>
    Finset.disjoint_left.mp hdis (Finset.mem_insert_self p {f p})
      (by rw [he]; exact Finset.mem_insert_self r {f r})
  have hqR : f p ≠ r := fun he =>
    Finset.disjoint_left.mp hdis (Finset.mem_insert_of_mem (Finset.mem_singleton_self (f p)))
      (by rw [he]; exact Finset.mem_insert_self r {f r})
  have heq : (A ∩ ({p,f p} ∪ {r,f r})).erase (f p) = {p,r} := by
    ext a
    simp only [Finset.mem_erase,Finset.mem_inter,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hne,ha,(hap | haq) | (har | hafr)⟩
      · exact Or.inl hap
      · exact False.elim (hne haq)
      · exact Or.inr har
      · exact False.elim (hfr (hafr ▸ ha))
    · rintro (rfl | rfl)
      · exact ⟨hfp.symm,hp,Or.inl (Or.inl rfl)⟩
      · exact ⟨hqR.symm,hr,Or.inr (Or.inl rfl)⟩
  refine ⟨heq,?_⟩
  rw [heq,Finset.card_insert_of_notMem (by simpa using hpR),Finset.card_singleton]

/-- Select the actual indexed representatives of a reserved petal and a
disjoint singly contacted spare. Their union has exactly the two pending
contacts after excluding the reserved mate. -/
theorem indexed_reserved_single_spare_selection
    {N : Type*} [DecidableEq N] (f : N → N) (hinv : Function.Involutive f)
    (P A : Finset N)
    (hindex : ∀ a, ∃! t, t ∈ P ∧ (a = t ∨ a = f t))
    (p r : N) (hp : p ∈ A) (hfp : f p ≠ p)
    (hr : r ∈ A) (hfr : f r ∉ A)
    (hdis : Disjoint ({p,f p} : Finset N) {r,f r}) :
    ∃ B : Finset N, B ⊆ P ∧ #B = 2 ∧
      B.biUnion (fun t => ({t,f t} : Finset N)) = {p,f p} ∪ {r,f r} ∧
      (A ∩ B.biUnion (fun t => ({t,f t} : Finset N))).erase (f p) = {p,r} := by
  classical
  obtain ⟨s, ⟨hs, hps⟩, _⟩ := hindex p
  obtain ⟨t, ⟨ht, hrt⟩, _⟩ := hindex r
  have hsp : ({s,f s} : Finset N) = {p,f p} := by
    rcases hps with rfl | rfl
    · rfl
    · simp only [hinv s, Finset.pair_comm]
  have htr : ({t,f t} : Finset N) = {r,f r} := by
    rcases hrt with rfl | rfl
    · rfl
    · simp only [hinv t, Finset.pair_comm]
  have hst : s ≠ t := by
    intro he
    have hsLeft : s ∈ ({p,f p} : Finset N) := by rw [←hsp]; simp
    have hsRight : s ∈ ({r,f r} : Finset N) := by rw [←htr, ←he]; simp
    exact Finset.disjoint_left.mp hdis hsLeft hsRight
  have hchosen : ({s,t} : Finset N).biUnion (fun a => ({a,f a} : Finset N)) =
      {p,f p} ∪ {r,f r} := by
    simp only [Finset.biUnion_insert, Finset.singleton_biUnion, hsp, htr]
  refine ⟨{s,t}, ?_, ?_, hchosen, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hs
    · exact (Finset.mem_singleton.mp ha) ▸ ht
  · rw [Finset.card_insert_of_notMem (by simpa using hst), Finset.card_singleton]
  · rw [hchosen]
    exact (reserved_petal_single_spare_count f A p r hp hfp hr hfr hdis).1

/-- A spare double petal contributes two additional contacts. -/
theorem reserved_petal_double_spare_count
    {N : Type*} [DecidableEq N] (f : N → N) (A : Finset N) (p r : N)
    (hp : p ∈ A) (hfp : f p ≠ p) (hr : r ∈ A) (hfrA : f r ∈ A)
    (hfr : f r ≠ r) (hdis : Disjoint ({p,f p} : Finset N) {r,f r}) :
    (A ∩ ({p,f p} ∪ {r,f r})).erase (f p) = insert p {r,f r} ∧
      #((A ∩ ({p,f p} ∪ {r,f r})).erase (f p)) = 3 := by
  have hpS : p ∉ ({r,f r} : Finset N) :=
    fun hm => Finset.disjoint_left.mp hdis (by simp) hm
  have hqS : f p ∉ ({r,f r} : Finset N) :=
    fun hm => Finset.disjoint_left.mp hdis (by simp) hm
  have hSA : ({r,f r} : Finset N) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with he | he
    · exact he ▸ hr
    · exact he ▸ hfrA
  obtain ⟨heq,hcard⟩ := reserved_petal_spare_contact_count f A {r,f r} p
    hp hfp hSA hpS hqS
  refine ⟨heq,?_⟩
  have hc : #({r,f r} : Finset N) = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hfr.symm),Finset.card_singleton]
  omega

/-- Select the indexed representatives of a reserved petal and a disjoint
+double-contact spare, retaining exactly three pending contacts. -/
theorem indexed_reserved_double_spare_selection
    {N : Type*} [DecidableEq N] (f : N → N) (hinv : Function.Involutive f)
    (P A : Finset N)
    (hindex : ∀ a, ∃! t, t ∈ P ∧ (a = t ∨ a = f t))
    (p r : N) (hp : p ∈ A) (hfp : f p ≠ p)
    (hr : r ∈ A) (hfrA : f r ∈ A) (hfr : f r ≠ r)
    (hdis : Disjoint ({p,f p} : Finset N) {r,f r}) :
    ∃ B : Finset N, B ⊆ P ∧ #B = 2 ∧
      B.biUnion (fun t => ({t,f t} : Finset N)) = {p,f p} ∪ {r,f r} ∧
      (A ∩ B.biUnion (fun t => ({t,f t} : Finset N))).erase (f p) = insert p {r,f r} := by
  classical
  obtain ⟨s, ⟨hs, hps⟩, _⟩ := hindex p
  obtain ⟨t, ⟨ht, hrt⟩, _⟩ := hindex r
  have hsp : ({s,f s} : Finset N) = {p,f p} := by
    rcases hps with rfl | rfl
    · rfl
    · simp only [hinv s, Finset.pair_comm]
  have htr : ({t,f t} : Finset N) = {r,f r} := by
    rcases hrt with rfl | rfl
    · rfl
    · simp only [hinv t, Finset.pair_comm]
  have hst : s ≠ t := by
    intro he
    have hsLeft : s ∈ ({p,f p} : Finset N) := by rw [←hsp]; simp
    have hsRight : s ∈ ({r,f r} : Finset N) := by rw [←htr, ←he]; simp
    exact Finset.disjoint_left.mp hdis hsLeft hsRight
  have hchosen : ({s,t} : Finset N).biUnion (fun a => ({a,f a} : Finset N)) =
      {p,f p} ∪ {r,f r} := by
    simp only [Finset.biUnion_insert, Finset.singleton_biUnion, hsp, htr]
  refine ⟨{s,t}, ?_, ?_, hchosen, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hs
    · exact (Finset.mem_singleton.mp ha) ▸ ht
  · rw [Finset.card_insert_of_notMem (by simpa using hst), Finset.card_singleton]
  · rw [hchosen]
    exact (reserved_petal_double_spare_count f A p r hp hfp hr hfrA hfr hdis).1

end Gallai.TwoException
