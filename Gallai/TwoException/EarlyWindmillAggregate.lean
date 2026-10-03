/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyWindmillGain
public import Gallai.TwoException.OrdinaryContributionSum
public import Gallai.TwoException.PacketGainStarRestoration
public import Gallai.TwoException.EarlyPrefixRestoration
public import Gallai.TwoException.OrdinaryPendingBound
public import Gallai.TwoException.EarlyContactPartition

@[expose] public section

/-! # Native double-petal contributions summed in early payment -/
namespace Gallai.TwoException
open scoped BigOperators Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
noncomputable local instance (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Disjoint double-petal packets have nonnegative total contribution.
Each local gain is derived from the actual windmill and tight half-star;
the caller supplies only representative and carrier preparation data. -/
theorem bare_early_double_family_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (F : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hdis : (F : Set {a : evenVertices G // (evenSubgraph G).Adj x a}).PairwiseDisjoint
      (fun p => ({p.val.val,(f p).val.val} : Finset V)))
    (D : Decomposition J) (u : V) (S A : Finset V)
    (hcontacts : ∀ p ∈ F, p.val.val ∈ S ∧ p.val.val ≠ u ∧
      ¬ J.Adj p.val.val u ∧ 0 < D.endpointCount (f p).val.val)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #(F.biUnion (fun p => ({p.val.val,(f p).val.val} : Finset V)) \ A) ≤
      #(F.biUnion (fun p => ({p.val.val,(f p).val.val} : Finset V)) ∩ A) := by
  classical
  let packet := fun p : {a : evenVertices G // (evenSubgraph G).Adj x a} =>
    ({p.val.val,(f p).val.val} : Finset V)
  have hc := ordinary_disjoint_packet_counts F packet A hdis
  have hg := ordinary_contact_gain_of_packet_counts F F (F.biUnion packet) A packet
    hc.1 hc.2 (fun p hp hn => (hn hp).elim) (by
      intro p hp _
      obtain ⟨hpS,hpu,hmissing,hq⟩ := hcontacts p hp
      exact bare_early_double_petal_gain h x H f hedge p D u S A hpS hpu
        hmissing hq E hsub hprofile hvec htight)
  dsimp only [packet] at hg
  omega

/-- Exact disjoint contact accounting rules out the one-surplus failure
when the centre and packet gains exceed its permitted loss. No truncated
selected-minus-pending subtraction is used. -/
theorem early_partition_tight_profile_false
    (K L A : Finset V) (d delta N epsilon : ℕ)
    (hdis : Disjoint K L) (hAS : A ⊆ K ∪ L)
    (hbalance : d + #A = #((K ∪ L) \ A) + 1)
    (hwindmill : #(K \ A) + delta ≤ #(K ∩ A))
    (hordinary : #(L \ A) + N ≤ #(L ∩ A) + epsilon)
    (hstrict : epsilon + 1 < d + delta + N) : False := by
  have hsel : #A = #(K ∩ A) + #(L ∩ A) := by
    have he : A = (K ∩ A) ∪ (L ∩ A) := by
      ext t
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro ht
        rcases Finset.mem_union.mp (hAS ht) with hk | hl
        · exact Or.inl ⟨hk, ht⟩
        · exact Or.inr ⟨hl, ht⟩
      · rintro (⟨_, ht⟩ | ⟨_, ht⟩) <;> exact ht
    exact (congrArg Finset.card he).trans (Finset.card_union_of_disjoint
      (hdis.mono Finset.inter_subset_left Finset.inter_subset_left))
  have hpend : #((K ∪ L) \ A) = #(K \ A) + #(L \ A) := by
    rw [Finset.union_sdiff_distrib, Finset.card_union_of_disjoint
      (hdis.mono Finset.sdiff_subset Finset.sdiff_subset)]
  omega

/-- The combined early gains complete the actual contact star without
adding paths and preserve all endpoint counts outside the contact star. -/
theorem restore_early_star_of_partition_gains
    (D : Decomposition J) (u b : V) (K L : Finset V) (delta N epsilon : ℕ)
    (hdis : Disjoint K L) (hu : u ∉ K ∪ L) (hb : b ∈ K ∪ L)
    (hround : 0 < D.endpointCount u ∨ Odd #(K ∪ L))
    (hstrict : epsilon + 1 < D.endpointCount u + delta + N)
    (hmissing : ∀ t ∈ K ∪ L, ¬ J.Adj u t)
    (hpositive : ∀ t, J.Adj u t ∨ t ∈ K ∪ L → 0 < D.endpointCount t)
    (hpassing : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      ∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t ≤ 2)
    (hgains : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      (∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t = 2) →
      #(K \ A) + delta ≤ #(K ∩ A) ∧
        #(L \ A) + N ≤ #(L ∩ A) + epsilon) :
    ∃ F : Decomposition (J ⊔ (K ∪ L).sup (SimpleGraph.edge u)),
      F.size = D.size ∧ 0 < F.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → F.endpointCount t = D.endpointCount t := by
  classical
  obtain ⟨A, hAS, hbA, hhalf, E, hs, hvec⟩ :=
    D.prescribed_half_star_addibility u (K ∪ L) hu hmissing hpositive b hb
  have huA : u ∉ A := fun ht => hu (hAS ht)
  have hEu : E.endpointCount u = D.endpointCount u + #A := by
    simpa only [huA, ite_false, ite_true, Nat.add_zero] using hvec u
  have hpart := Finset.card_sdiff_add_card_eq_card hAS
  have hreserve : #((K ∪ L) \ A) + 1 ≤ E.endpointCount u := by
    rcases hround with hp | ho
    · omega
    · rw [Nat.odd_iff] at ho
      omega
  have huR : u ∉ (K ∪ L) \ A := fun ht => hu (Finset.mem_sdiff.mp ht).1
  have hmiss : ∀ t ∈ (K ∪ L) \ A,
      ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj u t := by
    intro t ht ha
    rcases ha with ha | ha
    · exact hmissing t (Finset.mem_sdiff.mp ht).1 ha
    · exact (Finset.mem_sdiff.mp ht).2 ((star_sup_adj_center u A huA t).mp ha)
  have hcomplete : ∃ F : Decomposition ((J ⊔ A.sup (SimpleGraph.edge u)) ⊔
      ((K ∪ L) \ A).sup (SimpleGraph.edge u)), F.size = E.size ∧
      ∀ t, F.endpointCount t + (if u = t then #((K ∪ L) \ A) else 0) =
        E.endpointCount t + if t ∈ (K ∪ L) \ A then 1 else 0 := by
    by_contra hf
    obtain ⟨he, htight⟩ := star_surplus_failure_profile E u ((K ∪ L) \ A)
      huR hmiss (hpassing A hAS hbA E hvec) hreserve hf
    obtain ⟨hk, hl⟩ := hgains A hAS hbA E hvec htight
    exact early_partition_tight_profile_false K L A (D.endpointCount u)
      delta N epsilon hdis hAS (by omega) hk hl hstrict
  obtain ⟨F, hfs, hfv⟩ := hcomplete
  have hgraph : (J ⊔ A.sup (SimpleGraph.edge u)) ⊔
      ((K ∪ L) \ A).sup (SimpleGraph.edge u) =
      J ⊔ (K ∪ L).sup (SimpleGraph.edge u) := by
    rw [sup_assoc, ← Finset.sup_union, Finset.union_sdiff_of_subset hAS]
  have hout : ∃ F : Decomposition ((J ⊔ A.sup (SimpleGraph.edge u)) ⊔
      ((K ∪ L) \ A).sup (SimpleGraph.edge u)), F.size = D.size ∧
      0 < F.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → F.endpointCount t = D.endpointCount t := by
    refine ⟨F, hfs.trans hs, ?_, ?_⟩
    · have hv := hfv u
      simp only [huR, ite_true, ite_false, Nat.add_zero] at hv
      omega
    · intro t htu htS
      have htA : t ∉ A := fun ht => htS (hAS ht)
      have htR : t ∉ (K ∪ L) \ A := fun ht => htS (Finset.mem_sdiff.mp ht).1
      have he := hvec t
      have hf := hfv t
      simp only [htA, htR, htu.symm, ite_false, Nat.add_zero] at he hf
      exact hf.trans he
  rwa [hgraph] at hout

noncomputable local instance (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The early prepared star lifts back to the original graph. Retained
contact coverage derives Fan positivity, and original leaf caps derive
every pending passing-neighbour bound on the actual intermediate graph.
Only the branch-specific packet gains and strict excess remain inputs. -/
theorem restore_actual_early_star_of_partition_gains
    (u h b : V) (K L : Finset V) (O : List (V × V)) (delta N epsilon : ℕ)
    (hdis : Disjoint K L) (hb : b ∈ K ∪ L)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hcap : ∀ t ∈ K ∪ L, eDegree G t ≤ 2)
    (hcover : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ t = h ∨ ∃ e ∈ O, t = e.1)
    (D : Decomposition (starPuncture G u (K ∪ L)))
    (hh : 0 < D.endpointCount h)
    (hrec : ∀ e ∈ O, 2 ≤ D.endpointCount e.1)
    (hround : 0 < D.endpointCount u ∨ Odd #(K ∪ L))
    (hstrict : epsilon + 1 < D.endpointCount u + delta + N)
    (hgains : ∀ A : Finset V, A ⊆ K ∪ L → b ∈ A →
      ∀ E : Decomposition ((starPuncture G u (K ∪ L)) ⊔ A.sup (SimpleGraph.edge u)),
      (∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
        D.endpointCount t + if u = t then #A else 0) →
      (∀ t ∈ (K ∪ L) \ A, passingNeighborCount E t = 2) →
      #(K \ A) + delta ≤ #(K ∩ A) ∧
        #(L \ A) + N ≤ #(L ∩ A) + epsilon) :
    ∃ F : Decomposition G, F.size = D.size ∧ 0 < F.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → F.endpointCount t = D.endpointCount t := by
  classical
  have hu : u ∉ K ∪ L := fun ht => G.irrefl (hadj u ht)
  have hpositive := early_prefix_full_neighbourhood_positive u h (K ∪ L) O
    hadj hleaves hcover D hh hrec
  have hout := restore_early_star_of_partition_gains D u b K L delta N epsilon
    hdis hu hb hround hstrict
    (fun t ht => starPuncture_missing G u (K ∪ L) hu t ht)
    hpositive (fun A hA _ E _ =>
      actual_contact_half_star_pending_le_two u (K ∪ L) A hA hadj hleaves hcap E)
    hgains
  rwa [starPuncture_restore G u (K ∪ L) hadj] at hout

/-- On the literal early star puncture, double-petal gain has no auxiliary
subgraph, parity-profile or missing-edge assumptions. These follow from
the actual partial star restoration. -/
theorem bare_actual_early_double_family_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (F : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hdis : (F : Set {a : evenVertices G // (evenSubgraph G).Adj x a}).PairwiseDisjoint
      (fun p => ({p.val.val,(f p).val.val} : Finset V)))
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (D : Decomposition (starPuncture G u B))
    (hcontacts : ∀ p ∈ F, p.val.val ∈ B ∧ 0 < D.endpointCount (f p).val.val)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #(F.biUnion (fun p => ({p.val.val,(f p).val.val} : Finset V)) \ A) ≤
      #(F.biUnion (fun p => ({p.val.val,(f p).val.val} : Finset V)) ∩ A) := by
  classical
  have hu : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hsub : starPuncture G u B ⊔ A.sup (SimpleGraph.edge u) ≤ G := by
    intro a b hab
    rw [ordinary_half_star_graph u B A hAB hadj] at hab
    exact hab.1
  apply bare_early_double_family_gain h x H f hedge F hdis D u B A
  · intro p hp
    obtain ⟨hpB,hq⟩ := hcontacts p hp
    exact ⟨hpB,fun he => hu (he ▸ hpB),
      fun ha => starPuncture_missing G u B hu p.val.val hpB ha.symm,hq⟩
  · exact hsub
  · exact ordinary_half_star_even_preserved u B A hAB hadj hleaves
  · exact hvec
  · exact htight

/-- All indexed double-contact petals contribute nonnegative gain on the
actual half-star. Their disjointness is derived from the unique petal index,
and representative membership comes from the contact filter. -/
theorem bare_indexed_early_double_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hCB : ∀ p ∈ C, p.val.val ∈ B)
    (D : Decomposition (starPuncture G u B))
    (hmates : ∀ p ∈ C, 0 < D.endpointCount p.val.val)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #((doubleContactPetals f P C).biUnion
        (fun p => ({p.val.val,(f p).val.val} : Finset V)) \ A) ≤
      #((doubleContactPetals f P C).biUnion
        (fun p => ({p.val.val,(f p).val.val} : Finset V)) ∩ A) := by
  refine bare_actual_early_double_family_gain h x H f hedge
    (doubleContactPetals f P C)
    (indexed_windmill_ambient_pairs_disjoint x f P (doubleContactPetals f P C)
      hindex (Finset.filter_subset _ _)) u B A hAB hadj hleaves D ?_ E hvec htight
  intro p hp
  have hc := (Finset.mem_filter.mp hp).2
  exact ⟨hCB p hc.1,hmates (f p) hc.2⟩

/-- The sole-single early branch has a positive gain on its entire
windmill contact set. Local double and single gains, exact ambient
coverage and disjointness are all derived inside this proof. -/
theorem bare_actual_early_sole_single_windmill_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpC : p ∈ C) (hfpC : f p ∉ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p)
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hCB : ∀ r ∈ C, r.val.val ∈ B) (hfpB : (f p).val.val ∉ B)
    (D : Decomposition (starPuncture G u B))
    (hmates : ∀ r ∈ C, 0 < D.endpointCount r.val.val)
    (hq : 2 ≤ D.endpointCount (f p).val.val)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2) :
    #(windmillPrivateSet x C \ A) + 1 ≤ #(windmillPrivateSet x C ∩ A) := by
  classical
  have hu : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hsub : starPuncture G u B ⊔ A.sup (SimpleGraph.edge u) ≤ G := by
    intro a b hab
    rw [ordinary_half_star_graph u B A hAB hadj] at hab
    exact hab.1
  have hdouble := bare_indexed_early_double_gain h x H f hedge P C hindex
    u B A hAB hadj hleaves hCB D hmates E hvec htight
  have hsingleGain := bare_early_single_petal_gain h x H f hedge p D u B A hAB
    (hCB p hpC) (fun he => hu (he ▸ hCB p hpC)) hfpB
    (fun ha => starPuncture_missing G u B hu p.val.val (hCB p hpC) ha.symm)
    hq E hsub (ordinary_half_star_even_preserved u B A hAB hadj hleaves)
    hvec htight
  have hpA : p.val.val ∈ A := by
    by_contra hn
    simp [hn] at hsingleGain
  have hpD : p.val.val ∉ (doubleContactPetals f P C).biUnion
      (fun r => ({r.val.val,(f r).val.val} : Finset V)) := by
    rw [← windmillPrivateSet_pair_union]
    intro hp
    obtain ⟨a,ha,he⟩ := (mem_windmillPrivateSet x _ p.val.val).mp hp
    have hap : a = p := Subtype.ext (Subtype.ext he)
    exact single_contact_avoids_double_union f hinv P C p hfpC (hap ▸ ha)
  rw [ambient_early_sole_single_partition x f P C hindex p hpC hsingle]
  exact early_sole_single_union_gain _ A p.val.val hpD hpA hdouble

end Gallai.TwoException
