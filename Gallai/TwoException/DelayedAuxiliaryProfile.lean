/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryStarMateProfile
public import Gallai.TwoException.ContactPunctureWitness
public import Gallai.TwoException.OrdinaryStarMateBoundary
public import Gallai.TwoException.OrdinaryStarMateCap
public import Gallai.TwoException.OrdinaryStarMateBudget
public import Gallai.TwoException.OrdinarySpecialPacket
public import Gallai.TwoException.ComponentWitnessAssembly
public import Gallai.TwoException.OrdinarySequentialRestoration
public import Gallai.TwoException.ContactSpoke

@[expose] public section

/-! # Actual delayed-payment puncture with disjoint mate preparations -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance delayedAuxiliaryAdj (u x q : V)
    (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The delayed auxiliary deletes an even contact star, the unpaid hub
spoke, and disjoint neutralizing mates. It introduces no even vertex and
keeps the contact centre, hub and spoke private odd. -/
theorem delayed_auxiliary_profile
    (u x q : V) (B : Finset V) (M : List (V × V))
    (huB : u ∉ B) (hadj : ∀ t ∈ B, G.Adj u t)
    (huOdd : Odd (G.degree u)) (hB : Even #B)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxu : x ≠ u) (hqu : q ≠ u) (hxB : x ∉ B) (hqB : q ∉ B)
    (hxq : G.Adj x q) (hxEven : Even (G.degree x)) (hqEven : Even (G.degree q))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2)) :
    let K := (starPuncture G u B).deleteEdges {s(x,q)}
    let J := ordinaryMatePuncture K M
    (∀ t, Even (J.degree t) → Even (G.degree t)) ∧
      Odd (J.degree u) ∧ Odd (J.degree x) ∧ Odd (J.degree q) := by
  classical
  let Q := starPuncture G u B
  let K := Q.deleteEdges {s(x,q)}
  let J := ordinaryMatePuncture K M
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  change (∀ t, Even (J.degree t) → Even (G.degree t)) ∧
    Odd (J.degree u) ∧ Odd (J.degree x) ∧ Odd (J.degree q)
  have hp := contact_spoke_puncture_profile u x q B huB hadj huOdd hB
    hleaves hxu hqu hxB hqB hxq hxEven hqEven
  have hm : ∀ e ∈ M, K.Adj e.1 e.2 ∧
      Even (K.degree e.1) ∧ Even (K.degree e.2) := by
    intro e he
    obtain ⟨heu,hevu,heB,hevB,hex,hevx,heq,hevq⟩ := havoid e he
    obtain ⟨ha,hpe,hqe⟩ := hedges e he
    have hQ : Q.Adj e.1 e.2 := by
      exact ⟨ha, fun ht => hevu ((star_sup_adj_off_center u B e.1 e.2 heu).mp ht).2⟩
    refine ⟨?_,?_,?_⟩
    · change Q.Adj e.1 e.2 ∧ _
      refine ⟨hQ,?_⟩
      simp
      rintro (he | he)
      · exact False.elim (hex (congrArg Prod.fst he))
      · exact False.elim (heq (congrArg Prod.fst he))
    · have hs := starPuncture_degree_other (G := G) u B e.1 heu heB
      have hd := degree_delete_edge_of_ne Q x q e.1 hex heq
      simp only [← SimpleGraph.ncard_neighborSet] at hs hd hpe ⊢
      exact (hd.trans hs) ▸ hpe
    · have hs := starPuncture_degree_other (G := G) u B e.2 hevu hevB
      have hd := degree_delete_edge_of_ne Q x q e.2 hevx hevq
      simp only [← SimpleGraph.ncard_neighborSet] at hs hd hqe ⊢
      exact (hd.trans hs) ▸ hqe
  have huK : Odd (K.degree u) := by
    have hs := starPuncture_degree_center (G := G) u B huB
      (fun t ht => (G.mem_neighborFinset u t).mpr (hadj t ht))
    have hd := degree_delete_edge_of_ne Q x q u hxu.symm hqu.symm
    change Q.degree u + #B = G.degree u at hs
    simp only [← SimpleGraph.ncard_neighborSet] at hs hd huOdd ⊢
    rw [hd]
    rw [Nat.odd_iff] at huOdd ⊢
    rw [Nat.even_iff] at hB
    omega
  have hdu := ordinaryMatePuncture_degree_of_avoids (G := K) M u
    (fun e he => ⟨(havoid e he).1.symm,(havoid e he).2.1.symm⟩)
  have hdx := ordinaryMatePuncture_degree_of_avoids (G := K) M x
    (fun e he => ⟨(havoid e he).2.2.2.2.1.symm,(havoid e he).2.2.2.2.2.1.symm⟩)
  have hdq := ordinaryMatePuncture_degree_of_avoids (G := K) M q
    (fun e he => ⟨(havoid e he).2.2.2.2.2.2.1.symm,(havoid e he).2.2.2.2.2.2.2.symm⟩)
  simp only [← SimpleGraph.ncard_neighborSet] at hdu hdx hdq
  change (J.neighborSet u).ncard = (K.neighborSet u).ncard at hdu
  change (J.neighborSet x).ncard = (K.neighborSet x).ncard at hdx
  change (J.neighborSet q).ncard = (K.neighborSet q).ncard at hdq
  refine ⟨fun t ht => hp.1 t
    (ordinaryMatePuncture_even_preserved (G := K) M hdis hm t ht),?_,?_,?_⟩
  · simp only [← SimpleGraph.ncard_neighborSet] at huK ⊢
    rwa [hdu]
  · have ho : Odd (K.degree x) := hp.2.1
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rwa [hdx]
  · have ho : Odd (K.degree q) := hp.2.2
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rwa [hdq]

/-- Bare minimality controls every even vertex of an even-preserving
subgraph once its only non-bare exceptional hub has become odd. -/
theorem bare_odd_hub_subgraph_cap
    (h x : V) (H : BareMinimalCounterexample G h x)
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hsub : J ≤ G) (hkeep : ∀ t, Even (J.degree t) → Even (G.degree t))
    (hxOdd : Odd (J.degree x)) :
    ∀ t, Even (J.degree t) → eDegree J t ≤ 3 := by
  rcases H.counterexample.1 with ⟨_,_,_,_,_,hhzero,hcap⟩
  have hmono := eDegree_le_of_subgraph_of_even_preservation hsub hkeep
  intro t ht
  have htx : t ≠ x := by
    intro he
    subst t
    exact (Nat.not_even_iff_odd.mpr hxOdd) ht
  by_cases hth : t = h
  · subst t
    have hm := hmono h
    rw [hhzero] at hm
    omega
  · exact (hmono t).trans (hcap t (hkeep t ht) hth htx)

/-- The protected bare vertex loses no edge in the actual delayed
auxiliary when excluded from the contact star, spoke and mate packets. -/
theorem delayed_auxiliary_protected_degree
    (u x q h : V) (B : Finset V) (M : List (V × V))
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ x) (hhq : h ≠ q)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree h =
      G.degree h := by
  classical
  have hm := ordinaryMatePuncture_degree_of_avoids
    (G := (starPuncture G u B).deleteEdges {s(x,q)}) M h hhM
  have hd := degree_delete_edge_of_ne (starPuncture G u B) x q h hhx hhq
  have hs := starPuncture_degree_other (G := G) u B h hhu hhB
  simp only [← SimpleGraph.ncard_neighborSet] at hm hd hs ⊢
  exact hm.trans (hd.trans hs)

/-- Every component of the concrete delayed puncture meets the contact
centre, a deleted star leaf, an unpaid-spoke endpoint or a neutralized mate.
Thus a component witness audit need only cover these actual boundary types. -/
theorem delayed_auxiliary_component_meets_boundary
    (hconn : G.Connected) (u x q : V) (B : Finset V) (M : List (V × V))
    (K : (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).ConnectedComponent) :
    ∃ t ∈ K.supp, t = u ∨ t ∈ B ∨ t = x ∨ t = q ∨
      ∃ e ∈ M, t = e.1 ∨ t = e.2 := by
  classical
  by_contra hnone
  have havoid : ∀ t ∈ K.supp,
      t ≠ u ∧ t ∉ B ∧ t ≠ x ∧ t ≠ q ∧
        ∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2 := by
    intro t ht
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact fun he => hnone ⟨t,ht,Or.inl he⟩
    · exact fun hb => hnone ⟨t,ht,Or.inr (Or.inl hb)⟩
    · exact fun he => hnone ⟨t,ht,Or.inr (Or.inr (Or.inl he))⟩
    · exact fun he => hnone ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inl he)))⟩
    · intro e he
      exact ⟨fun hl => hnone ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e,he,Or.inl hl⟩)))⟩,
        fun hr => hnone ⟨t,ht,Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e,he,Or.inr hr⟩)))⟩⟩
  have hclosed : ∀ r s, r ∈ K.supp → G.Adj r s → s ∈ K.supp := by
    intro r s hr hrs
    obtain ⟨hru,hrB,hrx,hrq,hrM⟩ := havoid r hr
    have hstar : (starPuncture G u B).Adj r s := by
      refine ⟨hrs,?_⟩
      intro hs
      exact hrB ((star_sup_adj_off_center u B r s hru).mp hs).1
    have hspoke : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj r s := by
      simp only [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
      exact ⟨hstar,by simp [hrx,hrq]⟩
    have hJ := (ordinaryMatePuncture_adj_of_avoids
      (G := (starPuncture G u B).deleteEdges {s(x,q)}) M r s hrM).mpr hspoke
    exact K.mem_supp_of_adj_mem_supp hr hJ
  obtain ⟨w,hw⟩ := K.nonempty_supp
  have hreach : G.Reachable w u := hconn w u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj w v →
      w ∈ K.supp → v ∈ K.supp := by
    intro v hv hw
    induction hv with
    | refl => exact hw
    | tail _ hab ih => exact hclosed _ _ ih hab
  exact (havoid u (hpreserve hreach hw)).1 rfl

/-- The chosen spoke petal stays connected through its retained hub spoke
and mate edge. Its private supplies the floor for any auxiliary component
meeting either unpaid-spoke endpoint, including when q is separated from x
by the deletion of xq itself. -/
theorem delayed_spoke_petal_component_floor
    (u x p q : V) (B : Finset V) (M : List (V × V))
    (hxu : x ≠ u) (hpu : p ≠ u) (hqu : q ≠ u)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpqne : p ≠ q)
    (hxEven : Even (G.degree x)) (hpdegree : eDegree G p = 2)
    (hM : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2 ∧
      p ≠ e.1 ∧ p ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t)) →
    Odd (J.degree x) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent, x ∈ K.supp ∨ q ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  intro hkeep hxOdd hcap K hK
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hxpQ : (starPuncture G u B).Adj x p := by
    exact ⟨hxp,fun ha => hpu ((star_sup_adj_off_center u B x p hxu).mp ha).2⟩
  have hpqQ : (starPuncture G u B).Adj p q := by
    exact ⟨hpq,fun ha => hqu ((star_sup_adj_off_center u B p q hpu).mp ha).2⟩
  have hxpD : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj x p := by
    simp only [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    exact ⟨hxpQ,by simp [hpqne,hxp.ne.symm]⟩
  have hpqD : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj p q := by
    simp only [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    exact ⟨hpqQ,by simp [hxp.ne.symm,hpqne]⟩
  have hxpJ : J.Adj x p := (ordinaryMatePuncture_adj_of_avoids
    (G := (starPuncture G u B).deleteEdges {s(x,q)}) M x p
    (fun e he => ⟨(hM e he).1,(hM e he).2.1⟩)).mpr hxpD
  have hpqJ : J.Adj p q := (ordinaryMatePuncture_adj_of_avoids
    (G := (starPuncture G u B).deleteEdges {s(x,q)}) M p q
    (fun e he => ⟨(hM e he).2.2.1,(hM e he).2.2.2.1⟩)).mpr hpqD
  have hpK : p ∈ K.supp := by
    rcases hK with hxK | hqK
    · exact K.mem_supp_of_adj_mem_supp hxK hxpJ
    · exact K.mem_supp_of_adj_mem_supp hqK hpqJ.symm
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ha => ha.1.1)
  exact contact_private_component_floor_without_parity hsub hkeep hcap K x p
    hpK hxEven hxOdd hxp.symm hpdegree

/-- View the unpaid spoke as one additional neutralizing mate and reuse
the ordinary contact-coverage count. The exact graph identity is proved by
commuting its deletion past all other mates. -/
theorem delayed_auxiliary_centre_eDegree_le_one
    (h u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : ((x,q) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ (x,q) :: M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ (x,q) :: M, t = e.1 ∨ t = e.2) ∨ t = h) :
    eDegree (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M) u ≤ 1 := by
  classical
  letI : DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
  have hc := ordinary_star_mates_centre_eDegree_le_one h u B ((x,q) :: M)
    hadj hleaves hdis havoid hedges hcontacts
  have hg := ordinaryMatePuncture_deleteEdges_comm (G := starPuncture G u B)
    M ({s(x,q)} : Set (Sym2 V))
  simpa only [ordinaryMatePuncture,← hg] using hc

/-- A special ordinary triangle retains its third-vertex witness in the
delayed puncture. The unpaid spoke is handled as a separated extra mate. -/
theorem delayed_special_packet_component_floor
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : ((x,q) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ (x,q) :: M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hs : C.supp = {a,b,c}) (ha : (a : V) ∈ B) (hb : (b : V) ∈ B)
    (hac : G.Adj a c) (hbc : G.Adj b c)
    (hau : (a : V) ≠ u) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hcAvoid : ∀ e ∈ (x,q) :: M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2)
    (hcNonadj : ¬ G.Adj c u)
    (hcap : ∀ t, Even ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) →
      eDegree (ordinaryMatePuncture
        ((starPuncture G u B).deleteEdges {s(x,q)}) M) t ≤ 3)
    (K : (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).ConnectedComponent)
    (hcontact : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp) :
    HasPathBudget ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).induce K.supp)
      (Fintype.card K.supp / 2) := by
  classical
  letI : DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
  have hg : ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M =
      ordinaryMatePuncture (starPuncture G u B) ((x,q) :: M) :=
    ordinaryMatePuncture_deleteEdges_comm (G := starPuncture G u B) M {s(x,q)}
  have hl := ordinary_star_mates_leaves_odd u B ((x,q) :: M) hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have hodd : ∀ t ∈ B, Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) := by
    intro t ht
    have ho := hl t ht
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rw [hg]
    exact ho
  have hp := ordinary_star_mates_even_preserved u B ((x,q) :: M)
    hadj hleaves hdis havoid hedges
  have hprofile : ∀ t, Even ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) →
      Even (G.degree t) ∨ t = u := by
    intro t ht
    apply hp t
    simp only [← SimpleGraph.ncard_neighborSet] at ht ⊢
    rw [← hg]
    exact ht
  have hsub : ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M ≤ G :=
    (ordinaryMatePuncture_le M).trans (fun _ _ h => h.1.1)
  have hretain : ∀ t, G.Adj c t → t ≠ u →
      (ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj c t := by
    intro t hct htu
    have hv := hcAvoid (x,q) (List.mem_cons_self ..)
    have hstar : (starPuncture G u B).Adj c t :=
      ⟨hct,fun h => htu ((star_sup_adj_off_center u B c t hcu).mp h).2⟩
    have hdel : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj c t := by
      simp only [SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
      exact ⟨hstar,by simp [hv.1,hv.2]⟩
    exact (ordinaryMatePuncture_adj_of_avoids
      (G := (starPuncture G u B).deleteEdges {s(x,q)}) M c t
      (fun e he => hcAvoid e (List.mem_cons_of_mem (x,q) he))).mpr hdel
  have hcK : (c : V) ∈ K.supp := by
    rcases hcontact with haK | hbK | hcK
    · exact K.mem_supp_of_adj_mem_supp haK (hretain a hac.symm hau).symm
    · exact K.mem_supp_of_adj_mem_supp hbK (hretain b hbc.symm hbu).symm
    · exact hcK
  exact ordinary_special_triangle_component_floor C a b c hs u hsub hprofile
    (hodd a ha) (hodd b hb) (fun ht => hcNonadj (hsub ht)) hcap K hcK

/-- A fully neutralized ordinary component supplies a floor budget in the
actual delayed auxiliary: every original even vertex in it becomes odd. -/
theorem delayed_regular_packet_component_floor
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : ((x,q) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ (x,q) :: M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (C : (evenSubgraph G).ConnectedComponent) (p : evenVertices G)
    (hpC : p ∈ C.supp)
    (hcovered : ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ (x,q) :: M, (t : V) = e.1 ∨ (t : V) = e.2)
    (hcap : ∀ t, Even ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) →
      eDegree (ordinaryMatePuncture
        ((starPuncture G u B).deleteEdges {s(x,q)}) M) t ≤ 3)
    (K : (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).ConnectedComponent)
    (hpK : (p : V) ∈ K.supp) :
    HasPathBudget ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).induce K.supp)
      (Fintype.card K.supp / 2) := by
  classical
  letI : DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
  have hg : ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M =
      ordinaryMatePuncture (starPuncture G u B) ((x,q) :: M) :=
    ordinaryMatePuncture_deleteEdges_comm (G := starPuncture G u B) M {s(x,q)}
  have hl := ordinary_star_mates_leaves_odd u B ((x,q) :: M) hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have he := ordinary_star_mates_endpoints_odd u B ((x,q) :: M) hdis havoid hedges
  have hp := ordinary_star_mates_even_preserved u B ((x,q) :: M)
    hadj hleaves hdis havoid hedges
  have hprofile : ∀ t, Even ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) →
      Even (G.degree t) ∨ t = u := by
    intro t ht
    apply hp t
    simp only [← SimpleGraph.ncard_neighborSet] at ht ⊢
    rw [← hg]
    exact ht
  have hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) := by
    intro t ht
    have ho : Odd ((ordinaryMatePuncture (starPuncture G u B) ((x,q) :: M)).degree t) := by
      rcases hcovered t ht with htB | ⟨e,heM,htE⟩
      · exact hl t htB
      · rcases htE with htE | htE
        · rw [htE]
          exact (he e heM).1
        · rw [htE]
          exact (he e heM).2
    simp only [← SimpleGraph.ncard_neighborSet] at ho ⊢
    rw [hg]
    exact ho
  have hsub : ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M ≤ G :=
    (ordinaryMatePuncture_le M).trans (fun _ _ h => h.1.1)
  exact prepared_ordinary_component_floor C p hpC u hsub hprofile hodd hcap K hpK

/-- Deleted private leaves and neutralized petal endpoints supply floors
in their own delayed-auxiliary components. Their original hub neighbour
is odd, so at most one even neighbour survives. -/
theorem delayed_private_component_floor
    (u x q p : V) (B : Finset V) (M : List (V × V))
    (hxEven : Even (G.degree x)) (hpx : G.Adj p x)
    (hpdegree : eDegree G p = 2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t)) →
    Odd (J.degree x) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent, p ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  intro hkeep hxOdd hcap K hpK
  have hsub : ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M ≤ G :=
    (ordinaryMatePuncture_le M).trans (fun _ _ h => h.1.1)
  exact contact_private_component_floor_without_parity hsub hkeep hcap K x p
    hpK hxEven hxOdd hpx hpdegree

/-- Original support labels turn exhaustive deletion-boundary coverage
into the four types consumed by delayed component-floor assembly. -/
theorem delayed_auxiliary_component_contact
    (hconn : G.Connected) (u x q : V) (B privates : Finset V)
    (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (K : (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).ConnectedComponent) :
    u ∈ K.supp ∨ (x ∈ K.supp ∨ q ∈ K.supp) ∨
      (∃ p ∈ privates, p ∈ K.supp) ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) ∈ K.supp := by
  classical
  obtain ⟨t,ht,htype⟩ := delayed_auxiliary_component_meets_boundary hconn u x q B M K
  have hlabel : (t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t) →
      (∃ p ∈ privates, p ∈ K.supp) ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) ∈ K.supp := by
    rintro (hp | ⟨C,hC,v,hv,hvt⟩)
    · exact Or.inl ⟨t,hp,ht⟩
    · exact Or.inr ⟨C,hC,v,hv,hvt ▸ ht⟩
  rcases htype with rfl | htB | rfl | rfl | ⟨e,he,hte⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inr (hlabel (hB t htB)))
  · exact Or.inr (Or.inl (Or.inl ht))
  · exact Or.inr (Or.inl (Or.inr ht))
  · exact Or.inr (Or.inr (hlabel (hM e he t hte)))

/-- Assemble the delayed auxiliary from original packet labels and an
even deletion star at an odd centre. Parity, component floors and the
protected decomposition are all derived. -/
theorem bare_delayed_auxiliary_endpoint
    (h u x p q : V) (H : BareMinimalCounterexample G h x)
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : ((x,q) :: M).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ (x,q) :: M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ (x,q) :: M, t = e.1 ∨ t = e.2) ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ (x,q) :: M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ (x,q) :: M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧
        ¬ G.Adj c u)
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B)
    (hxu : x ≠ u) (hpu : p ≠ u) (hqu : q ≠ u)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpqne : p ≠ q)
    (hxEven : Even (G.degree x)) (hpdegree : eDegree G p = 2)
    (hpetal : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2 ∧
      p ≠ e.1 ∧ p ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ x) (hhq : h ≠ q)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∃ D : Decomposition J, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hdis
  have hv := havoid (x,q) (List.mem_cons_self ..)
  have hxq := hedges (x,q) (List.mem_cons_self ..)
  have hav : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q := by
    intro e he
    have ha := havoid e (List.mem_cons_of_mem (x,q) he)
    have hs := hhead e he
    exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,
      hs.1.symm,hs.2.1.symm,hs.2.2.1.symm,hs.2.2.2.symm⟩
  have hp := delayed_auxiliary_profile u x q B M
    (fun hu => G.irrefl (hadj u hu)) hadj huOdd hEvenB hleaves
    hxu hqu hv.2.2.1 hv.2.2.2 hxq.1 hxEven hxq.2.2 htail hav
    (fun e he => hedges e (List.mem_cons_of_mem (x,q) he))
  have hkeep := hp.1
  have hxOdd := hp.2.2.1
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ha => ha.1.1)
  have hcap := bare_odd_hub_subgraph_cap h x H J hsub hkeep hxOdd
  have hcentre := delayed_auxiliary_centre_eDegree_le_one h u x q B M
    hadj hleaves hdis havoid hedges hcontacts
  have hd := delayed_auxiliary_protected_degree (G := G) u x q h B M hhu hhB hhx hhq hhM
  rcases H.counterexample.1 with ⟨hconn,_,hhpos,hhEven,_,_,_⟩
  apply assemble_one_ceiling_of_component_floors J h
  · rw [hd]; exact hhpos
  · rw [hd]; exact hhEven
  · exact hcap
  · intro K _
    rcases delayed_auxiliary_component_contact hconn u x q B privates M F hB hM K with
      huK | hspoke | ⟨t,ht,htK⟩ | ⟨C,hC,t,htC,htK⟩
    · exact contact_component_floor_of_eDegree_le_one hcap K u huK hcentre
    · exact delayed_spoke_petal_component_floor u x p q B M hxu hpu hqu
        hxp hpq hpqne hxEven hpdegree hpetal hkeep hxOdd hcap K hspoke
    · exact delayed_private_component_floor u x q t B M hxEven
        (hprivates t ht).1 (hprivates t ht).2 hkeep hxOdd hcap K htK
    · rcases hordinary C hC with hregular | ⟨a,b,c,hs,ha,hb,hac,hbc,
        hau,hbu,hcu,hcAvoid,hcNonadj⟩
      · exact delayed_regular_packet_component_floor u x q B M hadj hleaves hdis
          havoid hedges C t htC hregular hcap K htK
      · have hcontact : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp := by
          rw [hs] at htC
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
          rcases htC with rfl | rfl | rfl
          · exact Or.inl htK
          · exact Or.inr (Or.inl htK)
          · exact Or.inr (Or.inr htK)
        exact delayed_special_packet_component_floor u x q B M hadj hleaves hdis
          havoid hedges C a b c hs ha hb hac hbc hau hbu hcu hcAvoid hcNonadj
          hcap K hcontact

/-- Ordinary packets are restored first, followed by the selected private
edge. The pending tail still contains the hub spoke and private mates;
all parity and centre-reserve guards are derived from the deletion data. -/
theorem restore_delayed_ordinary_prefix_and_private
    (u x p q : V) (B : Finset V) (O N : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B) (hpB : p ∈ B)
    (hdis : (O ++ (x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O ++ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O ++ (x,q) :: N, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (hpair : ∀ t, G.Adj p t → Even (G.degree t) → t = x ∨ t = q)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B)
      (O ++ (x,q) :: N))) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u B) ((x,q) :: N)) ⊔
        SimpleGraph.edge p u), E.size = D.size ∧ 2 ≤ E.endpointCount p ∧
      E.endpointCount u + 1 = D.endpointCount u ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
      ∀ t, (∀ e ∈ O, t ≠ e.1 ∧ t ≠ e.2) → t ≠ u → t ≠ p →
        E.endpointCount t = D.endpointCount t := by
  classical
  letI : DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
  have huD := ordinary_star_mates_centre_reserve u B (O ++ (x,q) :: N)
    hadj huOdd hEvenB (fun e he => ⟨(havoid e he).1,(havoid e he).2.1⟩) D
  obtain ⟨D1,hs1,hu1,hrec1,hkeep1⟩ := restore_ordinary_mate_prefix u B hadj hleaves
    O ((x,q) :: N) hdis havoid hedges hpacket D huD
  let J := ordinaryMatePuncture (starPuncture G u B) ((x,q) :: N)
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have htDis := (List.pairwise_append.mp hdis).2.1
  have htAvoid := fun e he => havoid e (List.mem_append_right O he)
  have htEdges := fun e he => hedges e (List.mem_append_right O he)
  have hp := ordinary_star_mates_even_preserved u B ((x,q) :: N)
    hadj hleaves htDis htAvoid htEdges
  have huJ : Odd (J.degree u) := by
    have hs := starPuncture_degree_center (G := G) u B
      (fun hu => G.irrefl (hadj u hu))
      (fun t ht => (G.mem_neighborFinset u t).mpr (hadj t ht))
    have hm := ordinaryMatePuncture_degree_of_avoids
      (G := starPuncture G u B) ((x,q) :: N) u
      (fun e he => ⟨(htAvoid e he).1.symm,(htAvoid e he).2.1.symm⟩)
    simp only [← SimpleGraph.ncard_neighborSet] at hs hm huOdd ⊢
    change (J.neighborSet u).ncard = _ at hm
    rw [hm,Nat.odd_iff]
    rw [Nat.odd_iff] at huOdd
    rw [Nat.even_iff] at hEvenB
    omega
  have hkeep : ∀ t, Even (J.degree t) → Even (G.degree t) := by
    intro t ht
    rcases hp t ht with he | rfl
    · exact he
    · exact False.elim ((Nat.not_even_iff_odd.mpr huJ) ht)
  have hodd := ordinary_star_mates_endpoints_odd u B ((x,q) :: N)
    htDis htAvoid htEdges (x,q) (List.mem_cons_self ..)
  have hpOdd := ordinary_star_mates_leaves_odd u B ((x,q) :: N) hadj hleaves
    (fun e he => ⟨(htAvoid e he).2.2.1,(htAvoid e he).2.2.2⟩) p hpB
  have hsub : J ≤ G := (ordinaryMatePuncture_le _).trans (fun _ _ ht => ht.1)
  have hmissing : ¬ J.Adj p u := by
    intro ha
    exact starPuncture_missing G u B (fun hu => G.irrefl (hadj u hu)) p hpB
      (ordinaryMatePuncture_le ((x,q) :: N) ha).symm
  obtain ⟨E,hs2,hp2,hv⟩ := restore_delayed_first_private (R := G) J u p x q
    (hadj p hpB) hsub hmissing hkeep hpair hodd.1 hodd.2 hpOdd D1 (by rwa [hu1])
  refine ⟨E,hs2.trans hs1,hp2,?_,?_,?_⟩
  · have hvu := hv u
    simp only [(hadj p hpB).ne.symm,ite_true,ite_false,Nat.add_zero] at hvu
    exact hvu.trans hu1
  · intro e he
    have ha := havoid e (List.mem_append_left _ he)
    have hpe : p ≠ e.1 := by
      intro hh
      exact ha.2.2.1 (hh ▸ hpB)
    have hue : u ≠ e.1 := ha.1.symm
    have heq : E.endpointCount e.1 = D1.endpointCount e.1 := by
      simpa only [hue,hpe,ite_false,Nat.add_zero] using hv e.1
    rw [heq]
    exact hrec1 e he
  · intro t ht htu htp
    have hvt := hv t
    simp only [htu.symm,htp.symm,ite_false,Nat.add_zero] at hvt
    exact hvt.trans (hkeep1 t ht)

/-- Restore the ordinary prefix and reserved contact while keeping the
protected vertex exposed. Special packets require no deleted mate. -/
theorem restore_delayed_protected_prefix
    (h u x p q : V) (B : Finset V) (O N : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (hleaves : ∀ t ∈ B, Even (G.degree t))
    (huOdd : Odd (G.degree u)) (hEvenB : Even #B) (hpB : p ∈ B)
    (hdis : (O ++ (x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ O ++ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B)
    (hedges : ∀ e ∈ O ++ (x,q) :: N, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B)
    (hpair : ∀ t, G.Adj p t → Even (G.degree t) → t = x ∨ t = q)
    (hhu : h ≠ u) (hhp : h ≠ p)
    (hhO : ∀ e ∈ O, h ≠ e.1 ∧ h ≠ e.2)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u B)
      (O ++ (x,q) :: N)))
    (hsize : D.size ≤ (Fintype.card V + 1) / 2)
    (hh : 2 ≤ D.endpointCount h) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u B) ((x,q) :: N)) ⊔
        SimpleGraph.edge p u),
      E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
      2 ≤ E.endpointCount p ∧ E.endpointCount u + 1 = D.endpointCount u ∧
      (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
      ∀ t, (∀ e ∈ O, t ≠ e.1 ∧ t ≠ e.2) → t ≠ u → t ≠ p →
        E.endpointCount t = D.endpointCount t := by
  obtain ⟨E,hs,hp,hu,hrec,hkeep⟩ := restore_delayed_ordinary_prefix_and_private
    (G := G) u x p q B O N hadj hleaves huOdd hEvenB hpB
    hdis havoid hedges hpacket hpair D
  refine ⟨E,hs ▸ hsize,?_,hp,hu,hrec,hkeep⟩
  rw [hkeep h hhO hhu hhp]
  exact hh

end Gallai.TwoException
