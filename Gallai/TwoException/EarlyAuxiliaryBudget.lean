/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyAuxiliaryProfile
public import Gallai.Inputs.CorridorAddibility

@[expose] public section

/-! # Ordinary-component floors in the early-spoke auxiliary -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance (u x q : V) (B : Finset V) :
    DecidableRel ((starPuncture G u B).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance (u x q : V) (B : Finset V) (M : List (V × V)) :
    DecidableRel (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Star leaves other than the spoke recipient remain odd after the
entire mate preparation. This excludes the double-deleted recipient,
which instead has its separate zero-E-degree witness. -/
theorem early_spoke_mates_leaf_odd
    (u x q t : V) (B : Finset V) (M : List (V × V))
    (htB : t ∈ B) (hut : G.Adj u t) (htEven : Even (G.degree t))
    (htx : t ≠ x) (htq : t ≠ q)
    (havoidB : ∀ e ∈ M, e.1 ∉ B ∧ e.2 ∉ B) :
    Odd ((ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s(x,q)}) M).degree t) := by
  classical
  let K := (starPuncture G u B).deleteEdges {s(x,q)}
  letI : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have ho := contact_spoke_puncture_leaf_odd u x q t B htB hut htEven htx htq
  have hd := ordinaryMatePuncture_degree_of_avoids (G := K) M t (by
    intro e he
    exact ⟨fun ht => (havoidB e he).1 (ht ▸ htB),
      fun ht => (havoidB e he).2 (ht ▸ htB)⟩)
  simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
  rwa [hd]

/-- A fully prepared ordinary component has a floor budget in every
early-spoke auxiliary component it meets. The hub's component is excluded;
its double-deleted private must not be classified as an odd ordinary leaf. -/
theorem early_regular_packet_component_floor
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (C : (evenSubgraph G).ConnectedComponent) (a : evenVertices G)
    (haC : a ∈ C.supp)
    (hCx : ∀ t : evenVertices G, t ∈ C.supp → (t : V) ≠ x)
    (hCq : ∀ t : evenVertices G, t ∈ C.supp → (t : V) ≠ q)
    (hcovered : ∀ t : evenVertices G, t ∈ C.supp →
      (t : V) ∈ B ∨ ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent, (a : V) ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  intro hprofile hcap K haK
  have hm := early_spoke_mates_endpoints_odd u x q B M hdis havoid hedges
  have hodd : ∀ t : evenVertices G, t ∈ C.supp → Odd (J.degree t) := by
    intro t ht
    rcases hcovered t ht with htB | ⟨e,he,hte⟩
    · exact early_spoke_mates_leaf_odd u x q t B M htB (hadj t htB)
        t.property (hCx t ht) (hCq t ht)
        (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2.1⟩)
    · rcases hte with hte | hte
      · rw [hte]
        exact (hm e he).1
      · rw [hte]
        exact (hm e he).2
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1.1)
  exact prepared_ordinary_component_floor C a haC u hsub hprofile hodd hcap K haK

/-- A special ordinary triangle keeps its third vertex as a non-SET
witness, even when the early spoke recipient belongs to the deleted star. -/
theorem early_special_packet_component_floor
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t)
    (havoid : ∀ e ∈ M, e.1 ∉ B ∧ e.2 ∉ B)
    (C : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hs : C.supp = {a,b,c}) (ha : (a : V) ∈ B) (hb : (b : V) ∈ B)
    (hac : G.Adj a c) (hbc : G.Adj b c)
    (hau : (a : V) ≠ u) (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hax : (a : V) ≠ x) (hbx : (b : V) ≠ x)
    (haq : (a : V) ≠ q) (hbq : (b : V) ≠ q)
    (hcx : (c : V) ≠ x) (hcq : (c : V) ≠ q)
    (hcAvoid : ∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2)
    (hcNonadj : ¬ G.Adj c u) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent,
      ((a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp) →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  intro hprofile hcap K hcontact
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1.1)
  have hao := early_spoke_mates_leaf_odd u x q a B M ha (hadj a ha)
    a.property hax haq havoid
  have hbo := early_spoke_mates_leaf_odd u x q b B M hb (hadj b hb)
    b.property hbx hbq havoid
  have hretain : ∀ t, G.Adj c t → t ≠ u → J.Adj c t := by
    intro t hct htu
    have hstar : (starPuncture G u B).Adj c t :=
      ⟨hct, fun h => htu ((star_sup_adj_off_center u B c t hcu).mp h).2⟩
    have hdel : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj c t := by
      simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      exact ⟨hstar, by simp [hcx, hcq]⟩
    exact (ordinaryMatePuncture_adj_of_avoids
      (G := (starPuncture G u B).deleteEdges {s(x,q)}) M c t hcAvoid).mpr hdel
  have hcK : (c : V) ∈ K.supp := by
    rcases hcontact with haK | hbK | hcK
    · exact K.mem_supp_of_adj_mem_supp haK (hretain a hac.symm hau).symm
    · exact K.mem_supp_of_adj_mem_supp hbK (hretain b hbc.symm hbu).symm
    · exact hcK
  exact ordinary_special_triangle_component_floor C a b c hs u hsub hprofile
    hao hbo (fun ht => hcNonadj (hsub ht)) hcap K hcK

/-- The retained spoke and petal edge carry the early windmill witness
into every component meeting either endpoint of the deleted spoke. The
private's contact is absent, so the newly even centre cannot spoil its cap. -/
theorem early_spoke_petal_component_floor
    (u x p q : V) (B : Finset V) (M : List (V × V))
    (huB : u ∉ B) (hpB : p ∈ B)
    (hxu : x ≠ u) (hpu : p ≠ u) (hqu : q ≠ u)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpqne : p ≠ q)
    (hxEven : Even (G.degree x)) (hpdegree : eDegree G p = 2)
    (hM : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2 ∧
      p ≠ e.1 ∧ p ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    (∀ t, Even (J.degree t) → Even (G.degree t) ∨ t = u) →
    Odd (J.degree x) →
    (∀ t, Even (J.degree t) → eDegree J t ≤ 3) →
    ∀ K : J.ConnectedComponent, x ∈ K.supp ∨ q ∈ K.supp ∨ p ∈ K.supp →
      HasPathBudget (J.induce K.supp) (Fintype.card K.supp / 2) := by
  classical
  dsimp only
  intro hprofile hxOdd hcap K hK
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hxpQ : (starPuncture G u B).Adj x p :=
    ⟨hxp, fun ha => hpu ((star_sup_adj_off_center u B x p hxu).mp ha).2⟩
  have hpqQ : (starPuncture G u B).Adj p q :=
    ⟨hpq, fun ha => hqu ((star_sup_adj_off_center u B p q hpu).mp ha).2⟩
  have hxpD : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj x p := by
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    exact ⟨hxpQ, by simp [hpqne, hxp.ne.symm]⟩
  have hpqD : ((starPuncture G u B).deleteEdges {s(x,q)}).Adj p q := by
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
    exact ⟨hpqQ, by simp [hxp.ne.symm, hpqne]⟩
  have hxpJ : J.Adj x p := (ordinaryMatePuncture_adj_of_avoids
    (G := (starPuncture G u B).deleteEdges {s(x,q)}) M x p
    (fun e he => ⟨(hM e he).1, (hM e he).2.1⟩)).mpr hxpD
  have hpqJ : J.Adj p q := (ordinaryMatePuncture_adj_of_avoids
    (G := (starPuncture G u B).deleteEdges {s(x,q)}) M p q
    (fun e he => ⟨(hM e he).2.2.1, (hM e he).2.2.2.1⟩)).mpr hpqD
  have hpK : p ∈ K.supp := by
    rcases hK with hxK | hqK | hpK
    · exact K.mem_supp_of_adj_mem_supp hxK hxpJ
    · exact K.mem_supp_of_adj_mem_supp hqK hpqJ.symm
    · exact hpK
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1.1)
  have hpuJ : ¬ J.Adj p u := by
    intro ht
    have htD := (ordinaryMatePuncture_le M) ht
    exact starPuncture_missing G u B huB p hpB htD.1.symm
  apply contact_component_floor_of_eDegree_le_one hcap K p hpK
  exact private_eDegree_le_one_of_odd_hub_except_centre u x p hsub hprofile
    hxEven hxOdd hxp.symm hpdegree hpuJ

/-- Original packet labels cover every component of the double-spoke
early auxiliary. Its protected endpoint decomposition is derived from these
labels, the actual puncture profile, and component witnesses. -/
theorem bare_early_double_spoke_auxiliary_endpoint
    (h u x p q : V) (H : BareMinimalCounterexample G h x)
    (B privates : Finset V) (M : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hpB : p ∈ B) (hqB : q ∈ B) (hxB : x ∉ B)
    (hxu : x ≠ u) (hpx : p ≠ x) (hpqne : p ≠ q)
    (hxq : G.Adj x q) (hxp : G.Adj x p) (hpq : G.Adj p q)
    (hpdegree : eDegree G p = 2)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ B ∧ e.2 ∉ B ∧
      e.1 ≠ x ∧ e.2 ≠ x ∧ e.1 ≠ q ∧ e.2 ≠ q)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ t = x ∨ t = h)
    (hB : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hM : ∀ e ∈ M, ∀ t, t = e.1 ∨ t = e.2 → t ∈ privates ∨
      ∃ C ∈ F, ∃ v : evenVertices G, v ∈ C.supp ∧ (v : V) = t)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hprivateContacts : ∀ t ∈ privates, G.Adj t u → t ∈ B)
    (hordinarySeparated : ∀ C ∈ F, ∀ t : evenVertices G,
      t ∈ C.supp → (t : V) ≠ x ∧ (t : V) ≠ q)
    (hordinary : ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ M, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ M, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u)
    (hhu : h ≠ u) (hhB : h ∉ B) (hhx : h ≠ x) (hhq : h ≠ q)
    (hhM : ∀ e ∈ M, h ≠ e.1 ∧ h ≠ e.2) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∃ D : Decomposition J, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  rcases H.counterexample.1 with ⟨hconn, _, hhpos, hhEven, hxEven, _, _⟩
  obtain ⟨hprofile, hxOdd, _, _, _⟩ := early_double_spoke_mates_profile
    u x p q B M hadj hleaves hpB hqB hxB hxu hpx hpqne hxq hxEven hpair
    hdis havoid hedges
  have hc := bare_early_double_spoke_mates_cap h x H u p q B M
    hadj hleaves hpB hqB hxB hxu hpx hpqne hxq hpair hdis havoid hedges hcontacts
  have hcap := hc.1
  have hcentre := hc.2
  have huB : u ∉ B := fun ht => G.irrefl (hadj u ht)
  have hsub : J ≤ G := (ordinaryMatePuncture_le M).trans (fun _ _ ht => ht.1.1)
  have hd := delayed_auxiliary_protected_degree (G := G) u x q h B M hhu hhB hhx hhq hhM
  have hpetal : ∀ e ∈ M, x ≠ e.1 ∧ x ≠ e.2 ∧
      p ≠ e.1 ∧ p ≠ e.2 ∧ q ≠ e.1 ∧ q ≠ e.2 := by
    intro e he
    have ha := havoid e he
    exact ⟨ha.2.2.2.2.1.symm, ha.2.2.2.2.2.1.symm,
      fun ht => ha.2.2.1 (ht ▸ hpB), fun ht => ha.2.2.2.1 (ht ▸ hpB),
      ha.2.2.2.2.2.2.1.symm, ha.2.2.2.2.2.2.2.symm⟩
  apply assemble_one_ceiling_of_component_floors J h
  · rw [hd]; exact hhpos
  · rw [hd]; exact hhEven
  · exact hcap
  · intro K _
    rcases delayed_auxiliary_component_contact hconn u x q B privates M F hB hM K with
      huK | hspoke | ⟨t, ht, htK⟩ | ⟨C, hC, t, htC, htK⟩
    · exact contact_component_floor_of_eDegree_le_one hcap K u huK hcentre
    · exact early_spoke_petal_component_floor u x p q B M huB hpB hxu
        (fun ht => huB (ht ▸ hpB)) (fun ht => huB (ht ▸ hqB))
        hxp hpq hpqne hxEven hpdegree hpetal hprofile hxOdd hcap K
        (hspoke.elim Or.inl (fun hqK => Or.inr (Or.inl hqK)))
    · have htu : ¬ J.Adj t u := by
        intro ha
        have htB := hprivateContacts t ht (hsub ha)
        have haD := (ordinaryMatePuncture_le M) ha
        exact starPuncture_missing G u B huB t htB haD.1.symm
      apply contact_component_floor_of_eDegree_le_one hcap K t htK
      exact private_eDegree_le_one_of_odd_hub_except_centre u x t hsub hprofile
        hxEven hxOdd (hprivates t ht).1 (hprivates t ht).2 htu
    · have hxsep := fun v hv => (hordinarySeparated C hC v hv).1
      have hqsep := fun v hv => (hordinarySeparated C hC v hv).2
      rcases hordinary C hC with hregular | ⟨a, b, c, hs, ha, hb, hac, hbc,
        hau, hbu, hcu, hcAvoid, hcNonadj⟩
      · exact early_regular_packet_component_floor u x q B M hadj hleaves hdis
          havoid hedges C t htC hxsep hqsep hregular hprofile hcap K htK
      · have haC : a ∈ C.supp := by rw [hs]; simp
        have hbC : b ∈ C.supp := by rw [hs]; simp
        have hcC : c ∈ C.supp := by rw [hs]; simp
        have hcontact : (a : V) ∈ K.supp ∨ (b : V) ∈ K.supp ∨ (c : V) ∈ K.supp := by
          rw [hs] at htC
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htC
          rcases htC with rfl | rfl | rfl
          · exact Or.inl htK
          · exact Or.inr (Or.inl htK)
          · exact Or.inr (Or.inr htK)
        exact early_special_packet_component_floor u x q B M hadj
          (fun e he => ⟨(havoid e he).2.2.1, (havoid e he).2.2.2.1⟩)
          C a b c hs ha hb hac hbc hau hbu hcu (hxsep a haC) (hxsep b hbC)
          (hqsep a haC) (hqsep b hbC) (hxsep c hcC) (hqsep c hcC)
          hcAvoid hcNonadj hprofile hcap K hcontact

/-- Pay the double-petal spoke before selecting contact edges. Its
recipient has zero E-degree, and its odd donor supplies the endpoint. All
deleted-star leaves are then positive, including the double-deleted leaf. -/
theorem restore_early_double_spoke
    (u x q : V) (B : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hxB : x ∉ B) (hqx : q ≠ x)
    (havoidB : ∀ e ∈ M, e.1 ∉ B ∧ e.2 ∉ B) :
    let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
    ∀ D : Decomposition J, Odd (J.degree x) → eDegree J q = 0 →
      ∃ E : Decomposition (J ⊔ SimpleGraph.edge q x), E.size = D.size ∧
        (∀ t ∈ B, 0 < E.endpointCount t) ∧
        ∀ t, E.endpointCount t + (if x = t then 1 else 0) =
          D.endpointCount t + if q = t then 1 else 0 := by
  classical
  dsimp only
  let J := ordinaryMatePuncture ((starPuncture G u B).deleteEdges {s(x,q)}) M
  letI : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  intro D hxOdd hzero
  have hmissing : ¬ J.Adj q x := by
    intro ht
    have hdel := (ordinaryMatePuncture_le M) ht
    have hnot := hdel.2
    exact hnot (by simp [Sym2.eq_swap, hqx])
  obtain ⟨E, hs, hv⟩ := D.single_edge_addibility_of_eDegree_zero_center
    q x hqx hmissing hzero (D.endpointCount_pos_of_odd_degree x hxOdd)
  refine ⟨E, hs, ?_, hv⟩
  intro t ht
  have htx : t ≠ x := fun he => hxB (he ▸ ht)
  have hvec := hv t
  simp only [Ne.symm htx, ite_false, Nat.add_zero] at hvec
  by_cases htq : t = q
  · subst t
    simp only [ite_true] at hvec
    omega
  · have ho := early_spoke_mates_leaf_odd u x q t B M ht (hadj t ht)
      (hleaves t ht) htx htq havoidB
    have hp := D.endpointCount_pos_of_odd_degree t ho
    simp only [Ne.symm htq, ite_false, Nat.add_zero] at hvec
    omega

end Gallai.TwoException
