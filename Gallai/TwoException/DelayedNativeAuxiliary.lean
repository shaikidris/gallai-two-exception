/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.DelayedAuxiliaryProfile
public import Gallai.TwoException.OrdinaryFiniteMateAssembly
public import Gallai.TwoException.OrdinaryRestoredPacketShape
public import Gallai.TwoException.DelayedPreparedStarRestoration
public import Gallai.TwoException.DelayedPrivateMateRestoration
public import Gallai.TwoException.OrdinarySpecialExistence

@[expose] public section

/-! # Native odd-component delayed auxiliary -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance delayedNativeComponents : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Returning a genuine star commutes with mate deletions avoiding its
leaves. This identifies the graph consumed by the final delayed return. -/
theorem ordinaryMatePuncture_return_star
    (u : V) (L : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ L, G.Adj u t)
    (havoid : ∀ t ∈ L, ∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) :
    ordinaryMatePuncture (starPuncture G u L) M ⊔ L.sup (SimpleGraph.edge u) =
      ordinaryMatePuncture G M := by
  classical
  have hcomm : ∀ (J : SimpleGraph V) (A : Finset V),
      (∀ t ∈ A, ∀ e ∈ M, t ≠ e.1 ∧ t ≠ e.2) →
      ordinaryMatePuncture (J ⊔ A.sup (SimpleGraph.edge u)) M =
        ordinaryMatePuncture J M ⊔ A.sup (SimpleGraph.edge u) := by
    intro J A
    induction A using Finset.induction_on with
    | empty => intro _; simp
    | @insert a A ha ih =>
      intro hav
      have haM := hav a (Finset.mem_insert_self ..)
      have htM := fun t ht => hav t (Finset.mem_insert_of_mem ht)
      calc
        ordinaryMatePuncture (J ⊔ (insert a A).sup (SimpleGraph.edge u)) M =
            ordinaryMatePuncture ((J ⊔ A.sup (SimpleGraph.edge u)) ⊔
              SimpleGraph.edge a u) M := by
                rw [Finset.sup_insert,SimpleGraph.edge_comm]
                congr 1
                ac_rfl
        _ = (ordinaryMatePuncture (J ⊔ A.sup (SimpleGraph.edge u)) M) ⊔
              SimpleGraph.edge a u := ordinaryMatePuncture_sup_edge M a u haM
        _ = (ordinaryMatePuncture J M ⊔ A.sup (SimpleGraph.edge u)) ⊔
              SimpleGraph.edge a u := by rw [ih htM]
        _ = ordinaryMatePuncture J M ⊔ (insert a A).sup (SimpleGraph.edge u) := by
              rw [Finset.sup_insert,SimpleGraph.edge_comm]
              ac_rfl
  rw [← hcomm (starPuncture G u L) L havoid,starPuncture_restore G u L hadj]

/-- In the remaining delayed star, selected leaves and pending mate
endpoints are odd. Original even contacts not in these sets use their
already restored endpoint reserves; no extra positivity assumption on
the whole current neighbourhood is needed. -/
theorem delayed_remaining_star_endpoint_positive
    (u : V) (L : Finset V) (M : List (V × V))
    (hadj : ∀ t ∈ L, G.Adj u t)
    (hleaves : ∀ t ∈ L, Even (G.degree t))
    (hdis : M.Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ M, e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ L ∧ e.2 ∉ L)
    (hedges : ∀ e ∈ M, G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u L) M))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ L ∨ (∃ e ∈ M, t = e.1 ∨ t = e.2) ∨ 0 < D.endpointCount t) :
    ∀ t, (ordinaryMatePuncture (starPuncture G u L) M).Adj u t ∨ t ∈ L →
      0 < D.endpointCount t := by
  classical
  let J := ordinaryMatePuncture (starPuncture G u L) M
  have hleaf := ordinary_star_mates_leaves_odd (G := G) u L M hadj hleaves
    (fun e he => ⟨(havoid e he).2.2.1,(havoid e he).2.2.2⟩)
  have hends := ordinary_star_mates_endpoints_odd (G := G) u L M hdis havoid hedges
  have hprofile := ordinary_star_mates_even_preserved (G := G) u L M
    hadj hleaves hdis havoid hedges
  intro t ht
  rcases ht with ht | ht
  · rcases Nat.even_or_odd (J.degree t) with he | ho
    · have hut : G.Adj u t := (ordinaryMatePuncture_le M ht).1
      have htG : Even (G.degree t) := by
        rcases hprofile t he with heG | htu
        · exact heG
        · exact False.elim (G.irrefl (htu ▸ hut))
      rcases hcontact t hut htG with htL | ⟨e,heM,hte⟩ | hp
      · exact D.endpointCount_pos_of_odd_degree t (hleaf t htL)
      · rcases hte with htl | htr
        · exact D.endpointCount_pos_of_odd_degree t (htl ▸ (hends e heM).1)
        · exact D.endpointCount_pos_of_odd_degree t (htr ▸ (hends e heM).2)
      · exact hp
    · exact D.endpointCount_pos_of_odd_degree t ho
  · exact D.endpointCount_pos_of_odd_degree t (hleaf t ht)

/-- A single remaining ordinary contact is paid inward. This is the
one-component I/T1/T2 return, independent of the multi-component surplus. -/
theorem restore_delayed_single_ordinary_contact
    (u a x q : V) (N : List (V × V))
    (hadj : G.Adj u a) (haEven : Even (G.degree a))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ ({a} : Finset V) ∧ e.2 ∉ ({a} : Finset V))
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u {a}) ((x,q) :: N)))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ ({a} : Finset V) ∨ (∃ e ∈ (x,q) :: N, t = e.1 ∨ t = e.2) ∨
        0 < D.endpointCount t) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u {a}) ((x,q) :: N)) ⊔
      SimpleGraph.edge u a), E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ≠ a → E.endpointCount t = D.endpointCount t := by
  classical
  have huL : u ∉ ({a} : Finset V) := by simpa using hadj.ne
  have hpos := delayed_remaining_star_endpoint_positive G u {a} ((x,q) :: N)
    (by intro t ht; simpa using (Finset.mem_singleton.mp ht ▸ hadj))
    (by intro t ht; simpa using (Finset.mem_singleton.mp ht ▸ haEven))
    hdis havoid hedges D hcontact
  have hzero : #{t ∈ (ordinaryMatePuncture (starPuncture G u {a})
      ((x,q) :: N)).neighborFinset u | D.endpointCount t = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htN,htZero⟩ := Finset.mem_filter.mp ht
    have hp := hpos t (Or.inl (((ordinaryMatePuncture (starPuncture G u {a})
      ((x,q) :: N)).mem_neighborFinset u t).mp htN))
    omega
  have haPos := hpos a (Or.inr (Finset.mem_singleton_self _))
  obtain ⟨E,hs,hvec⟩ := D.single_edge_addibility u a hadj.ne
    (fun he => starPuncture_missing G u {a} huL a (Finset.mem_singleton_self _)
      (ordinaryMatePuncture_le _ he)) (by rw [hzero]; exact haPos)
  refine ⟨E,hs,?_,?_⟩
  · have hv := hvec u
    simp only [hadj.ne.symm,ite_false,ite_true,Nat.add_zero] at hv
    omega
  · intro t htu hta
    have hv := hvec t
    simp only [Ne.symm htu,Ne.symm hta,ite_false,Nat.add_zero] at hv
    exact hv

/-- Once the sole private edge has returned, the odd pending star has
only ordinary leaves. Packet shapes and contact reserves restore it without
spending an endpoint at the still unpaid hub. -/
theorem restore_delayed_ordinary_only_star
    (u x q : V) (L : Finset V) (N : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion P).image Subtype.val)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hcount : 1 < #F) (hodd : Odd #L)
    (hadj : ∀ t ∈ L, G.Adj u t)
    (hleaves : ∀ t ∈ L, Even (G.degree t))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ L ∧ e.2 ∉ L)
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hcap : ∀ t ∈ L, eDegree G t ≤ 2)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u L) ((x,q) :: N)))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ L ∨ (∃ e ∈ (x,q) :: N, t = e.1 ∨ t = e.2) ∨ 0 < D.endpointCount t)
    (hregular : ∀ C ∈ F,
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)})) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u L) ((x,q) :: N)) ⊔
        L.sup (SimpleGraph.edge u)),
      E.size = D.size ∧ 0 < E.endpointCount u ∧
        ∀ t, t ≠ u → t ∉ L → E.endpointCount t = D.endpointCount t := by
  classical
  have hnon : L.Nonempty := by
    apply Finset.card_pos.mp
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨b,hb⟩ := hnon
  have huL : u ∉ L := fun ht => G.irrefl (hadj u ht)
  have hx := havoid (x,q) (List.mem_cons_self ..)
  have hsub : ordinaryMatePuncture (starPuncture G u L) ((x,q) :: N) ≤ G :=
    (ordinaryMatePuncture_le _).trans (fun _ _ ha => ha.1)
  have hxOdd := (ordinary_star_mates_endpoints_odd (G := G) u L ((x,q) :: N)
    hdis havoid hedges (x,q) (List.mem_cons_self ..)).1
  have hPS : ∀ C ∈ F, (P C).image Subtype.val ⊆ ∅ ∪ L := by
    intro C hC t ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    apply Finset.mem_union_right
    rw [hL]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,ha⟩,hat⟩
  obtain ⟨E,hs,hupos,hkeep⟩ :=
    (restore_delayed_prepared_star (R := G) D u x b ∅ L F ∅ P hL hsupp hPS
      (Finset.disjoint_empty_left _) (by simpa using huL)
      (by simpa using hx.2.2.1) hx.1 (by simpa using hb)
      (by simpa using hodd) (by simpa using hcount) hsub
      (by simpa using hadj) (by simpa using hleaves)
      (ordinary_star_mates_even_preserved (G := G) u L ((x,q) :: N)
        hadj hleaves hdis havoid hedges)
      (by
        intro t ht
        have htL : t ∈ L := by simpa using ht
        intro ha
        exact starPuncture_missing G u L huL t htL
          (ordinaryMatePuncture_le _ ha))
      (by simpa only [Finset.empty_union] using
        (delayed_remaining_star_endpoint_positive G u L ((x,q) :: N)
          hadj hleaves hdis havoid hedges D hcontact))
      (D.endpointCount_pos_of_odd_degree x hxOdd)
      (by intro w hw; simp at hw) (by simpa using hcap)
      (fun C hC _ => hregular C hC) (by intro C _ hC; simp at hC))
  have hg : (ordinaryMatePuncture (starPuncture G u L) ((x,q) :: N)) ⊔
      (∅ ∪ L).sup (SimpleGraph.edge u) =
      (ordinaryMatePuncture (starPuncture G u L) ((x,q) :: N)) ⊔
        L.sup (SimpleGraph.edge u) := by rw [Finset.empty_union]
  have htransport : ∀ {J R : SimpleGraph V} (e : J = R) (E : Decomposition J),
      (e ▸ E).size = E.size ∧ ∀ t, (e ▸ E).endpointCount t = E.endpointCount t := by
    intro J R e E
    subst R
    exact ⟨rfl,fun _ => rfl⟩
  refine ⟨hg ▸ E,(htransport hg E).1.trans hs,?_,?_⟩
  · rw [(htransport hg E).2]
    exact hupos
  · intro t htu htL
    rw [(htransport hg E).2]
    exact hkeep t htu (by simpa using htL)

/-- Remaining private leaves contribute to the strict packet gain while
the unpaid hub stays exposed. -/
theorem restore_delayed_private_ordinary_star
    (u x q : V) (K L : Finset V) (N : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion P).image Subtype.val)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hKL : Disjoint K L) (hcount : 1 < #K + #F) (hodd : Odd #(K ∪ L))
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ K ∪ L ∧ e.2 ∉ K ∪ L)
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hprivate : ∀ w ∈ K, ∃ p, ∀ t, G.Adj w t → Even (G.degree t) → t = x ∨ t = p)
    (hcap : ∀ t ∈ L, eDegree G t ≤ 2)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u (K ∪ L)) ((x,q) :: N)))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ (∃ e ∈ (x,q) :: N, t = e.1 ∨ t = e.2) ∨ 0 < D.endpointCount t)
    (hregular : ∀ C ∈ F,
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)})) :
    ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u (K ∪ L)) ((x,q) :: N)) ⊔
      (K ∪ L).sup (SimpleGraph.edge u)),
      E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → E.endpointCount t = D.endpointCount t := by
  classical
  have hnon : (K ∪ L).Nonempty := by
    apply Finset.card_pos.mp
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨b,hb⟩ := hnon
  have huL : u ∉ K ∪ L := fun ht => G.irrefl (hadj u ht)
  have hx := havoid (x,q) (List.mem_cons_self ..)
  have hsub : ordinaryMatePuncture (starPuncture G u (K ∪ L)) ((x,q) :: N) ≤ G :=
    (ordinaryMatePuncture_le _).trans (fun _ _ ha => ha.1)
  have hxOdd := (ordinary_star_mates_endpoints_odd (G := G) u (K ∪ L) ((x,q) :: N)
    hdis havoid hedges (x,q) (List.mem_cons_self ..)).1
  have hPS : ∀ C ∈ F, (P C).image Subtype.val ⊆ K ∪ L := by
    intro C hC t ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    apply Finset.mem_union_right
    rw [hL]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,ha⟩,hat⟩
  exact restore_delayed_prepared_star (R := G) D u x b K L F ∅ P hL hsupp hPS
    hKL huL hx.2.2.1 hx.1 hb hodd (by simpa using hcount) hsub hadj hleaves
    (ordinary_star_mates_even_preserved (G := G) u (K ∪ L) ((x,q) :: N)
      hadj hleaves hdis havoid hedges)
    (fun t ht he => starPuncture_missing G u (K ∪ L) huL t ht
      (ordinaryMatePuncture_le _ he))
    (delayed_remaining_star_endpoint_positive G u (K ∪ L) ((x,q) :: N)
      hadj hleaves hdis havoid hedges D hcontact)
    (D.endpointCount_pos_of_odd_degree x hxOdd) hprivate hcap
    (fun C hC _ => hregular C hC) (by intro C _ hC; simp at hC)

/-- Return a mixed star with special two-contact packets. The loss of one
gain unit per special packet is explicit in the strict count. -/
theorem return_delayed_prepared_mixed_star
    (u x q : V) (K L : Finset V) (N : List (V × V))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion P).image Subtype.val)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hKL : Disjoint K L) (hcount : #special + 1 < #K + #F)
    (hodd : Odd #(K ∪ L))
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ K ∪ L ∧ e.2 ∉ K ∪ L)
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hprivate : ∀ w ∈ K, ∃ p, ∀ t,
      G.Adj w t → Even (G.degree t) → t = x ∨ t = p)
    (hcap : ∀ t ∈ L, eDegree G t ≤ 2)
    (D : Decomposition (ordinaryMatePuncture
      (starPuncture G u (K ∪ L)) ((x,q) :: N)))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∪ L ∨ (∃ e ∈ (x,q) :: N, t = e.1 ∨ t = e.2) ∨
      0 < D.endpointCount t)
    (hregular : ∀ C ∈ F, C ∉ special →
      (∃ a : evenVertices G, (P C).image Subtype.val = {a.val} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {a.val} ∧ 2 ≤ D.endpointCount b.val) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {a.val,b.val,c.val}))
    (hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ G.Adj a b ∧
      (P C).image Subtype.val = {a.val,b.val}) :
    ∃ E : Decomposition (ordinaryMatePuncture G ((x,q) :: N)),
      E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K ∪ L → E.endpointCount t = D.endpointCount t := by
  classical
  have hnon : (K ∪ L).Nonempty := by
    apply Finset.card_pos.mp
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨b,hb⟩ := hnon
  have huL : u ∉ K ∪ L := fun ht => G.irrefl (hadj u ht)
  have hx := havoid (x,q) (List.mem_cons_self ..)
  have hsub : ordinaryMatePuncture (starPuncture G u (K ∪ L)) ((x,q) :: N) ≤ G :=
    (ordinaryMatePuncture_le _).trans (fun _ _ ha => ha.1)
  have hxOdd := (ordinary_star_mates_endpoints_odd (G := G) u (K ∪ L) ((x,q) :: N)
    hdis havoid hedges (x,q) (List.mem_cons_self ..)).1
  have hPS : ∀ C ∈ F, (P C).image Subtype.val ⊆ K ∪ L := by
    intro C hC t ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    apply Finset.mem_union_right
    rw [hL]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,ha⟩,hat⟩
  obtain ⟨E,hs,hu,hkeep⟩ := restore_delayed_prepared_star (R := G)
    D u x b K L F special P hL hsupp hPS hKL huL hx.2.2.1 hx.1 hb hodd
    hcount hsub hadj hleaves
    (ordinary_star_mates_even_preserved (G := G) u (K ∪ L) ((x,q) :: N)
      hadj hleaves hdis havoid hedges)
    (fun t ht he => starPuncture_missing G u (K ∪ L) huL t ht
      (ordinaryMatePuncture_le _ he))
    (delayed_remaining_star_endpoint_positive G u (K ∪ L) ((x,q) :: N)
      hadj hleaves hdis havoid hedges D hcontact)
    (D.endpointCount_pos_of_odd_degree x hxOdd) hprivate hcap hregular hspecial
  have hg := ordinaryMatePuncture_return_star G u (K ∪ L) ((x,q) :: N) hadj
    (fun t ht e he => ⟨fun h => (havoid e he).2.2.1 (h ▸ ht),
      fun h => (havoid e he).2.2.2 (h ▸ ht)⟩)
  have htransport : ∀ {J R : SimpleGraph V} (e : J = R) (E : Decomposition J),
      (e ▸ E).size = E.size ∧ ∀ t, (e ▸ E).endpointCount t = E.endpointCount t := by
    intro J R e E
    subst R
    exact ⟨rfl,fun _ => rfl⟩
  refine ⟨hg ▸ E,?_,?_,?_⟩
  · rw [(htransport hg E).1]; exact hs
  · rw [(htransport hg E).2]; exact hu
  · intro t htu ht
    rw [(htransport hg E).2]; exact hkeep t htu ht

/-- Returning the reserved contact leaves exactly K.erase p as private leaves. -/
theorem delayed_reserved_contact_remaining_graph
    (u p : V) (K L : Finset V) (M : List (V × V))
    (hpK : p ∈ K) (hpL : p ∉ L)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (havoid : ∀ e ∈ M, p ≠ e.1 ∧ p ≠ e.2) :
    (ordinaryMatePuncture (starPuncture G u (K ∪ L)) M) ⊔ SimpleGraph.edge p u =
      ordinaryMatePuncture (starPuncture G u (K.erase p ∪ L)) M := by
  have hu : u ∉ K ∪ L := fun ht => G.irrefl (hadj u ht)
  have heq := ordinaryMatePuncture_restore_star_leaf (G := G) u p (K ∪ L) M
    hu (Finset.mem_union_left L hpK) (hadj p (Finset.mem_union_left L hpK)) havoid
  rw [Finset.erase_union_distrib,Finset.erase_eq_of_notMem hpL] at heq
  exact heq

/-- The actual remaining mixed star reconstructs the mate puncture, while
preserving every endpoint reserve outside the remaining leaves. -/
theorem return_delayed_remaining_mixed_star
    (u x q p : V) (K L : Finset V) (N : List (V × V))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hL : L = (F.biUnion P).image Subtype.val)
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hpK : p ∈ K) (hpL : p ∉ L) (hKL : Disjoint K L)
    (hEven : Even #(K ∪ L)) (hcount : 1 < #(K.erase p) + #F)
    (hadj : ∀ t ∈ K ∪ L, G.Adj u t)
    (hleaves : ∀ t ∈ K ∪ L, Even (G.degree t))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (havoid : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ K ∪ L ∧ e.2 ∉ K ∪ L)
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hprivate : ∀ w ∈ K.erase p, ∃ a, ∀ t,
      G.Adj w t → Even (G.degree t) → t = x ∨ t = a)
    (hcap : ∀ t ∈ L, eDegree G t ≤ 2)
    (D : Decomposition (ordinaryMatePuncture (starPuncture G u (K.erase p ∪ L)) ((x,q) :: N)))
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K.erase p ∪ L ∨ (∃ e ∈ (x,q) :: N, t = e.1 ∨ t = e.2) ∨
      0 < D.endpointCount t)
    (hregular : ∀ C ∈ F,
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)})) :
    ∃ E : Decomposition (ordinaryMatePuncture G ((x,q) :: N)),
      E.size = D.size ∧ 0 < E.endpointCount u ∧
      ∀ t, t ≠ u → t ∉ K.erase p ∪ L → E.endpointCount t = D.endpointCount t := by
  classical
  let W := K.erase p ∪ L
  have hWB : W ⊆ K ∪ L := Finset.union_subset_union (Finset.erase_subset _ _) (Finset.Subset.refl _)
  have hW : (K ∪ L).erase p = W := by
    rw [Finset.erase_union_distrib,Finset.erase_eq_of_notMem hpL]
  have hOdd : Odd #W := by
    have hpB := Finset.mem_union_left L hpK
    have hc := Finset.card_erase_add_one hpB
    rw [hW] at hc
    rw [Nat.even_iff] at hEven
    rw [Nat.odd_iff]
    omega
  have hav : ∀ e ∈ (x,q) :: N,
      e.1 ≠ u ∧ e.2 ≠ u ∧ e.1 ∉ W ∧ e.2 ∉ W :=
    fun e he => ⟨(havoid e he).1,(havoid e he).2.1,
      fun ht => (havoid e he).2.2.1 (hWB ht),
      fun ht => (havoid e he).2.2.2 (hWB ht)⟩
  obtain ⟨E,hs,hu,hkeep⟩ := restore_delayed_private_ordinary_star G u x q
    (K.erase p) L N F P hL hsupp (hKL.mono_left (Finset.erase_subset _ _))
    hcount hOdd (fun t ht => hadj t (hWB ht)) (fun t ht => hleaves t (hWB ht))
    hdis hav hedges hprivate hcap D hcontact hregular
  have hg := ordinaryMatePuncture_return_star G u W ((x,q) :: N)
    (fun t ht => hadj t (hWB ht))
    (fun t ht e he => ⟨fun h => (hav e he).2.2.1 (h ▸ ht),
      fun h => (hav e he).2.2.2 (h ▸ ht)⟩)
  have htransport : ∀ {J R : SimpleGraph V} (e : J = R) (E : Decomposition J),
      (e ▸ E).size = E.size ∧ ∀ t, (e ▸ E).endpointCount t = E.endpointCount t := by
    intro J R e E; subst R; exact ⟨rfl,fun _ => rfl⟩
  refine ⟨hg ▸ E,?_,?_,?_⟩
  · rw [(htransport hg E).1]; exact hs
  · rw [(htransport hg E).2]; exact hu
  · intro t htu htW
    rw [(htransport hg E).2]; exact hkeep t htu htW

/-- Final mate/spoke payment does not depend on the private-leaf offset. -/
theorem return_delayed_original_mates_and_spoke
    (x q p u : V) (N : List (V × V))
    (hdis : ((x,q) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hedges : ∀ e ∈ (x,q) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hpavoid : ∀ e ∈ N, p ≠ e.1 ∧ p ≠ e.2)
    (huavoid : ∀ e ∈ N, u ≠ e.1 ∧ u ≠ e.2)
    (hmates : ∀ e ∈ N, ∀ t, G.Adj e.2 t → Even (G.degree t) → t = x ∨ t = e.1)
    (hpair : ∀ t, G.Adj q t → Even (G.degree t) → t = x ∨ t = p)
    (D : Decomposition (ordinaryMatePuncture G ((x,q) :: N)))
    (hp : 2 ≤ D.endpointCount p) (hu : 0 < D.endpointCount u) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ t, t ≠ x → t ≠ q → (∀ e ∈ N, t ≠ e.1 ∧ t ≠ e.2) →
        E.endpointCount t = D.endpointCount t := by
  classical
  have hspoke := hedges (x,q) (List.mem_cons_self ..)
  have hsingle : [(x,q)].Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by simp
  have hsingleE : ∀ e ∈ [(x,q)], G.Adj e.1 e.2 ∧
      Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    simp only [List.mem_singleton] at he
    subst e
    exact hspoke
  have hprofile := ordinaryMatePuncture_even_preserved (G := G) [(x,q)] hsingle hsingleE
  have hxOdd := (ordinaryMatePuncture_endpoints_odd (G := G)
    [(x,q)] hsingle hsingleE (x,q) (by simp)).1
  obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hdis
  have hneutral : ∀ e ∈ N, (G.deleteEdges {s(x,q)}).Adj e.1 e.2 ∧
      Even ((G.deleteEdges {s(x,q)}).degree e.1) ∧
      Even ((G.deleteEdges {s(x,q)}).degree e.2) := by
    intro e he
    have hn := hhead e he
    have hg := hedges e (List.mem_cons_of_mem _ he)
    refine ⟨?_,?_,?_⟩
    · exact (ordinaryMatePuncture_adj_of_avoids (G := G) [(x,q)] e.1 e.2
        (by intro f hf; simp only [List.mem_singleton] at hf; subst f
            exact ⟨hn.1.symm,hn.2.2.1.symm⟩)).mpr hg.1
    · rw [degree_delete_edge_of_ne G x q e.1 hn.1.symm hn.2.2.1.symm]; exact hg.2.1
    · rw [degree_delete_edge_of_ne G x q e.2 hn.2.1.symm hn.2.2.2.symm]; exact hg.2.2
  have hgD : ordinaryMatePuncture G ((x,q) :: N) =
      ordinaryMatePuncture (G.deleteEdges {s(x,q)}) N := by
    rw [ordinaryMatePuncture_deleteEdges_comm]; rfl
  have htransport : ∀ {J R : SimpleGraph V} (e : J = R) (D : Decomposition J),
      (e ▸ D).size = D.size ∧ ∀ t, (e ▸ D).endpointCount t = D.endpointCount t := by
    intro J R e D; subst R; exact ⟨rfl,fun _ => rfl⟩
  let D0 := hgD ▸ D
  obtain ⟨E,hs,hkeep⟩ := restore_delayed_mates_and_final_spoke (R := G)
    x q p u N hspoke.1 hprofile hxOdd htail
    (fun e he => by simpa only [← SimpleGraph.ncard_neighborSet] using hneutral e he)
    (fun e he => ⟨(hhead e he).1,(hhead e he).2.1⟩) hpavoid huavoid hmates hpair D0
    (by rw [(htransport hgD D).2]; exact hp)
    (by rw [(htransport hgD D).2]; exact hu)
  refine ⟨E,hs.trans (htransport hgD D).1,?_⟩
  intro t htx htq htN
  rw [hkeep t htx htq htN,(htransport hgD D).2]

/-- Selected regular and special ordinary packets give the complete
boundary alternative required by the delayed component-floor theorem.
The special witness avoids both flattened ordinary mates and every
hub-component deletion by original component separation. -/
theorem delayed_ordinary_boundary_from_selected_family
    (u : V) (x : evenVertices G) (hu : Odd (G.degree u))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hmsupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (B : Finset V) (hPB : ∀ C ∈ F, ∀ a ∈ P C, (a : V) ∈ B)
    (N : List (V × V))
    (hN : ∀ e ∈ N, ∃ a b : evenVertices G, e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ a ∈ P C ∧ b ∈ P C ∧ mates C = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u) :
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    ∀ C ∈ F,
      (∀ t : evenVertices G, t ∈ C.supp → (t : V) ∈ B ∨
        ∃ e ∈ O ++ N, (t : V) = e.1 ∨ (t : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ O ++ N, (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧ ¬ G.Adj c u := by
  classical
  dsimp only
  intro C hC
  by_cases hCs : C ∈ special
  · obtain ⟨a,b,c,hs,ha,hb,hEmpty,hac,hbc,hcu⟩ := hspecial C hC hCs
    have hnotu : ∀ t : evenVertices G, (t : V) ≠ u := by
      intro t he
      exact (Nat.not_even_iff_odd.mpr hu) (he ▸ t.property)
    have hcC : c ∈ C.supp := by rw [hs]; simp
    have hOavoid := ordinary_empty_component_avoids_finite_mates G F mates hmsupp
      C hEmpty c hcC
    refine Or.inr ⟨a,b,c,hs,hPB C hC a ha,hPB C hC b hb,hac,hbc,
      hnotu a,hnotu b,hnotu c,?_,hcu⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hOavoid e he
    · obtain ⟨v,w,rfl,hv,hw⟩ := hN e he
      have hsep : ∀ t : evenVertices G, (evenSubgraph G).Reachable x t →
          (c : V) ≠ t := by
        intro t ht he
        have hct : c = t := Subtype.val_injective he
        have htC : t ∈ C.supp := hct ▸ hcC
        apply hx C hC
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at htC ⊢
        exact (SimpleGraph.ConnectedComponent.sound ht).trans htC
      exact ⟨hsep v hv,hsep w hw⟩
  · left
    intro t ht
    rcases hregular C hC hCs t ht with htP | ⟨e,he,hte⟩
    · exact Or.inl (hPB C hC t htP)
    · refine Or.inr ⟨((e.1 : V),(e.2 : V)),?_,?_⟩
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨e,
          List.mem_flatMap.mpr ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩)
      · rcases hte with hl | hr
        · exact Or.inl (congrArg Subtype.val hl)
        · exact Or.inr (congrArg Subtype.val hr)

/-- A coherent selected preparation, including special packets, supplies
the actual delayed auxiliary within the protected ceiling budget. All
component floors are derived from its boundary data. -/
theorem bare_delayed_prepared_auxiliary_endpoint
    (h u : V) (x p q : evenVertices G)
    (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (hx : ∀ C ∈ F, x ∉ C.supp)
    (hP : ∀ C ∈ F, P C ⊆ ordinaryComponentPacket G S C)
    (hmsupp : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp)
    (hregular : ∀ C ∈ F, C ∉ special → ∀ t ∈ C.supp,
      t ∈ P C ∨ ∃ e ∈ mates C, t = e.1 ∨ t = e.2)
    (hspecial : ∀ C ∈ F, C ∈ special → ∃ a b c : evenVertices G,
      C.supp = {a,b,c} ∧ a ∈ P C ∧ b ∈ P C ∧ mates C = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u)
    (hu : Odd (G.degree u))
    (hS : ∀ a ∈ S, G.Adj u a.val ∧ a.val ≠ h)
    (K privates : Finset V)
    (hK : ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h)
    (hKprivate : K ⊆ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (N : List (V × V))
    (hNprivate : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates)
    (hNreach : ∀ e ∈ ((x : V),(q : V)) :: N,
      ∃ a b : evenVertices G, e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpdegree : eDegree G p = 2)
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∨ (∃ e ∈ ((x : V),(q : V)) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h) :
    let B := K ∪ ((F.biUnion P).image Subtype.val)
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    Even #B →
    (((x : V),(q : V)) :: (O ++ N)).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) →
    (∀ e ∈ ((x : V),(q : V)) :: (O ++ N),
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2)) →
    (∀ e ∈ ((x : V),(q : V)) :: (O ++ N), e.1 ∉ B ∧ e.2 ∉ B) →
    (∀ e ∈ O ++ N, (p : V) ≠ e.1 ∧ (p : V) ≠ e.2) →
    (∀ a ∈ S, (a : V) ∈ B ∨ ∃ e ∈ O ++ N, (a : V) = e.1 ∨ (a : V) = e.2) →
    ∃ D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s((x : V),(q : V))}) (O ++ N)),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h := by
  classical
  dsimp only
  let B := K ∪ ((F.biUnion P).image Subtype.val)
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  intro hEven hdis hE havoid hpavoid hcover
  have hsupp : ∀ C ∈ F, ∀ a ∈ P C, a ∈ C.supp := by
    intro C hC a ha
    exact (Finset.mem_filter.mp (hP C hC ha)).2
  have hstar := ordinary_private_selected_star_guards G u h S F P hP hS K hK
  have hBlabels : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ a : evenVertices G, a ∈ C.supp ∧ (a : V) = t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Or.inl (hKprivate ht)
    · obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
      exact Or.inr ⟨C,hC,a,hsupp C hC a haP,hat⟩
  have hMlabels := ordinary_finite_private_mate_boundary_labels G F mates hmsupp privates N hNprivate
  have hmembership : ∀ e,
      e ∈ O ++ (((x : V),(q : V)) :: N) ↔
      e ∈ ((x : V),(q : V)) :: (O ++ N) := by
    intro e
    simp only [List.mem_append,List.mem_cons]
    tauto
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ ((x : V),(q : V)) :: (O ++ N), t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t ht he
    rcases hcontact t ht he with htK | ⟨e,he,hte⟩ | ⟨a,ha,hat⟩ | hth
    · exact Or.inl (Finset.mem_union_left _ htK)
    · exact Or.inr (Or.inl ⟨e,(hmembership e).mp (List.mem_append_right O he),hte⟩)
    · rcases hcover a ha with haB | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ haB)
      · exact Or.inr (Or.inl ⟨e,List.mem_cons_of_mem _ he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr hth)
  have hboundary := delayed_ordinary_boundary_from_selected_family G u x hu F special P mates
    hx hmsupp B (fun C hC a ha => Finset.mem_union_right K
      (Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hC,ha⟩,rfl⟩))
    (((x : V),(q : V)) :: N) hNreach hregular hspecial
  have hordinary : ∀ C ∈ F,
      (∀ a : evenVertices G, a ∈ C.supp → (a : V) ∈ B ∨
        ∃ e ∈ ((x : V),(q : V)) :: (O ++ N), (a : V) = e.1 ∨ (a : V) = e.2) ∨
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (a : V) ∈ B ∧ (b : V) ∈ B ∧ G.Adj a c ∧ G.Adj b c ∧
        (a : V) ≠ u ∧ (b : V) ≠ u ∧ (c : V) ≠ u ∧
        (∀ e ∈ ((x : V),(q : V)) :: (O ++ N), (c : V) ≠ e.1 ∧ (c : V) ≠ e.2) ∧
        ¬ G.Adj c u := by
    intro C hC
    rcases hboundary C hC with hr | ⟨a,b,c,hs,ha,hb,hac,hbc,hau,hbu,hcu,hav,hnon⟩
    · left
      intro a ha
      rcases hr a ha with haB | ⟨e,he,hae⟩
      · exact Or.inl haB
      · exact Or.inr ⟨e,(hmembership e).mp he,hae⟩
    · exact Or.inr ⟨a,b,c,hs,ha,hb,hac,hbc,hau,hbu,hcu,
        fun e he => hav e ((hmembership e).mpr he),hnon⟩
  have hnotu : ∀ a : evenVertices G, (a : V) ≠ u := by
    intro a ha
    exact (Nat.not_even_iff_odd.mpr hu) (ha ▸ a.property)
  have huavoid := ordinary_even_mates_avoid_odd_centre G
    (((x : V),(q : V)) :: (O ++ N)) u hu (fun e he => (hE e he).2)
  have hhavoid := even_ended_deletions_avoid_bare_vertex G h
    H.counterexample.1.2.2.2.2.2.1 (((x : V),(q : V)) :: (O ++ N)) hE
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr hu) (he ▸ H.counterexample.1.2.2.2.1)
  have hpetal : ∀ e ∈ O ++ N, (x : V) ≠ e.1 ∧ (x : V) ≠ e.2 ∧
      (p : V) ≠ e.1 ∧ (p : V) ≠ e.2 ∧ (q : V) ≠ e.1 ∧ (q : V) ≠ e.2 := by
    intro e he
    have hd := (List.pairwise_cons.mp hdis).1 e he
    exact ⟨hd.1,hd.2.1,(hpavoid e he).1,(hpavoid e he).2,hd.2.2.1,hd.2.2.2⟩
  exact bare_delayed_auxiliary_endpoint (G := G) h u x p q H B privates (O ++ N) F
    (fun t ht => (hstar.2.2 t ht).1) (fun t ht => (hstar.2.2 t ht).2) hdis
    (fun e he => ⟨(huavoid e he).1,(huavoid e he).2,(havoid e he).1,(havoid e he).2⟩)
    hE hcontacts hBlabels hMlabels hprivates hordinary hu hEven
    (hnotu x) (hnotu p) (hnotu q) hxp hpq (fun he => G.irrefl (he ▸ hpq))
    x.property hpdegree hpetal hhu hstar.2.1 H.counterexample.1.2.1
    (hhavoid ((x : V),(q : V)) (List.mem_cons_self ..)).2
    (fun e he => hhavoid e (List.mem_cons_of_mem _ he))

/-- Native special-packet selection and its actual protected auxiliary.
The contact set is the original set outside the hub component; no selected
preparation or auxiliary decomposition is supplied by the caller. -/
theorem bare_delayed_special_native_auxiliary
    (h u : V) (x p q : evenVertices G)
    (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (S : Finset (evenVertices G))
    (hSdef : S = Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (htouched : ∀ a ∈ S, (evenSubgraph G).connectedComponentMk a ∈ F)
    (hx : ∀ D ∈ F, x ∉ D.supp) (offset : ℕ)
    (hodd : Odd offset) (heven : Even #F)
    (hT2 : (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty)
    (hu : Odd (G.degree u))
    (K privates : Finset V) (hKcard : #K = offset)
    (hKreach : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a)
    (hK : ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h)
    (hKprivate : K ⊆ privates)
    (N : List (V × V))
    (hNdis : (((x : V),(q : V)) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hNreach : ∀ e ∈ ((x : V),(q : V)) :: N,
      ∃ a b : evenVertices G, e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hNE : ∀ e ∈ ((x : V),(q : V)) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hNK : ∀ e ∈ ((x : V),(q : V)) :: N, e.1 ∉ K ∧ e.2 ∉ K)
    (hNprivate : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∨ (∃ e ∈ ((x : V),(q : V)) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpdegree : eDegree G p = 2)
    (hpreach : (evenSubgraph G).Reachable x p)
    (hNp : ∀ e ∈ N, (p : V) ≠ e.1 ∧ (p : V) ≠ e.2) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
    let B := K ∪ ((F.biUnion P).image Subtype.val)
    let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
    #special = 1 ∧ (∀ D ∈ F, P D ⊆ ordinaryComponentPacket G S D) ∧
    (∀ D ∈ F, (mates D).length ≤ 1 ∧
      (∀ e ∈ mates D, G.Adj e.1 e.2 ∧ e.1 ∈ D.supp ∧ e.2 ∈ D.supp ∧
        e.1 ∉ P D ∧ e.2 ∉ P D) ∧
      (∀ e ∈ mates D, ∃ a : evenVertices G,
        D.supp = {a,e.1,e.2} ∧ a ∈ P D ∧ G.Adj a e.1 ∧ G.Adj e.2 a)) ∧
    (∀ D ∈ F, D ∉ special → ∀ t ∈ D.supp,
      t ∈ P D ∨ ∃ e ∈ mates D, t = e.1 ∨ t = e.2) ∧
    (∀ D ∈ F, D ∈ special → ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ a ∈ P D ∧ b ∈ P D ∧ mates D = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u) ∧
    (∀ D ∈ special, ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ G.Adj a b ∧
      (P D).image Subtype.val = {a.val,b.val}) ∧
    (∀ D ∈ F, ∀ e ∈ mates D, e.2 ∉ S) ∧
    #((F.biUnion P).image Subtype.val) = #F +
      2 * #(F.filter (fun D => #(ordinaryComponentPacket G S D) = 3)) + 1 ∧
    Even #B ∧
    ∃ D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s((x : V),(q : V))}) (O ++ N)),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h ∧
      (p.val ∈ K →
        (∀ t, G.Adj p t → Even (G.degree t) → t = x.val ∨ t = q.val) →
        ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u B)
          ((x.val,q.val) :: N)) ⊔ SimpleGraph.edge p.val u),
          E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
          2 ≤ E.endpointCount p.val ∧
          (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
          (∀ t, G.Adj u t → Even (G.degree t) →
            t ∈ K.erase p.val ∪ ((F.biUnion P).image Subtype.val) ∨
            (∃ e ∈ (x.val,q.val) :: N, t = e.1 ∨ t = e.2) ∨
            0 < E.endpointCount t) ∧
          (∀ D ∈ F, D ∉ special →
            (∃ a : evenVertices G, (P D).image Subtype.val = {a.val} ∧
              ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
            (∃ a b c : evenVertices G, D.supp = {a,b,c} ∧
              (P D).image Subtype.val = {a.val} ∧ 2 ≤ E.endpointCount b.val) ∨
            (∃ a b c : evenVertices G, D.supp = {a,b,c} ∧
              G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
              (P D).image Subtype.val = {a.val,b.val,c.val})) ∧
          (2 < #(K.erase p.val) + #F →
            ∃ R : Decomposition (ordinaryMatePuncture G ((x.val,q.val) :: N)),
              R.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ R.endpointCount h ∧
              2 ≤ R.endpointCount p.val ∧ 0 < R.endpointCount u ∧
              ∃ T : Decomposition G, T.size ≤ (Fintype.card V + 1) / 2 ∧
                2 ≤ T.endpointCount h)) := by
  classical
  obtain ⟨special,P,mates,hs,hsOne,hP,hEven,hdata,hregular,hspec,hdonor,
    hdis,hE,havoid,huAvoid,hhAvoid,hcover,hcount⟩ := bare_delayed_special_deletion_bundle G
      h u x H S F hF htouched hx offset hodd heven hT2 hu K hKcard hKreach
      (((x : V),(q : V)) :: N) hNdis hNreach hNE hNK
  let B := K ∪ ((F.biUnion P).image Subtype.val)
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hspecial : ∀ D ∈ F, D ∈ special → ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ a ∈ P D ∧ b ∈ P D ∧ mates D = [] ∧
      G.Adj a c ∧ G.Adj b c ∧ ¬ G.Adj c u := by
    have hs' : special ⊆ F.filter (fun D => #(ordinaryComponentPacket G
        (Finset.univ.filter (fun a : evenVertices G =>
          G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D) = 2) := by
      simpa only [hSdef] using hs
    have hspec' : ∀ D ∈ special, P D = ordinaryComponentPacket G
        (Finset.univ.filter (fun a : evenVertices G =>
          G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)) D ∧ mates D = [] := by
      simpa only [hSdef] using hspec
    intro D _ hDs
    exact bare_delayed_special_family_labels h u x H C hxC F special hx P mates
      hs' hspec' D hDs
  obtain ⟨hhead,hmembership⟩ := disjoint_deletion_spoke_to_head O N
    ((x : V),(q : V)) hdis
  have hmsupp : ∀ D ∈ F, ∀ e ∈ mates D, e.1 ∈ D.supp ∧ e.2 ∈ D.supp := by
    intro D hD e he
    have hd := (hdata D hD).2.1 e he
    exact ⟨hd.2.1,hd.2.2.1⟩
  have hOavoid : ∀ e ∈ O, (p : V) ≠ e.1 ∧ (p : V) ≠ e.2 := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨D,hD,hfD⟩ := List.mem_flatMap.mp hf
    have hDF := Finset.mem_toList.mp hD
    have hd := hmsupp D hDF f hfD
    have hsep : ∀ a : evenVertices G, a ∈ D.supp → (p : V) ≠ a := by
      intro a ha he
      have hpa : p = a := Subtype.val_injective he
      have hpD : p ∈ D.supp := hpa ▸ ha
      apply hx D hDF
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hpD ⊢
      exact (SimpleGraph.ConnectedComponent.sound hpreach).trans hpD
    exact ⟨hsep f.1 hd.1,hsep f.2 hd.2⟩
  have hS : ∀ a ∈ S, G.Adj u a.val ∧ a.val ≠ h := by
    intro a ha
    rw [hSdef] at ha
    have hd := (Finset.mem_filter.mp ha).2
    exact ⟨hd.1,hd.2.2⟩
  have hstarShape : ∀ D ∈ special, ∃ a b c : evenVertices G,
      D.supp = {a,b,c} ∧ G.Adj a b ∧
      (P D).image Subtype.val = {a.val,b.val} := by
    apply bare_delayed_special_family_star_shape h u x H C hxC F special hx P
    · simpa only [hSdef] using hs
    · intro D hD
      simpa only [hSdef] using (hspec D hD).1
  refine ⟨special,P,mates,hsOne,hP,hdata,hregular,hspecial,hstarShape,
    hdonor,hcount,hEven,?_⟩
  have haux := bare_delayed_prepared_auxiliary_endpoint G h u x p q H S F special P mates
    hx hP hmsupp hregular hspecial hu hS K privates hK hKprivate hprivates
    N hNprivate hNreach hxp hpq hpdegree hcontact hEven hhead
    (fun e he => hE e ((hmembership e).mpr he))
    (fun e he => havoid e ((hmembership e).mpr he))
    (by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hOavoid e he
      · exact hNp e he)
  have hcoverage : ∀ a ∈ S, a.val ∈ B ∨
      ∃ e ∈ O ++ N, a.val = e.1 ∨ a.val = e.2 := by
    intro a ha
    rcases hcover a ha with haB | ⟨e,he,hae⟩
    · exact Or.inl haB
    · have he' := (hmembership e).mp he
      rcases List.mem_cons.mp he' with heq | heO
      · subst e
        have haX : (a : V) ≠ (x : V) := by
          intro he
          have hax : a = x := Subtype.val_injective he
          rw [hSdef] at ha
          have hanot := (Finset.mem_filter.mp ha).2.2.1
          exact hanot (hax ▸ hxC)
        rcases hae with heX | heQ
        · exact False.elim (haX heX)
        · have hqNot : ¬ ∃ a ∈ S, (a : V) = (q : V) := by
            intro hqS
            obtain ⟨b,hb,hbq⟩ := hqS
            rw [hSdef] at hb
            have hbnot := (Finset.mem_filter.mp hb).2.2.1
            have hbq' : b = q := Subtype.val_injective hbq
            have hqC : q ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC
              (show (evenSubgraph G).Adj x q from
                (hNE ((x : V),(q : V)) (List.mem_cons_self ..)).1)
            exact hbnot (hbq' ▸ hqC)
          exact False.elim (hqNot ⟨a,ha,heQ⟩)
      · exact Or.inr ⟨e,heO,hae⟩
  obtain ⟨D,hsize,hh⟩ := haux hcoverage
  refine ⟨D,hsize,hh,?_⟩
  intro hpK hpair
  have hadjB : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact (hK t ht).1
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨D,hD,haP⟩ := Finset.mem_biUnion.mp ha
      exact (hS a (Finset.mem_filter.mp (hP D hD haP)).1).1
  have hevenB : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact (hK t ht).2.1
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ht
      exact a.property
  have hpacket : ∀ e ∈ O, ∃ (D : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      D.supp = {a,b,c} ∧ (a : V) ∈ B := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    obtain ⟨D,hD,hfD⟩ := List.mem_flatMap.mp hf
    have hDF := Finset.mem_toList.mp hD
    obtain ⟨a,hsupp,ha,_,_⟩ := (hdata D hDF).2.2 f hfD
    exact ⟨D,a,f.1,f.2,rfl,hsupp,Finset.mem_union_right K
      (Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨D,hDF,ha⟩,rfl⟩)⟩
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr hu) (he ▸ H.counterexample.1.2.2.2.1)
  have hg := ordinaryMatePuncture_ordered_spoke (G := starPuncture G u B)
    x.val q.val O N
  have htransport : ∀ {J L : SimpleGraph V} (e : J = L) (D : Decomposition J),
      (e ▸ D).size = D.size ∧
        ∀ t, (e ▸ D).endpointCount t = D.endpointCount t := by
    intro J L e D
    subst L
    exact ⟨rfl,fun _ => rfl⟩
  let D0 := hg ▸ D
  have hs0 : D0.size ≤ (Fintype.card V + 1) / 2 := by
    rw [(htransport hg D).1]
    exact hsize
  have hh0 : 2 ≤ D0.endpointCount h := by
    rw [(htransport hg D).2 h]
    exact hh
  obtain ⟨E,hsE,hhE,hpE,_,hrec,_⟩ := restore_delayed_protected_prefix
    (G := G) h u x.val p.val q.val B O N hadjB hevenB hu hEven
    (Finset.mem_union_left _ hpK) hdis
    (fun e he => ⟨(huAvoid e he).1,(huAvoid e he).2,
      (havoid e he).1,(havoid e he).2⟩) hE hpacket hpair hhu
    (hK p.val hpK).2.2.symm
    (fun e he => hhAvoid e (List.mem_append_left _ he)) D0 hs0 hh0
  have hremaining : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K.erase p.val ∪ ((F.biUnion P).image Subtype.val) ∨
      (∃ e ∈ (x.val,q.val) :: N, t = e.1 ∨ t = e.2) ∨
      0 < E.endpointCount t := by
    intro t hut htG
    rcases hcontact t hut htG with htK | hm | ⟨a,ha,hat⟩ | hth
    · by_cases htp : t = p.val
      · right; right; rw [htp]; omega
      · exact Or.inl (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨htp,htK⟩))
    · exact Or.inr (Or.inl hm)
    · have hD := htouched a ha
      have haD : a ∈ ((evenSubgraph G).connectedComponentMk a).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      have hcoverContact : a ∈ P ((evenSubgraph G).connectedComponentMk a) ∨
          ∃ e ∈ mates ((evenSubgraph G).connectedComponentMk a),
            a = e.1 ∨ a = e.2 := by
        by_cases hspecialD : (evenSubgraph G).connectedComponentMk a ∈ special
        · left
          rw [(hspec _ hspecialD).1]
          exact Finset.mem_filter.mpr ⟨ha,haD⟩
        · exact hregular _ hD hspecialD a haD
      rcases hcoverContact with haP | ⟨e,he,hae⟩
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨a,Finset.mem_biUnion.mpr ⟨_,hD,haP⟩,hat⟩))
      · rcases hae with hal | har
        · right; right
          rw [← hat,hal]
          have heO : ((e.1 : V),(e.2 : V)) ∈ O := List.mem_map.mpr
            ⟨e,List.mem_flatMap.mpr ⟨_,Finset.mem_toList.mpr hD,he⟩,rfl⟩
          have hr : 2 ≤ E.endpointCount (e.1 : V) := hrec _ heO
          omega
        · exact False.elim ((hdonor _ hD e he) (har ▸ ha))
    · right; right; rw [hth]; omega
  have hsupp : ∀ D ∈ F, ∀ a ∈ P D, a ∈ D.supp := by
    intro D hD a ha
    exact (Finset.mem_filter.mp (hP D hD ha)).2
  have hregularE : ∀ D ∈ F, D ∉ special →
      (∃ a : evenVertices G, (P D).image Subtype.val = {a.val} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, D.supp = {a,b,c} ∧
        (P D).image Subtype.val = {a.val} ∧ 2 ≤ E.endpointCount b.val) ∨
      (∃ a b c : evenVertices G, D.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P D).image Subtype.val = {a.val,b.val,c.val}) := by
    intro D hD hDs
    obtain ⟨w,hw,hwDeq⟩ := Finset.mem_image.mp (hF hD)
    have hwD : w ∈ D.supp := by
      rw [← hwDeq]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    apply bare_ordinary_restored_regular_shape h x w H S D (hx D hD) hwD hw
      (P D) (mates D) (hsupp D hD) (hregular D hD hDs)
      (fun e he => ⟨((hdata D hD).2.1 e he).2.2.2.1,
        ((hdata D hD).2.1 e he).2.2.2.2⟩)
      (fun e he => by
        obtain ⟨a,ha,haP,_,_⟩ := (hdata D hD).2.2 e he
        exact ⟨a,ha,haP⟩) _ E
    intro e he
    exact hrec ((e.1 : V),(e.2 : V)) (List.mem_map.mpr
      ⟨e,List.mem_flatMap.mpr ⟨D,Finset.mem_toList.mpr hD,he⟩,rfl⟩)
  refine ⟨E,hsE,hhE,hpE,hrec,hremaining,hregularE,?_⟩
  intro hcountMixed
  let L := (F.biUnion P).image Subtype.val
  have hKL : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro t ht hm
    obtain ⟨a,hat,hr⟩ := hKreach t ht
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hm
    obtain ⟨D,hD,hbP⟩ := Finset.mem_biUnion.mp hb
    have hab : a = b := Subtype.val_injective (hat.trans hbt.symm)
    subst b
    have haD := hsupp D hD a hbP
    apply hx D hD
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haD ⊢
    exact (SimpleGraph.ConnectedComponent.sound hr).trans haD
  have hpL : p.val ∉ L := fun ht => Finset.disjoint_left.mp hKL hpK ht
  have htailAvoid := fun e he => havoid e (List.mem_append_right O he)
  have htailU := fun e he => huAvoid e (List.mem_append_right O he)
  have htailE := fun e he => hE e (List.mem_append_right O he)
  have hpB : p.val ∈ B := Finset.mem_union_left _ hpK
  have hgMixed := delayed_reserved_contact_remaining_graph G u p.val K L
    ((x.val,q.val) :: N) hpK hpL hadjB
    (fun e he => ⟨fun heq => (htailAvoid e he).1 (heq ▸ hpB),
      fun heq => (htailAvoid e he).2 (heq ▸ hpB)⟩)
  let E0 := hgMixed ▸ E
  have hcontactMixed : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K.erase p.val ∪ L ∨
      (∃ e ∈ (x.val,q.val) :: N, t = e.1 ∨ t = e.2) ∨
      0 < E0.endpointCount t := by
    intro t hut ht
    rw [(htransport hgMixed E).2]
    exact hremaining t hut ht
  have hcapL : ∀ t ∈ L, eDegree G t ≤ 2 := by
    intro t ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    obtain ⟨D,hD,haP⟩ := Finset.mem_biUnion.mp ha
    have hd := bare_ordinary_degree_zero_or_two x a h H D (hx D hD)
      (hsupp D hD a haP)
    subst t
    omega
  have hprivate : ∀ w ∈ K.erase p.val, ∃ a, ∀ t,
      G.Adj w t → Even (G.degree t) → t = x.val ∨ t = a := by
    intro w hw
    have hwK := Finset.mem_of_mem_erase hw
    let a : evenVertices G := ⟨w,(hK w hwK).2.1⟩
    have haw : G.Adj w x := (hprivates w (hKprivate hwK)).1
    obtain ⟨b,_,_,_,hb⟩ := bare_hub_neighbor_even_successor h x a H haw.ne haw.symm
    exact ⟨b,hb⟩
  have hW : (K ∪ L).erase p.val = K.erase p.val ∪ L := by
    rw [Finset.erase_union_distrib,Finset.erase_eq_of_notMem hpL]
  have hOdd : Odd #(K.erase p.val ∪ L) := by
    have hc := Finset.card_erase_add_one hpB
    change #((K ∪ L).erase p.val) + 1 = #(K ∪ L) at hc
    change Even #(K ∪ L) at hEven
    rw [hW] at hc
    rw [Nat.even_iff] at hEven
    rw [Nat.odd_iff]
    omega
  have hregularMixed := hregularE
  have hepMixed := (htransport hgMixed E).2
  simp only [← hepMixed] at hregularMixed
  have hWB : K.erase p.val ∪ L ⊆ B :=
    Finset.union_subset_union (Finset.erase_subset _ _) (Finset.Subset.refl _)
  obtain ⟨R,hsR,huR,hkeepR⟩ := return_delayed_prepared_mixed_star
    (G := G) u x.val q.val (K.erase p.val) L N F special P rfl hsupp
    (hKL.mono_left (Finset.erase_subset _ _)) (by omega) hOdd
    (fun t ht => hadjB t (hWB ht)) (fun t ht => hevenB t (hWB ht)) hNdis
    (fun e he => ⟨(htailU e he).1,(htailU e he).2,
      fun ht => (htailAvoid e he).1 (hWB ht),
      fun ht => (htailAvoid e he).2 (hWB ht)⟩)
    htailE hprivate hcapL E0 hcontactMixed hregularMixed
    (fun D _ hDs => hstarShape D hDs)
  have hsBudget : R.size ≤ (Fintype.card V + 1) / 2 := by
    rw [hsR,(htransport hgMixed E).1]
    exact hsE
  have hhReserve : 2 ≤ R.endpointCount h := by
    have hhB : h ∉ B := by
      intro ht
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (hK h ht).2.2 rfl
      · obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
        obtain ⟨D,hD,haP⟩ := Finset.mem_biUnion.mp ha
        exact (hS a (Finset.mem_filter.mp (hP D hD haP)).1).2 hat
    rw [hkeepR h hhu (fun ht => hhB (hWB ht)),(htransport hgMixed E).2]
    exact hhE
  have hpReserve : 2 ≤ R.endpointCount p.val := by
    have hpW : p.val ∉ K.erase p.val ∪ L := by
      simpa only [Finset.mem_union,Finset.notMem_erase,false_or] using hpL
    have hpu : p.val ≠ u := by
      intro he
      exact G.irrefl (he ▸ (hK p.val hpK).1)
    rw [hkeepR p.val hpu hpW,(htransport hgMixed E).2]
    exact hpE
  refine ⟨R,hsBudget,hhReserve,hpReserve,huR,?_⟩
  have hheadN := (List.pairwise_cons.mp hNdis).1
  have hneutralPair : ∀ e ∈ N, ∀ t, G.Adj e.2 t → Even (G.degree t) →
      t = x.val ∨ t = e.1 := by
    intro e he
    have hg := hNE e (List.mem_cons_of_mem _ he)
    have hv := hprivates e.2 (hNprivate e he).2
    exact even_neighbors_pair_of_degree_two e.2 x e.1 hv.2
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨hv.1,x.property⟩)
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨hg.1.symm,hg.2.1⟩)
      (hheadN e he).1
  have hspoke := hNE (x.val,q.val) (List.mem_cons_self ..)
  have hqEV : (evenSubgraph G).Adj x q := hspoke.1
  have hqdeg := bare_hub_private_eDegree_eq_two h x q H hqEV.reachable hspoke.1.ne.symm
  have hqpair := even_neighbors_pair_of_degree_two q.val x p hqdeg
    ((mem_evenNeighbors (G := G) _ _).mpr ⟨hspoke.1.symm,x.property⟩)
    ((mem_evenNeighbors (G := G) _ _).mpr ⟨hpq.symm,p.property⟩) hxp.ne
  obtain ⟨T,hsT,hkeepT⟩ := return_delayed_original_mates_and_spoke G
    x.val q.val p.val u N hNdis hNE hNp
    (fun e he => ⟨(htailU e (List.mem_cons_of_mem _ he)).1.symm,
      (htailU e (List.mem_cons_of_mem _ he)).2.symm⟩)
    hneutralPair hqpair R hpReserve huR
  refine ⟨T,hsT ▸ hsBudget,?_⟩
  have hhx : h ≠ x.val := H.counterexample.1.2.1
  have hhq : h ≠ q.val :=
    (hhAvoid (x.val,q.val) (List.mem_append_right O (List.mem_cons_self ..))).2
  rw [hkeepT h hhx hhq (fun e he =>
    hhAvoid e (List.mem_append_right O (List.mem_cons_of_mem _ he)))]
  exact hhReserve

/-- Native parity-compatible deletion supplies the protected auxiliary. -/
theorem bare_delayed_native_auxiliary_endpoint
    (h u : V) (x p q : evenVertices G)
    (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G))
    (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (htouched : ∀ a ∈ S, (evenSubgraph G).connectedComponentMk a ∈ F)
    (hx : ∀ C ∈ F, x ∉ C.supp) (offset : ℕ)
    (hevenOffset : Even (offset + #F))
    (hu : Odd (G.degree u))
    (hS : ∀ a ∈ S, G.Adj u a.val ∧ a.val ≠ h)
    (K privates : Finset V) (hKcard : #K = offset)
    (hKreach : ∀ t ∈ K, ∃ a : evenVertices G,
      (a : V) = t ∧ (evenSubgraph G).Reachable x a)
    (hK : ∀ t ∈ K, G.Adj u t ∧ Even (G.degree t) ∧ t ≠ h)
    (hKprivate : K ⊆ privates)
    (N : List (V × V))
    (hNdis : (((x : V),(q : V)) :: N).Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2))
    (hNreach : ∀ e ∈ ((x : V),(q : V)) :: N,
      ∃ a b : evenVertices G, e = ((a : V),(b : V)) ∧
      (evenSubgraph G).Reachable x a ∧ (evenSubgraph G).Reachable x b)
    (hNE : ∀ e ∈ ((x : V),(q : V)) :: N,
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2))
    (hNK : ∀ e ∈ ((x : V),(q : V)) :: N, e.1 ∉ K ∧ e.2 ∉ K)
    (hNprivate : ∀ e ∈ N, e.1 ∈ privates ∧ e.2 ∈ privates)
    (hprivates : ∀ t ∈ privates, G.Adj t x ∧ eDegree G t = 2)
    (hcontact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K ∨ (∃ e ∈ ((x : V),(q : V)) :: N, t = e.1 ∨ t = e.2) ∨
      (∃ a ∈ S, (a : V) = t) ∨ t = h)
    (hxp : G.Adj x p) (hpq : G.Adj p q) (hpdegree : eDegree G p = 2)
    (hpreach : (evenSubgraph G).Reachable x p)
    (hNp : ∀ e ∈ N, (p : V) ≠ e.1 ∧ (p : V) ≠ e.2) :
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
    #((F.biUnion P).image Subtype.val) = #F +
      2 * #(F.filter (fun C => #(ordinaryComponentPacket G S C) = 3)) ∧ Even #B ∧
    ∃ D : Decomposition (ordinaryMatePuncture
      ((starPuncture G u B).deleteEdges {s((x : V),(q : V))}) (O ++ N)),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount h ∧
      ((p : V) ∈ K →
        (∀ t, G.Adj p t → Even (G.degree t) → t = (x : V) ∨ t = (q : V)) →
        ∃ E : Decomposition ((ordinaryMatePuncture (starPuncture G u B)
          (((x : V),(q : V)) :: N)) ⊔ SimpleGraph.edge (p : V) u),
          E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount h ∧
          2 ≤ E.endpointCount p ∧ (∀ e ∈ O, 2 ≤ E.endpointCount e.1) ∧
          (∀ C ∈ F,
            (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
              ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
            (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
              (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ E.endpointCount b) ∨
            (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
              G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
              (P C).image Subtype.val = {(a : V),(b : V),(c : V)})) ∧
          (∀ t, G.Adj u t → Even (G.degree t) →
            t ∈ K.erase (p : V) ∪ ((F.biUnion P).image Subtype.val) ∨
            (∃ e ∈ (((x : V),(q : V)) :: N), t = e.1 ∨ t = e.2) ∨
            0 < E.endpointCount t) ∧
          (∀ w ∈ K.erase (p : V), ∃ a, ∀ t,
            G.Adj w t → Even (G.degree t) → t = (x : V) ∨ t = a) ∧
          (1 < #(K.erase (p : V)) + #F →
            ∃ R : Decomposition (ordinaryMatePuncture G (((x : V),(q : V)) :: N)),
              R.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ R.endpointCount h ∧
              2 ≤ R.endpointCount p ∧ 0 < R.endpointCount u ∧
              ∃ T : Decomposition G, T.size ≤ (Fintype.card V + 1) / 2 ∧
                2 ≤ T.endpointCount h) ∧
          (#K = 1 → (1 < #F ∨ #((F.biUnion P).image Subtype.val) = 1) →
            ∃ R : Decomposition ((ordinaryMatePuncture (starPuncture G u
              ((F.biUnion P).image Subtype.val)) (((x : V),(q : V)) :: N)) ⊔
              ((F.biUnion P).image Subtype.val).sup (SimpleGraph.edge u)),
              R.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ R.endpointCount h ∧
                2 ≤ R.endpointCount p ∧ 0 < R.endpointCount u ∧
                ∃ T : Decomposition G, T.size ≤ (Fintype.card V + 1) / 2 ∧
                  2 ≤ T.endpointCount h)) := by
  classical
  obtain ⟨P,mates,hP,hdata,hdonor,hlocal,hEven,hdis,hE,havoid,huAvoid,hhAvoid,hcover,hpacketCount⟩ :=
    bare_delayed_native_deletion_bundle G h u x H S F hF hx offset hevenOffset hu
      K hKcard hKreach (((x : V),(q : V)) :: N) hNdis hNreach hNE hNK
  let B := K ∪ ((F.biUnion P).image Subtype.val)
  let O := (F.toList.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V)))
  have hsupp : ∀ C ∈ F, ∀ a ∈ P C, a ∈ C.supp := by
    intro C hC a ha
    exact (Finset.mem_filter.mp (hP C hC ha)).2
  have hmates : ∀ C ∈ F, ∀ e ∈ mates C, e.1 ∈ C.supp ∧ e.2 ∈ C.supp := by
    intro C hC e he
    have ht := (hdata C hC).2.1 e he
    exact ⟨ht.2.1,ht.2.2.1⟩
  obtain ⟨hhead,hmembership⟩ := disjoint_deletion_spoke_to_head O N
    ((x : V),(q : V)) hdis
  have hstar := ordinary_private_selected_star_guards G u h S F P hP hS K hK
  have hBlabels : ∀ t ∈ B, t ∈ privates ∨
      ∃ C ∈ F, ∃ a : evenVertices G, a ∈ C.supp ∧ (a : V) = t := by
    intro t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Or.inl (hKprivate ht)
    · obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
      exact Or.inr ⟨C,hC,a,hsupp C hC a haP,hat⟩
  have hMlabels := ordinary_finite_private_mate_boundary_labels G F mates
    hmates privates N hNprivate
  have hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ B ∨ (∃ e ∈ ((x : V),(q : V)) :: (O ++ N), t = e.1 ∨ t = e.2) ∨ t = h := by
    intro t hadj heven
    rcases hcontact t hadj heven with ht | ⟨e,he,hte⟩ | ⟨a,ha,hat⟩ | ht
    · exact Or.inl (Finset.mem_union_left _ ht)
    · exact Or.inr (Or.inl ⟨e,(hmembership e).mp (List.mem_append_right O he),hte⟩)
    · have hC := htouched a ha
      have haC : a ∈ ((evenSubgraph G).connectedComponentMk a).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      rcases hcover _ hC a haC with haB | ⟨e,he,hae⟩
      · exact Or.inl (hat ▸ haB)
      · exact Or.inr (Or.inl ⟨e,(hmembership e).mp he,hat ▸ hae⟩)
    · exact Or.inr (Or.inr ht)
  have hordinary : ∀ C ∈ F, ∀ a : evenVertices G, a ∈ C.supp →
      (a : V) ∈ B ∨ ∃ e ∈ ((x : V),(q : V)) :: (O ++ N),
        (a : V) = e.1 ∨ (a : V) = e.2 := by
    intro C hC a ha
    rcases hcover C hC a ha with haB | ⟨e,he,hae⟩
    · exact Or.inl haB
    · exact Or.inr ⟨e,(hmembership e).mp he,hae⟩
  have hOavoid : ∀ a : evenVertices G, (evenSubgraph G).Reachable x a →
      ∀ e ∈ O, (a : V) ≠ e.1 ∧ (a : V) ≠ e.2 := by
    intro a hr e he
    obtain ⟨f,hf,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    have hab := hmates C hCF f hfC
    have hsep : ∀ b : evenVertices G, b ∈ C.supp → (a : V) ≠ b := by
      intro b hb heq
      have heqab : a = b := Subtype.val_injective heq
      have haC : a ∈ C.supp := heqab ▸ hb
      apply hx C hCF
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
      exact (SimpleGraph.ConnectedComponent.sound hr).trans haC
    exact ⟨hsep f.1 hab.1,hsep f.2 hab.2⟩
  have hpetal : ∀ e ∈ O ++ N, (x : V) ≠ e.1 ∧ (x : V) ≠ e.2 ∧
      (p : V) ≠ e.1 ∧ (p : V) ≠ e.2 ∧ (q : V) ≠ e.1 ∧ (q : V) ≠ e.2 := by
    intro e he
    have hxq := (List.pairwise_cons.mp hhead).1 e he
    have hp : (p : V) ≠ e.1 ∧ (p : V) ≠ e.2 := by
      rcases List.mem_append.mp he with he | he
      · exact hOavoid p hpreach e he
      · exact hNp e he
    exact ⟨hxq.1,hxq.2.1,hp.1,hp.2,hxq.2.2.1,hxq.2.2.2⟩
  have hEvenH : Even (G.degree h) := H.counterexample.1.2.2.2.1
  have hhu : h ≠ u := by
    intro hh
    exact (Nat.not_even_iff_odd.mpr hu) (hh ▸ hEvenH)
  have hnotu : ∀ a : evenVertices G, (a : V) ≠ u := by
    intro a ha
    exact (Nat.not_even_iff_odd.mpr hu) (ha ▸ a.property)
  have hhx : h ≠ (x : V) := H.counterexample.1.2.1
  have hhq : h ≠ (q : V) := (hhAvoid ((x : V),(q : V))
    (List.mem_append_right O (List.mem_cons_self ..))).2
  refine ⟨P,mates,hP,hdata,hdonor,hpacketCount,hEven,?_⟩
  obtain ⟨D,hsize,hh⟩ := bare_delayed_auxiliary_endpoint (G := G) h u x p q H B privates (O ++ N) F
    (fun t ht => (hstar.2.2 t ht).1) (fun t ht => (hstar.2.2 t ht).2)
    hhead
    (fun e he => ⟨(huAvoid e ((hmembership e).mpr he)).1,
      (huAvoid e ((hmembership e).mpr he)).2,
      (havoid e ((hmembership e).mpr he)).1,
      (havoid e ((hmembership e).mpr he)).2⟩)
    (fun e he => hE e ((hmembership e).mpr he))
    hcontacts hBlabels hMlabels hprivates (fun C hC => Or.inl (hordinary C hC))
    hu hEven (hnotu x) (hnotu p) (hnotu q) hxp hpq
    (fun hp => G.irrefl (hp ▸ hpq)) x.property hpdegree hpetal hhu hstar.2.1 hhx hhq
    (fun e he => hhAvoid e ((hmembership e).mpr (List.mem_cons_of_mem _ he)))
  refine ⟨D,hsize,hh,?_⟩
  intro hpK hpair
  have hpB : (p : V) ∈ B := Finset.mem_union_left _ hpK
  have hpacket : ∀ e ∈ O, ∃ (C : (evenSubgraph G).ConnectedComponent)
      (a b c : evenVertices G), e = ((b : V),(c : V)) ∧
      C.supp = {a,b,c} ∧ (a : V) ∈ B := by
    intro e he
    obtain ⟨f,hf,heq⟩ := List.mem_map.mp he
    subst e
    obtain ⟨C,hC,hfC⟩ := List.mem_flatMap.mp hf
    have hCF := Finset.mem_toList.mp hC
    obtain ⟨a,hs,ha,_,_⟩ := (hdata C hCF).2.2 f hfC
    exact ⟨C,a,f.1,f.2,rfl,hs,Finset.mem_union_right K
      (Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨C,hCF,ha⟩,rfl⟩)⟩
  have hg := ordinaryMatePuncture_ordered_spoke (G := starPuncture G u B)
    (x : V) (q : V) O N
  have htransport : ∀ {J L : SimpleGraph V} (e : J = L) (D : Decomposition J),
      (e ▸ D).size = D.size ∧
        ∀ t, (e ▸ D).endpointCount t = D.endpointCount t := by
    intro J L e D
    subst L
    exact ⟨rfl,fun _ => rfl⟩
  let D0 := hg ▸ D
  have hsize0 : D0.size ≤ (Fintype.card V + 1) / 2 := by
    rw [(htransport hg D).1]
    exact hsize
  have hh0 : 2 ≤ D0.endpointCount h := by
    rw [(htransport hg D).2 h]
    exact hh
  obtain ⟨E,hs,hp,_,hrec,hkeep⟩ := restore_delayed_ordinary_prefix_and_private
    (G := G) u x p q B O N
    (fun t ht => (hstar.2.2 t ht).1) (fun t ht => (hstar.2.2 t ht).2)
    hu hEven hpB hdis
    (fun e he => ⟨(huAvoid e he).1,(huAvoid e he).2,
      (havoid e he).1,(havoid e he).2⟩) hE hpacket hpair D0
  have hhp : h ≠ (p : V) := (hK p hpK).2.2.symm
  have hhO : ∀ e ∈ O, h ≠ e.1 ∧ h ≠ e.2 :=
    fun e he => hhAvoid e (List.mem_append_left _ he)
  have hhE : 2 ≤ E.endpointCount h := (hkeep h hhO hhu hhp) ▸ hh0
  have hregular : ∀ C ∈ F,
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ E.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)}) := by
    intro C hC
    obtain ⟨w,hw,hwCeq⟩ := Finset.mem_image.mp (hF hC)
    have hwC : w ∈ C.supp := by
      rw [← hwCeq]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
    apply bare_ordinary_restored_regular_shape h x w H S C (hx C hC) hwC hw
      (P C) (mates C) (hsupp C hC) (hlocal C hC)
      (fun e he => ⟨((hdata C hC).2.1 e he).2.2.2.1,
        ((hdata C hC).2.1 e he).2.2.2.2⟩)
      (fun e he => by
        obtain ⟨a,ha,haP,_,_⟩ := (hdata C hC).2.2 e he
        exact ⟨a,ha,haP⟩) _ E
    intro e he
    exact hrec ((e.1 : V),(e.2 : V)) (List.mem_map.mpr
      ⟨e,List.mem_flatMap.mpr ⟨C,Finset.mem_toList.mpr hC,he⟩,rfl⟩)
  have hremainingContact : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ K.erase (p : V) ∪ ((F.biUnion P).image Subtype.val) ∨
      (∃ e ∈ (((x : V),(q : V)) :: N), t = e.1 ∨ t = e.2) ∨
      0 < E.endpointCount t := by
    intro t hut htG
    rcases hcontact t hut htG with htK | hm | ⟨a,ha,hat⟩ | hth
    · by_cases htp : t = (p : V)
      · right; right; rw [htp]; omega
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨htp,htK⟩))
    · exact Or.inr (Or.inl hm)
    · have hC := htouched a ha
      have haC : a ∈ ((evenSubgraph G).connectedComponentMk a).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      rcases hlocal _ hC a haC with haP | ⟨e,he,hae⟩
      · exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨a,Finset.mem_biUnion.mpr ⟨_,hC,haP⟩,hat⟩))
      · rcases hae with hal | har
        · right; right
          rw [← hat,hal]
          have heO : ((e.1 : V),(e.2 : V)) ∈ O := List.mem_map.mpr
            ⟨e,List.mem_flatMap.mpr ⟨_,Finset.mem_toList.mpr hC,he⟩,rfl⟩
          have hr : 2 ≤ E.endpointCount (e.1 : V) := hrec _ heO
          omega
        · exact False.elim ((hdonor _ hC e he) (har ▸ ha))
    · right; right; rw [hth]; omega
  have hremainingPrivate : ∀ w ∈ K.erase (p : V), ∃ a, ∀ t,
      G.Adj w t → Even (G.degree t) → t = (x : V) ∨ t = a := by
    intro w hw
    have hwK := Finset.mem_of_mem_erase hw
    let a : evenVertices G := ⟨w,(hK w hwK).2.1⟩
    have haw : G.Adj w x := (hprivates w (hKprivate hwK)).1
    obtain ⟨b,_,_,_,hb⟩ := bare_hub_neighbor_even_successor h x a H haw.ne haw.symm
    exact ⟨b,hb⟩
  have hmixedReturn : 1 < #(K.erase (p : V)) + #F →
      ∃ R : Decomposition (ordinaryMatePuncture G (((x : V),(q : V)) :: N)),
        R.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ R.endpointCount h ∧
        2 ≤ R.endpointCount p ∧ 0 < R.endpointCount u ∧
        ∃ T : Decomposition G, T.size ≤ (Fintype.card V + 1) / 2 ∧
          2 ≤ T.endpointCount h := by
    intro hcountMixed
    let L := (F.biUnion P).image Subtype.val
    have hKL : Disjoint K L := by
      apply Finset.disjoint_left.mpr
      intro t ht hm
      obtain ⟨a,hat,hr⟩ := hKreach t ht
      obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp hm
      obtain ⟨C,hC,hbP⟩ := Finset.mem_biUnion.mp hb
      have hab : a = b := Subtype.val_injective (hat.trans hbt.symm)
      subst b
      have haC := hsupp C hC a hbP
      apply hx C hC
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at haC ⊢
      exact (SimpleGraph.ConnectedComponent.sound hr).trans haC
    have hpL : (p : V) ∉ L := fun ht => Finset.disjoint_left.mp hKL hpK ht
    have htailAvoid := fun e he => havoid e (List.mem_append_right O he)
    have htailU := fun e he => huAvoid e (List.mem_append_right O he)
    have htailE := fun e he => hE e (List.mem_append_right O he)
    have hgMixed := delayed_reserved_contact_remaining_graph G u (p : V) K L
      (((x : V),(q : V)) :: N) hpK hpL
      (fun t ht => (hstar.2.2 t ht).1)
      (fun e he => ⟨fun heq => (htailAvoid e he).1 (heq ▸ hpB),
        fun heq => (htailAvoid e he).2 (heq ▸ hpB)⟩)
    let E0 := hgMixed ▸ E
    have hcontactMixed : ∀ t, G.Adj u t → Even (G.degree t) →
        t ∈ K.erase (p : V) ∪ L ∨
        (∃ e ∈ (((x : V),(q : V)) :: N), t = e.1 ∨ t = e.2) ∨
        0 < E0.endpointCount t := by
      intro t hut he
      rw [(htransport hgMixed E).2]
      exact hremainingContact t hut he
    have hcapL : ∀ t ∈ L, eDegree G t ≤ 2 := by
      intro t ht
      obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
      obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
      have hd := bare_ordinary_degree_zero_or_two x a h H C (hx C hC) (hsupp C hC a haP)
      subst t
      omega
    have hregularMixed := hregular
    have hepMixed := (htransport hgMixed E).2
    simp only [← hepMixed] at hregularMixed
    obtain ⟨R,hsR,huR,hkeepR⟩ := return_delayed_remaining_mixed_star G u x q p K L N F P
      rfl hsupp hpK hpL hKL hEven hcountMixed
      (fun t ht => (hstar.2.2 t ht).1) (fun t ht => (hstar.2.2 t ht).2) hNdis
      (fun e he => ⟨(htailU e he).1,(htailU e he).2,
        (htailAvoid e he).1,(htailAvoid e he).2⟩)
      htailE hremainingPrivate hcapL E0 hcontactMixed hregularMixed
    have hsBudget : R.size ≤ (Fintype.card V + 1) / 2 := by
      rw [hsR,(htransport hgMixed E).1,hs]; exact hsize0
    have hhReserve : 2 ≤ R.endpointCount h := by
      have hhW : h ∉ K.erase (p : V) ∪ L := by
        intro ht
        apply hstar.2.1
        rcases Finset.mem_union.mp ht with ht | ht
        · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase ht)
        · exact Finset.mem_union_right _ ht
      rw [hkeepR h hhu hhW,(htransport hgMixed E).2]
      exact hhE
    have hpReserve : 2 ≤ R.endpointCount p := by
      have hpW : (p : V) ∉ K.erase (p : V) ∪ L := by
        simp only [Finset.mem_union,Finset.notMem_erase, false_or]
        exact hpL
      rw [hkeepR p (hnotu p) hpW,(htransport hgMixed E).2]
      exact hp
    refine ⟨R,hsBudget,hhReserve,hpReserve,huR,?_⟩
    have hheadN := (List.pairwise_cons.mp hNdis).1
    have hneutralPair : ∀ e ∈ N, ∀ t, G.Adj e.2 t → Even (G.degree t) →
        t = (x : V) ∨ t = e.1 := by
      intro e he
      have hg := hNE e (List.mem_cons_of_mem _ he)
      have hv := hprivates e.2 (hNprivate e he).2
      exact even_neighbors_pair_of_degree_two e.2 x e.1 hv.2
        ((mem_evenNeighbors (G := G) _ _).mpr ⟨hv.1,x.property⟩)
        ((mem_evenNeighbors (G := G) _ _).mpr ⟨hg.1.symm,hg.2.1⟩) (hheadN e he).1
    have hspoke := hNE ((x : V),(q : V)) (List.mem_cons_self ..)
    have hqEV : (evenSubgraph G).Adj x q := hspoke.1
    have hqdeg := bare_hub_private_eDegree_eq_two h x q H hqEV.reachable hspoke.1.ne.symm
    have hqpair := even_neighbors_pair_of_degree_two (q : V) x p hqdeg
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨hspoke.1.symm,x.property⟩)
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨hpq.symm,p.property⟩) hxp.ne
    obtain ⟨T,hsT,hkeepT⟩ := return_delayed_original_mates_and_spoke G x q p u N
      hNdis hNE hNp
      (fun e he => ⟨(htailU e (List.mem_cons_of_mem _ he)).1.symm,
        (htailU e (List.mem_cons_of_mem _ he)).2.symm⟩)
      hneutralPair hqpair R hpReserve huR
    refine ⟨T,hsT ▸ hsBudget,?_⟩
    rw [hkeepT h hhx hhq (fun e he =>
      hhAvoid e (List.mem_append_right O (List.mem_cons_of_mem _ he)))]
    exact hhReserve
  refine ⟨E,hs ▸ hsize0,hhE,hp,hrec,hregular,hremainingContact,hremainingPrivate,hmixedReturn,?_⟩
  intro hKone hcount
  let L := (F.biUnion P).image Subtype.val
  have hpL : (p : V) ∉ L := by
    intro ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
    have hap : a = p := Subtype.val_injective hat
    have hpC : p ∈ C.supp := hap ▸ hsupp C hC a haP
    apply hx C hC
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hpC ⊢
    exact (SimpleGraph.ConnectedComponent.sound hpreach).trans hpC
  have hKsingle : K = {(p : V)} := by
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp hKone
    have hpt : (p : V) = t := by simpa [ht] using hpK
    simpa [hpt] using ht
  have hBL : B.erase (p : V) = L := by
    change (K ∪ L).erase (p : V) = L
    rw [hKsingle,Finset.singleton_union]
    ext t
    simp only [Finset.mem_erase,Finset.mem_insert]
    constructor
    · rintro ⟨hne,heq | ht⟩
      · exact False.elim (hne heq)
      · exact ht
    · intro ht
      exact ⟨fun heq => hpL (heq ▸ ht),Or.inr ht⟩
  have hoddL : Odd #L := by
    have hcard : #B = 1 + #L := by
      change #(K ∪ L) = _
      rw [hKsingle,Finset.singleton_union,Finset.card_insert_of_notMem hpL]
      omega
    rw [Nat.even_iff,hcard] at hEven
    rw [Nat.odd_iff]
    omega
  have htAvoid := fun e he => havoid e (List.mem_append_right O he)
  have htU := fun e he => huAvoid e (List.mem_append_right O he)
  have htE := fun e he => hE e (List.mem_append_right O he)
  have hpTail : ∀ e ∈ (((x : V),(q : V)) :: N), (p : V) ≠ e.1 ∧ (p : V) ≠ e.2 := by
    intro e he
    have hav := htAvoid e he
    exact ⟨fun ht => hav.1 (ht ▸ hpB),fun ht => hav.2 (ht ▸ hpB)⟩
  have hgraph := ordinaryMatePuncture_restore_star_leaf (G := G) u (p : V) B
    (((x : V),(q : V)) :: N) hstar.1 hpB (hstar.2.2 p hpB).1 hpTail
  rw [hBL] at hgraph
  let E0 := hgraph ▸ E
  have hcontact0 : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ L ∨ (∃ e ∈ (((x : V),(q : V)) :: N), t = e.1 ∨ t = e.2) ∨
        0 < E0.endpointCount t := by
    intro t hut htG
    rcases hcontact t hut htG with htK | hm | ⟨a,ha,hat⟩ | hth
    · have htp : t = (p : V) := by simpa [hKsingle] using htK
      right; right
      rw [(htransport hgraph E).2,htp]
      omega
    · exact Or.inr (Or.inl hm)
    · have hC := htouched a ha
      have haC : a ∈ ((evenSubgraph G).connectedComponentMk a).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      rcases hlocal _ hC a haC with haP | ⟨e,he,hae⟩
      · exact Or.inl (Finset.mem_image.mpr
          ⟨a,Finset.mem_biUnion.mpr ⟨_,hC,haP⟩,hat⟩)
      · have heO : ((e.1 : V),(e.2 : V)) ∈ O := List.mem_map.mpr
          ⟨e,List.mem_flatMap.mpr ⟨_,Finset.mem_toList.mpr hC,he⟩,rfl⟩
        rcases hae with hal | har
        · right; right
          rw [(htransport hgraph E).2,← hat,hal]
          have hr : 2 ≤ E.endpointCount (e.1 : V) := hrec _ heO
          omega
        · exact False.elim ((hdonor _ hC e he) (har ▸ ha))
    · right; right
      rw [(htransport hgraph E).2,hth]
      omega
  have hcapL : ∀ t ∈ L, eDegree G t ≤ 2 := by
    intro t ht
    obtain ⟨a,ha,hat⟩ := Finset.mem_image.mp ht
    obtain ⟨C,hC,haP⟩ := Finset.mem_biUnion.mp ha
    have hd := bare_ordinary_degree_zero_or_two x a h H C (hx C hC) (hsupp C hC a haP)
    subst t
    omega
  have hregular0 := hregular
  have hep := (htransport hgraph E).2
  simp only [← hep] at hregular0
  have hrestore : ∃ R : Decomposition
      ((ordinaryMatePuncture (starPuncture G u L) (((x : V),(q : V)) :: N)) ⊔
        L.sup (SimpleGraph.edge u)),
      R.size = E0.size ∧ 0 < R.endpointCount u ∧
        ∀ t, t ≠ u → t ∉ L → R.endpointCount t = E0.endpointCount t := by
    rcases hcount with hcount | hsingle
    · exact restore_delayed_ordinary_only_star G u x q L N F P
        rfl hsupp hcount hoddL
        (fun t ht => (hstar.2.2 t (Finset.mem_union_right K ht)).1)
        (fun t ht => (hstar.2.2 t (Finset.mem_union_right K ht)).2) hNdis
        (fun e he => ⟨(htU e he).1,(htU e he).2,
          fun ht => (htAvoid e he).1 (Finset.mem_union_right K ht),
          fun ht => (htAvoid e he).2 (Finset.mem_union_right K ht)⟩)
        htE hcapL E0 hcontact0 hregular0
    · obtain ⟨a,haL⟩ := Finset.card_eq_one.mp hsingle
      have hadjL : G.Adj u a :=
        (hstar.2.2 a (Finset.mem_union_right K (haL ▸ Finset.mem_singleton_self a))).1
      have hevenL : Even (G.degree a) :=
        (hstar.2.2 a (Finset.mem_union_right K (haL ▸ Finset.mem_singleton_self a))).2
      change (F.biUnion P).image Subtype.val = {a} at haL
      have hgS : ordinaryMatePuncture (starPuncture G u L) (((x : V),(q : V)) :: N) =
          ordinaryMatePuncture (starPuncture G u {a}) (((x : V),(q : V)) :: N) := by
        dsimp only [L]; rw [haL]
      let E1 := hgS ▸ E0
      have hc1 : ∀ t, G.Adj u t → Even (G.degree t) →
          t ∈ ({a} : Finset V) ∨ (∃ e ∈ (((x : V),(q : V)) :: N), t = e.1 ∨ t = e.2) ∨
          0 < E1.endpointCount t := by
        intro t ht he
        rw [(htransport hgS E0).2]
        simpa only [L,haL] using hcontact0 t ht he
      obtain ⟨R,hsingleSize,hupos,hkeep⟩ :=
        restore_delayed_single_ordinary_contact G u a x q N hadjL hevenL hNdis
          (fun e he => ⟨(htU e he).1,(htU e he).2,
            fun ht => (htAvoid e he).1 (Finset.mem_union_right K (haL.symm ▸ ht)),
            fun ht => (htAvoid e he).2 (Finset.mem_union_right K (haL.symm ▸ ht))⟩)
          htE E1 hc1
      have hgR : (ordinaryMatePuncture (starPuncture G u {a}) (((x : V),(q : V)) :: N)) ⊔
          SimpleGraph.edge u a =
          (ordinaryMatePuncture (starPuncture G u L) (((x : V),(q : V)) :: N)) ⊔
            L.sup (SimpleGraph.edge u) := by
        dsimp only [L]; rw [haL,Finset.sup_singleton]
      refine ⟨hgR ▸ R,?_,?_,?_⟩
      · rw [(htransport hgR R).1,hsingleSize,(htransport hgS E0).1]
      · rw [(htransport hgR R).2]; exact hupos
      · intro t htu htL
        have hta : t ≠ a := by
          intro hta; apply htL; dsimp only [L]; rw [haL,hta]; simp
        rw [(htransport hgR R).2,hkeep t htu hta,(htransport hgS E0).2]
  obtain ⟨R,hsizeR,huR,hkeepR⟩ := hrestore
  have hhL : h ∉ L := fun ht => hstar.2.1 (Finset.mem_union_right K ht)
  have hsR : R.size ≤ (Fintype.card V + 1) / 2 := by
    rw [hsizeR,(htransport hgraph E).1,hs]
    exact hsize0
  have hhR : 2 ≤ R.endpointCount h := by
    rw [hkeepR h hhu hhL,(htransport hgraph E).2]
    exact hhE
  have hpR : 2 ≤ R.endpointCount p := by
    rw [hkeepR p (hnotu p) hpL,(htransport hgraph E).2]
    exact hp
  refine ⟨R,hsR,hhR,hpR,huR,?_⟩
  have hgraphR : (ordinaryMatePuncture (starPuncture G u L)
      (((x : V),(q : V)) :: N)) ⊔ L.sup (SimpleGraph.edge u) =
      ordinaryMatePuncture (G.deleteEdges {s((x : V),(q : V))}) N := by
    rw [ordinaryMatePuncture_return_star G u L _
      (fun t ht => (hstar.2.2 t (Finset.mem_union_right K ht)).1)
      (fun t ht e he => ⟨fun hte => (htAvoid e he).1
        (hte ▸ Finset.mem_union_right K ht),fun hte => (htAvoid e he).2
        (hte ▸ Finset.mem_union_right K ht)⟩)]
    rw [ordinaryMatePuncture_deleteEdges_comm]
    rfl
  let R0 := hgraphR ▸ R
  have hpR0 : 2 ≤ R0.endpointCount p := by
    rw [(htransport hgraphR R).2]; exact hpR
  have huR0 : 0 < R0.endpointCount u := by
    rw [(htransport hgraphR R).2]; exact huR
  have hspoke := hNE ((x : V),(q : V)) (List.mem_cons_self ..)
  have hsingle : [((x : V),(q : V))].Pairwise (fun e f =>
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) := by simp
  have hsingleE : ∀ e ∈ [((x : V),(q : V))],
      G.Adj e.1 e.2 ∧ Even (G.degree e.1) ∧ Even (G.degree e.2) := by
    intro e he
    simp only [List.mem_singleton] at he
    subst e
    exact hspoke
  have hprofileFinal := ordinaryMatePuncture_even_preserved (G := G)
    [((x : V),(q : V))] hsingle hsingleE
  have hxOddFinal := (ordinaryMatePuncture_endpoints_odd (G := G)
    [((x : V),(q : V))] hsingle hsingleE ((x : V),(q : V)) (by simp)).1
  obtain ⟨hheadN,hdisN⟩ := List.pairwise_cons.mp hNdis
  have hneutral : ∀ e ∈ N,
      (G.deleteEdges {s((x : V),(q : V))}).Adj e.1 e.2 ∧
      Even ((G.deleteEdges {s((x : V),(q : V))}).degree e.1) ∧
      Even ((G.deleteEdges {s((x : V),(q : V))}).degree e.2) := by
    intro e he
    have hn := hheadN e he
    have heG := hNE e (List.mem_cons_of_mem _ he)
    refine ⟨?_,?_,?_⟩
    · exact (ordinaryMatePuncture_adj_of_avoids (G := G)
        [((x : V),(q : V))] e.1 e.2 (by
          intro f hf
          simp only [List.mem_singleton] at hf
          subst f
          exact ⟨hn.1.symm,hn.2.2.1.symm⟩)).mpr heG.1
    · rw [degree_delete_edge_of_ne G x q e.1 hn.1.symm hn.2.2.1.symm]
      exact heG.2.1
    · rw [degree_delete_edge_of_ne G x q e.2 hn.2.1.symm hn.2.2.2.symm]
      exact heG.2.2
  have hneutralPair : ∀ e ∈ N, ∀ t,
      G.Adj e.2 t → Even (G.degree t) → t = (x : V) ∨ t = e.1 := by
    intro e he
    have heG := hNE e (List.mem_cons_of_mem _ he)
    have hxpriv := hprivates e.2 (hNprivate e he).2
    exact even_neighbors_pair_of_degree_two e.2 x e.1 hxpriv.2
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨hxpriv.1,x.property⟩)
      ((mem_evenNeighbors (G := G) _ _).mpr ⟨heG.1.symm,heG.2.1⟩)
      (hheadN e he).1
  have hqEV : (evenSubgraph G).Adj x q := hspoke.1
  have hqdeg := bare_hub_private_eDegree_eq_two h x q H hqEV.reachable hspoke.1.ne.symm
  have hqpair := even_neighbors_pair_of_degree_two (q : V) x p hqdeg
    ((mem_evenNeighbors (G := G) _ _).mpr ⟨hspoke.1.symm,x.property⟩)
    ((mem_evenNeighbors (G := G) _ _).mpr ⟨hpq.symm,p.property⟩) hxp.ne
  obtain ⟨T,hsizeT,hkeepT⟩ := restore_delayed_mates_and_final_spoke (R := G)
    x q p u N hspoke.1 hprofileFinal hxOddFinal hdisN
    (fun e he => by
      simpa only [← SimpleGraph.ncard_neighborSet] using hneutral e he)
    (fun e he => ⟨(hheadN e he).1,(hheadN e he).2.1⟩) hNp
    (fun e he => ⟨(htU e (List.mem_cons_of_mem _ he)).1.symm,
      (htU e (List.mem_cons_of_mem _ he)).2.symm⟩)
    hneutralPair hqpair R0 hpR0 huR0
  refine ⟨T,?_,?_⟩
  · rw [hsizeT,(htransport hgraphR R).1]
    exact hsR
  · rw [hkeepT h hhx hhq (fun e he =>
      hhAvoid e (List.mem_append_right O (List.mem_cons_of_mem _ he))),
      (htransport hgraphR R).2]
    exact hhR

end Gallai.TwoException
