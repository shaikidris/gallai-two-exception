/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.PrescribedRetainedEdge
public import Gallai.TwoException.PrescribedCut
public import Gallai.TwoException.AdjacentHubOddSingleton

@[expose] public section

/-! # Connectivity of leaf-side retained-star punctures -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [DecidableEq V]

/-- A star puncture remains connected when its core outside h,w is
connected, hw survives, and a surviving spoke joins h to that core.
No connectivity of G-h is assumed. -/
theorem starPuncture_connected_with_leaf
    (G : SimpleGraph V) (h w : V) (S : Finset V)
    (hc : (G.induce {v | v ≠ h ∧ v ≠ w}).Connected)
    (hhw : (starPuncture G h S).Adj h w)
    (hret : ∃ v, v ≠ h ∧ v ≠ w ∧ (starPuncture G h S).Adj h v) :
    (starPuncture G h S).Connected := by
  have : Nonempty V := ⟨h⟩
  let J := starPuncture G h S
  let f : (G.induce {v | v ≠ h ∧ v ≠ w}) →g J :=
    { toFun := Subtype.val
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_⟩
        intro hs
        exact b.property.1 ((star_sup_adj_off_center h S a b a.property.1).mp hs).2 }
  obtain ⟨v, hvh, hvw, hv⟩ := hret
  have reach (a : V) : J.Reachable h a := by
    by_cases hah : a = h
    · subst a; exact SimpleGraph.Reachable.refl _
    · by_cases haw : a = w
      · subst a; exact hhw.reachable
      · exact hv.reachable.trans ((hc.preconnected ⟨v, hvh, hvw⟩ ⟨a, hah, haw⟩).map f)
  exact ⟨fun a b => (reach a).symm.trans (reach b)⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The odd leaf spoke and one retained even spoke connect the partial
even-star puncture through the connected core of a leaf-edge cut. -/
theorem retained_evenStar_connected_with_leaf (h w v : V)
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hv : v ∈ evenNeighbors G h) :
    (starPuncture G h ((evenNeighbors G h).erase v)).Connected := by
  classical
  let S := (evenNeighbors G h).erase v
  have hS : S ⊆ evenNeighbors G h := Finset.erase_subset _ _
  have hhS : h ∉ S := fun ha => (show h ∉ evenNeighbors G h by simp) (hS ha)
  have hwS : w ∉ S := by
    intro ha
    exact (Nat.not_even_iff_odd.mpr hwOdd) ((mem_evenNeighbors h w).mp (hS ha)).2
  obtain ⟨hhv, hvEven⟩ := (mem_evenNeighbors h v).mp hv
  have hvw : v ≠ w := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hwOdd) hvEven
  apply starPuncture_connected_with_leaf G h w S hc
  · refine ⟨hhw, ?_⟩
    intro hs
    exact hwS ((star_sup_adj_center h S hhS w).mp hs)
  · refine ⟨v, hhv.ne.symm, hvw, hhv, ?_⟩
    intro hs
    exact (Finset.notMem_erase v _) ((star_sup_adj_center h S hhS v).mp hs)

/-- A connected core and odd leaf close the positive-even E-degree
leaf-cut branch by the same retained-spoke induction and restoration as
the non-cut case, without assuming G-h connected. -/
theorem prescribed_retained_leaf_cut (h x w v : V)
    (hhne : h ≠ x) (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x) (hv : v ∈ evenNeighbors G h)
    (hpar : Even (eDegree G h))
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ t, Even (J.degree t) → t ≠ a → t ≠ b → eDegree J t ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  exact prescribed_retained_edge_of_connected_puncture h x v hhne hhEven hxEven hhx hv
    hpar (retained_evenStar_connected_with_leaf G h w v hc hhw hwOdd hv) hcap hind

/-- Any ceiling budget on the full odd-star puncture restores the original
graph while exposing h twice. This applies to disconnected budgets as well
as connected one-exception budgets. -/
theorem prescribed_odd_star_of_budget (h x : V)
    (hhEven : Even (G.degree h)) (hhx : ¬ G.Adj h x)
    (ho : Odd (eDegree G h))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hbudget : HasPathBudget (evenStarPuncture G h) ((Fintype.card V + 1) / 2)) :
    BareConclusion G h := by
  obtain ⟨D, hd⟩ := hbudget
  have hleaf (a : V) (ha : a ∈ evenNeighbors G h) : eDegree G a ≤ 3 := by
    obtain ⟨hadj, he⟩ := (mem_evenNeighbors h a).mp ha
    exact hcap a he hadj.ne.symm (by rintro rfl; exact hhx hadj)
  obtain ⟨E, hs, hh⟩ := D.restore_odd_even_star_exposing h hhEven ho hleaf
  exact ⟨E, by omega, hh⟩

/-- If a full even-star puncture retains an ordinary core neighbour, its
connected one-exception budget closes the odd-E-degree leaf-cut branch. -/
theorem prescribed_odd_leaf_cut_with_core_neighbor (h x w v : V)
    (hhne : h ≠ x) (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hxpos : 0 < G.degree x) (hhx : ¬ G.Adj h x)
    (ho : Odd (eDegree G h))
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hhv : G.Adj h v) (hvw : v ≠ w) (hvOdd : Odd (G.degree v))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    BareConclusion G h := by
  classical
  let S := evenNeighbors G h
  let J := evenStarPuncture G h
  let : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hhS : h ∉ S := by simp [S]
  have hretain (a : V) (ha : G.Adj h a) (he : Odd (G.degree a)) : J.Adj h a := by
    refine ⟨ha, ?_⟩
    intro hs
    have ham : a ∈ S := (star_sup_adj_center h S hhS a).mp hs
    exact (Nat.not_even_iff_odd.mpr he) ((mem_evenNeighbors h a).mp ham).2
  have hconn : J.Connected := starPuncture_connected_with_leaf G h w S hc
    (hretain w hhw hwOdd) ⟨v, hhv.ne.symm, hvw, hretain v hhv hvOdd⟩
  have hxS : x ∉ S := by
    intro ha
    exact hhx ((mem_evenNeighbors h x).mp ha).1
  have hdx : J.degree x = G.degree x := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G h S x hhne.symm hxS
  have hcapJ := partialEvenStar_cap_two_exceptions G h x S (by rfl) hhEven ho hcap
  obtain ⟨D, hd, _⟩ := one_exception_endpoint J x hconn
    (by rwa [hdx]) (by rwa [hdx]) hcapJ
  exact prescribed_odd_star_of_budget G h x hhEven hhx ho hcap ⟨D, hd⟩

/-- A connected closed core with one positive even exception, together with
an isolated single-edge component, fits the original ceiling budget. -/
theorem prescribed_closed_core_singleton_budget (h w x : V)
    (hhw : G.Adj h w)
    (hhonly : ∀ a, G.Adj h a → a = w)
    (hwonly : ∀ a, G.Adj w a → a = h)
    (hxcore : x ≠ h ∧ x ≠ w)
    (hxpos : 0 < G.degree x) (hxEven : Even (G.degree x))
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hcap : ∀ a, Even (G.degree a) → a ≠ x → eDegree G a ≤ 3) :
    HasPathBudget G ((Fintype.card V + 1) / 2) := by
  classical
  let U : Set V := {a | a ≠ h ∧ a ≠ w}
  let K := G.induce U
  have hclosed (a : V) (ha : a ∈ U) : G.neighborSet a ⊆ U := by
    intro b hab
    constructor
    · intro hb; subst b
      exact ha.2 (hhonly a hab.symm)
    · intro hb; subst b
      exact ha.1 (hwonly a hab.symm)
  have hdeg (a : U) : K.degree a = G.degree a :=
    SimpleGraph.degree_induce_of_neighborSet_subset (hclosed a a.property)
  have hcapK (a : U) (ha : Even (K.degree a))
      (hax : a ≠ ⟨x, hxcore⟩) : eDegree K a ≤ 3 := by
    rw [eDegree_induce_of_closed G U hclosed]
    exact hcap a (by rwa [← hdeg a]) (fun he => hax (Subtype.ext he))
  obtain ⟨D, hd, _⟩ := one_exception_endpoint K ⟨x, hxcore⟩ hc
    (by rwa [hdeg]) (by rwa [hdeg]) hcapK
  let R := K.spanningCoe
  have hRadj (a b : V) : R.Adj a b ↔ a ∈ U ∧ b ∈ U ∧ G.Adj a b := by
    change (K.map (Function.Embedding.subtype _)).Adj a b ↔ _
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨a', b', hab, rfl, rfl⟩
      exact ⟨a'.property, b'.property, hab⟩
    · rintro ⟨ha, hb, hab⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, rfl, rfl⟩
  have hR : R.support ⊆ U := by
    rintro a ⟨b, hab⟩
    exact (hRadj a b).mp hab |>.1
  have hmap : K.map (Function.Embedding.subtype _) = R := by
    rfl
  let E : Decomposition R := hmap ▸ D.map (Function.Embedding.subtype _)
  have he : E.size = D.size := by rfl
  have hdis : Disjoint R.edgeSet (SimpleGraph.edge h w).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e hr hw
    rw [SimpleGraph.edgeSet_edge_of_ne hhw.ne] at hw
    subst e
    exact (hR ⟨w, hr⟩).1 rfl
  obtain ⟨F, hf, _⟩ := union_singleton_edge R E h w hhw.ne hdis
  have hgraph : R ⊔ SimpleGraph.edge h w = G := by
    ext a b
    rw [SimpleGraph.sup_adj, hRadj, SimpleGraph.edge_adj]
    constructor
    · rintro (⟨ha, hb, hab⟩ | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
      · exact hab
      · exact hhw
      · exact hhw.symm
    · intro hab
      by_cases hah : a = h
      · subst a; right; exact ⟨Or.inl ⟨rfl, hhonly b hab⟩, hab.ne⟩
      by_cases haw : a = w
      · subst a; right; exact ⟨Or.inr ⟨rfl, hwonly b hab⟩, hab.ne⟩
      left
      exact ⟨⟨hah, haw⟩, hclosed a ⟨hah, haw⟩ hab, hab⟩
  have hpair : Fintype.card {a : V // a = h ∨ a = w} = 2 := by
    simp [Fintype.card_subtype, Finset.filter_or, Finset.filter_eq', hhw.ne]
  have hcard : Fintype.card U + 2 = Fintype.card V := by
    have hp := Fintype.card_subtype_compl (fun a : V => a = h ∨ a = w)
    have hp' : Fintype.card U = Fintype.card V - 2 := by
      have heq : Fintype.card U = Fintype.card {a : V // ¬ (a = h ∨ a = w)} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (fun a => by simp [U]))
      rw [heq, hp, hpair]
    have htwo : 2 ≤ Fintype.card V := by
      rw [← hpair]
      exact Fintype.card_subtype_le _
    omega
  have hout : HasPathBudget (R ⊔ SimpleGraph.edge h w) ((Fintype.card V + 1) / 2) :=
    ⟨F, by omega⟩
  rwa [hgraph] at hout

/-- When the odd leaf is the only originally odd neighbour of the hub,
the full odd-star puncture is its singleton spoke plus the connected core.
Its native component budget restores the prescribed hub within the ceiling. -/
theorem prescribed_odd_leaf_cut_without_core_neighbor (h x w : V)
    (hhne : h ≠ x) (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hxpos : 0 < G.degree x) (hhx : ¬ G.Adj h x)
    (ho : Odd (eDegree G h))
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hwleaf : ∀ a, G.Adj w a → a = h)
    (hcoreEven : ∀ a, G.Adj h a → a ≠ w → Even (G.degree a))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    BareConclusion G h := by
  classical
  let S := evenNeighbors G h
  let J := evenStarPuncture G h
  let : DecidableRel J.Adj := fun _ _ => Classical.propDecidable _
  have hhS : h ∉ S := by simp [S]
  have hwS : w ∉ S := by
    intro ha
    exact (Nat.not_even_iff_odd.mpr hwOdd) ((mem_evenNeighbors h w).mp ha).2
  have hkeep : J.Adj h w := by
    refine ⟨hhw, ?_⟩
    intro hs
    exact hwS ((star_sup_adj_center h S hhS w).mp hs)
  have hhonly (a : V) (ha : J.Adj h a) : a = w := by
    by_contra haw
    have haS : a ∈ S := (mem_evenNeighbors h a).mpr
      ⟨ha.1, hcoreEven a ha.1 haw⟩
    exact ha.2 ((star_sup_adj_center h S hhS a).mpr haS)
  have hwonly (a : V) (ha : J.Adj w a) : a = h := hwleaf a ha.1
  have hxw : x ≠ w := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hwOdd) hxEven
  have hxS : x ∉ S := by
    intro ha
    exact hhx ((mem_evenNeighbors h x).mp ha).1
  have hdx : J.degree x = G.degree x := by
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', J] using
      starPuncture_degree_other G h S x hhne.symm hxS
  have hcore : (J.induce {a | a ≠ h ∧ a ≠ w}).Connected := by
    have heq := induce_evenStarPuncture_eq_of_notMem G h
      {a | a ≠ h ∧ a ≠ w} (by simp)
    change ((evenStarPuncture G h).induce _).Connected
    rwa [heq]
  have hcapJ := partialEvenStar_cap_two_exceptions G h x S (by rfl) hhEven ho hcap
  have hb := prescribed_closed_core_singleton_budget J h w x hkeep hhonly hwonly
    ⟨hhne.symm, hxw⟩ (by rwa [hdx]) (by rwa [hdx]) hcore hcapJ
  exact prescribed_odd_star_of_budget G h x hhEven hhx ho hcap hb

/-- The odd-E-degree leaf-cut branch is exhaustive: either an originally
odd core neighbour survives, or the puncture is the isolated leaf edge plus
the connected core. No decomposition certificate is supplied. -/
theorem prescribed_odd_leaf_cut (h x w : V)
    (hhne : h ≠ x) (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hxpos : 0 < G.degree x) (hhx : ¬ G.Adj h x)
    (ho : Odd (eDegree G h))
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hwleaf : ∀ a, G.Adj w a → a = h)
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    BareConclusion G h := by
  classical
  by_cases hex : ∃ v, G.Adj h v ∧ v ≠ w ∧ Odd (G.degree v)
  · obtain ⟨v, hv, hvw, hoV⟩ := hex
    exact prescribed_odd_leaf_cut_with_core_neighbor G h x w v hhne hhEven hxEven
      hxpos hhx ho hc hhw hwOdd hv hvw hoV hcap
  · apply prescribed_odd_leaf_cut_without_core_neighbor G h x w hhne hhEven hxEven
      hxpos hhx ho hc hhw hwOdd hwleaf ?_ hcap
    intro a ha haw
    exact Nat.not_odd_iff_even.mp (fun hoa => hex ⟨a, ha, haw, hoa⟩)

/-- Complete leaf-cut reduction for a nonadjacent pair of possible
exceptions. Only the positive-even E-degree case uses strict edge induction. -/
theorem prescribed_leaf_cut_reducible (h x w : V)
    (hconn : G.Connected) (hhne : h ≠ x)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hhx : ¬ G.Adj h x)
    (hc : (G.induce {a | a ≠ h ∧ a ≠ w}).Connected)
    (hhw : G.Adj h w) (hwOdd : Odd (G.degree w))
    (hwleaf : ∀ a, G.Adj w a → a = h)
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3)
    (hind : ∀ (J : SimpleGraph V) [DecidableRel J.Adj],
      J.edgeFinset.card < G.edgeFinset.card → J.Connected →
      ∀ a b : V, a ≠ b → 0 < J.degree a → Even (J.degree a) →
      Even (J.degree b) →
      (∀ t, Even (J.degree t) → t ≠ a → t ≠ b → eDegree J t ≤ 3) →
      BareConclusion J a) : BareConclusion G h := by
  classical
  by_cases hxpos : 0 < G.degree x
  · by_cases hz : eDegree G h = 0
    · exact bare_endpoint h x
        ⟨hconn, hhne, hhw.degree_pos_left, hhEven, hxEven, hz, hcap⟩
    · by_cases he : Even (eDegree G h)
      · obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < eDegree G h by omega)
        exact prescribed_retained_leaf_cut G h x w v hhne hhEven hxEven hhx hv
          he hc hhw hwOdd hcap hind
      · exact prescribed_odd_leaf_cut G h x w hhne hhEven hxEven hxpos hhx
          (Nat.not_even_iff_odd.mp he) hc hhw hwOdd hwleaf hcap
  · apply one_exception_endpoint G h hconn hhw.degree_pos_left hhEven
    intro a ha hah
    by_cases hax : a = x
    · subst a
      have hb := eDegree_le_degree (G := G) x
      omega
    · exact hcap a ha hah hax

end Gallai.TwoException
