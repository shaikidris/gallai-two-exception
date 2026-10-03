/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactSets
public import Gallai.TwoException.ContactE1

@[expose] public section

/-! # Native single-petal contact reconstruction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def windmillContacts (x : evenVertices G) (u : V) :
    Finset {a : evenVertices G // (evenSubgraph G).Adj x a} :=
  Finset.univ.filter fun a => G.Adj u a.val.val

def ambientWindmillContacts (x : evenVertices G) (u : V) : Finset V :=
  windmillPrivateSet x (windmillContacts x u)

noncomputable local instance nativeE1StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance nativeE1DeleteAdj (u v x q : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert v S)).deleteEdges {s(x,q)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Native E1 chooses its single petal and derives all private caps,
mate-neighbour and protected-vertex guards. Only the reserved-edge locality
and decomposition reserves remain supplied by the enclosing schedule. -/
theorem bare_windmill_restore_E1
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u v : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (ho : Odd #(singleContactPetals f P (windmillContacts x u)))
    (huOdd : Odd (G.degree u)) (huv : u ≠ v) (huvAdj : G.Adj u v)
    (hux : ¬ G.Adj u x) (hvx : ¬ G.Adj v x) (hhv : h ≠ v)
    (hseparate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      ¬ G.Adj v a.val.val) :
    ∃ p : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      ∀ D : Decomposition
        ((starPuncture G u (insert v (ambientWindmillContacts x u))).deleteEdges
          {s((x : V),(f p).val.val)}),
        (∀ t, G.Adj u t → t ∉ ambientWindmillContacts x u →
          Odd (G.degree t) ∨ 0 < D.endpointCount t) →
        (∀ t, (starPuncture G u (insert v (ambientWindmillContacts x u))).Adj v t →
          0 < D.endpointCount t) →
        ∃ F : Decomposition G, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
          F.endpointCount v = D.endpointCount v + 1 ∧
          F.endpointCount h = D.endpointCount h := by
  classical
  have hpos : 0 < #(singleContactPetals f P (windmillContacts x u)) := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  obtain ⟨p, _, hp, hq⟩ := single_contact_orientation f hinv P (windmillContacts x u) r hr
  refine ⟨p, hp, hq, ?_⟩
  intro D hretained hvpositive
  let S := ambientWindmillContacts x u
  have hcap := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hxS : (x : V) ∉ S := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have hpS : p.val.val ∈ S :=
    (mem_windmillPrivateSet x (windmillContacts x u) p.val.val).mpr ⟨p, hp, rfl⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).1 ho
  have hxu : (x : V) ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ x.property)
  have hxv : (x : V) ≠ v := by
    intro he
    exact hux (he.symm ▸ huvAdj)
  have hqu : ¬ G.Adj (f p).val.val u := by
    intro hadj
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩)
  have hqv : ¬ G.Adj (f p).val.val v := fun hadj => hseparate (f p) hadj.symm
  have hqne : (f p).val.val ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ (f p).val.property)
  have hqvne : (f p).val.val ≠ v := by
    intro he
    exact hvx (he ▸ (f p).property.symm)
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) v).mp hv
    exact hvx (ha ▸ a.property.symm)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, _, hhbare, _⟩
  have hhu : h ≠ u := by
    intro he
    exact (Nat.not_even_iff_odd.mpr huOdd) (he ▸ hhEven)
  have hhprivate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      h ≠ a.val.val := by
    intro a he
    have hd := bare_windmillPrivateSet_leaf_guards h x H ({a} : Finset _)
      a.val.val ((mem_windmillPrivateSet x {a} a.val.val).mpr ⟨a, by simp, rfl⟩)
    rw [← he, hhbare] at hd
    omega
  have hhS : h ∉ S := by
    intro hh
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp hh
    exact hhprivate a ha.symm
  exact restore_contact_E1 u v x p.val.val (f p).val.val p.val.val h S
    hstar.1 hvS huv huOdd hodd huvAdj hstar.2
    (fun t ht => (hcap t ht).1) hpS hpS
    (fun t ht _ => (hcap t ht).2.le)
    (fun t ht => by
      obtain ⟨a, _, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp ht
      exact hseparate a)
    hxu hxv hxS hqu hqv hqne hqvne (f p).property x.property
    (by
      intro t ht he
      simpa only [hinv p] using
        bare_windmill_private_even_neighbors h x H f hedge (f p) t ht he)
    hvx hux hhu hhv hhx (hhprivate (f p)) hhS D hretained hvpositive

end Gallai.TwoException
