/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactE1
public import Gallai.TwoException.ContactE4

@[expose] public section

/-! # Native retained single-petal contact reconstruction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance nativeE4StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance nativeE4DeleteAdj (u v q p : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert v S)).deleteEdges {s(q,p)}).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Native E4 retains the single contact and prescribes the hub inward.
The mate edge preparation and every private guard come from its petal. -/
theorem bare_windmill_restore_E4
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
    (huxAdj : G.Adj u x) (hxv : (x : V) ≠ v)
    (hvx : ¬ G.Adj v x) (hhv : h ≠ v)
    (hseparate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      ¬ G.Adj v a.val.val) :
    ∃ p : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      ∀ D : Decomposition
        ((starPuncture G u (insert v
          (insert (x : V) ((ambientWindmillContacts x u).erase p.val.val)))).deleteEdges
          {s((f p).val.val,p.val.val)}),
        (∀ t, G.Adj u t →
          t ∉ insert (x : V) ((ambientWindmillContacts x u).erase p.val.val) →
          t ≠ p.val.val → Odd (G.degree t) ∨ 0 < D.endpointCount t) →
        (∀ t, (starPuncture G u (insert v
          (insert (x : V) ((ambientWindmillContacts x u).erase p.val.val)))).Adj v t →
          0 < D.endpointCount t) →
        ∃ F : Decomposition G, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
          F.endpointCount v = D.endpointCount v + 1 ∧
          F.endpointCount h = D.endpointCount h := by
  classical
  have hpos : 0 < #(singleContactPetals f P (windmillContacts x u)) := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  obtain ⟨p, _, hpA, hqA⟩ := single_contact_orientation f hinv P (windmillContacts x u) r hr
  refine ⟨p, hpA, hqA, ?_⟩
  intro D hretained hvpositive
  let B := ambientWindmillContacts x u
  let S := insert (x : V) (B.erase p.val.val)
  have hcap := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hpB : p.val.val ∈ B :=
    (mem_windmillPrivateSet x (windmillContacts x u) p.val.val).mpr ⟨p, hpA, rfl⟩
  have hqB : (f p).val.val ∉ B := by
    intro hq
    obtain ⟨a, ha, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) (f p).val.val).mp hq
    have hae : a = f p := Subtype.ext (Subtype.ext heq)
    exact hqA (hae ▸ ha)
  have hpx : p.val.val ≠ (x : V) := by
    intro heq
    exact p.property.ne (Subtype.ext heq.symm)
  have hqx : (f p).val.val ≠ (x : V) := by
    intro heq
    exact (f p).property.ne (Subtype.ext heq.symm)
  have hpS : p.val.val ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hpx, Finset.notMem_erase _ _⟩
  have hqS : (f p).val.val ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hqx, fun hq => hqB (Finset.mem_of_mem_erase hq)⟩
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.2.2 ho _ hpB
  have hux : u ≠ (x : V) := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq.symm ▸ x.property)
  have huS : u ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hux, fun hu => hstar.1 (Finset.mem_of_mem_erase hu)⟩
  have hvB : v ∉ B := by
    intro hv
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) v).mp hv
    exact hvx (ha ▸ a.property.symm)
  have hvS : v ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hxv.symm, fun hv => hvB (Finset.mem_of_mem_erase hv)⟩
  have hpu : p.val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ p.val.property)
  have hqu : (f p).val.val ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ (f p).val.property)
  have hpv : p.val.val ≠ v := fun heq => hvx (heq ▸ p.property.symm)
  have hqv : (f p).val.val ≠ v := fun heq => hvx (heq ▸ (f p).property.symm)
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, _, hhbare, _⟩
  have hhu : h ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hhEven)
  have hhprivate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      h ≠ a.val.val := by
    intro a heq
    have hd := bare_windmillPrivateSet_leaf_guards h x H ({a} : Finset _)
      a.val.val ((mem_windmillPrivateSet x {a} a.val.val).mpr ⟨a, by simp, rfl⟩)
    rw [← heq, hhbare] at hd
    omega
  have hhB : h ∉ B := by
    intro hh
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp hh
    exact hhprivate a ha.symm
  have hhS : h ∉ S := by
    simp only [S, Finset.mem_insert, not_or]
    exact ⟨hhx, fun hh => hhB (Finset.mem_of_mem_erase hh)⟩
  exact restore_contact_E4 u v x p.val.val (f p).val.val h S
    huS hvS huv huOdd hodd huvAdj
    (fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact huxAdj
      · exact hstar.2 t (Finset.mem_of_mem_erase ht))
    (fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact x.property
      · exact (hcap t (Finset.mem_of_mem_erase ht)).1)
    (Finset.mem_insert_self _ _)
    (fun t ht htx => (hcap t (Finset.mem_of_mem_erase
      ((Finset.mem_insert.mp ht).resolve_left htx))).2.le)
    (fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hvx
      · obtain ⟨a, _, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp
          (Finset.mem_of_mem_erase ht)
        exact hseparate a)
    hqu hqv hqS hpu hpv hpS ((hedge p (f p)).mpr rfl).symm
    (f p).val.property p.val.property
    (fun ha => hseparate p ha.symm)
    (bare_windmill_private_even_neighbors h x H f hedge p)
    (hseparate (f p))
    (fun ha => hqA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
    hhu hhv (hhprivate (f p)) (hhprivate p) hhS D hretained hvpositive

end Gallai.TwoException
