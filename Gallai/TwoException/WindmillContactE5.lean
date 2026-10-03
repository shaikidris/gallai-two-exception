/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.WindmillContactE1
public import Gallai.TwoException.ContactE5

@[expose] public section

/-! # Native two-petal contact reconstruction -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance nativeE5StarAdj (u v : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert v S)).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance nativeE5SpokeAdj (u v x s : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert v S)).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance nativeE5MateAdj (u v x s q p : V) (S : Finset V) :
    DecidableRel (((starPuncture G u (insert v S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Native E5 chooses disjoint single petals for the mate and spoke
preparations. The complete cross-petal guards are derived, not assumed. -/
theorem bare_windmill_restore_E5
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u v : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (hpair : ∃ r ∈ singleContactPetals f P (windmillContacts x u),
      ∃ s ∈ singleContactPetals f P (windmillContacts x u), r ≠ s)
    (huOdd : Odd (G.degree u)) (huv : u ≠ v) (huvAdj : G.Adj u v)
    (hux : ¬ G.Adj u x) (hvx : ¬ G.Adj v x) (hhv : h ≠ v)
    (hseparate : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      ¬ G.Adj v a.val.val) :
    ∃ p r : {a : evenVertices G // (evenSubgraph G).Adj x a},
      p ∈ windmillContacts x u ∧ f p ∉ windmillContacts x u ∧
      r ∈ windmillContacts x u ∧ f r ∉ windmillContacts x u ∧
      Disjoint ({p, f p} : Finset _) {r, f r} ∧
      ∀ D : Decomposition
        (((starPuncture G u
          (insert v ((ambientWindmillContacts x u).erase p.val.val))).deleteEdges
          {s((x : V),(f r).val.val)}).deleteEdges {s((f p).val.val,p.val.val)}),
        (∀ t, G.Adj u t → t ∉ (ambientWindmillContacts x u).erase p.val.val →
          t ≠ p.val.val → Odd (G.degree t) ∨ 0 < D.endpointCount t) →
        (∀ t, (starPuncture G u
          (insert v ((ambientWindmillContacts x u).erase p.val.val))).Adj v t →
          0 < D.endpointCount t) →
        ∃ F : Decomposition G, F.size = D.size ∧ 1 ≤ F.endpointCount u ∧
          F.endpointCount v = D.endpointCount v + 1 ∧
          F.endpointCount h = D.endpointCount h := by
  classical
  obtain ⟨p, r, hpA, hqA, hrA, hsA, hdisj⟩ :=
    two_single_contact_petals f hinv P (windmillContacts x u) hindex hpair
  refine ⟨p, r, hpA, hqA, hrA, hsA, hdisj, ?_⟩
  intro D hretained hvpositive
  let B := ambientWindmillContacts x u
  let S := B.erase p.val.val
  have hcap := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hmem : ∀ a ∈ windmillContacts x u, a.val.val ∈ B := by
    intro a ha
    exact (mem_windmillPrivateSet x (windmillContacts x u) a.val.val).mpr ⟨a, ha, rfl⟩
  have hnot : ∀ a, a ∉ windmillContacts x u → a.val.val ∉ B := by
    intro a ha hb
    obtain ⟨b, hb, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) a.val.val).mp hb
    have hba : b = a := Subtype.ext (Subtype.ext heq)
    exact ha (hba ▸ hb)
  have hcross : ∀ a ∈ ({p, f p} : Finset _), ∀ b ∈ ({r, f r} : Finset _),
      a.val.val ≠ b.val.val := by
    intro a ha b hb heq
    have hab : a = b := Subtype.ext (Subtype.ext heq)
    exact (Finset.disjoint_left.mp hdisj) ha (hab.symm ▸ hb)
  have hrp : r.val.val ≠ p.val.val := by
    intro hEq
    exact hcross p (by simp) r (by simp) hEq.symm
  have hrS : r.val.val ∈ S := Finset.mem_erase.mpr ⟨hrp, hmem r hrA⟩
  have hpS : p.val.val ∉ S := Finset.notMem_erase _ _
  have hqS : (f p).val.val ∉ S := fun hq => hnot (f p) hqA (Finset.mem_of_mem_erase hq)
  have huS : u ∉ S := fun hu => hstar.1 (Finset.mem_of_mem_erase hu)
  have hxS : (x : V) ∉ S := fun hx =>
    hub_not_mem_windmillPrivateSet x (windmillContacts x u) (Finset.mem_of_mem_erase hx)
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.1
      he p.val.val (hmem p hpA)
  have hxu : (x : V) ≠ u := by
    intro hEq
    exact (Nat.not_even_iff_odd.mpr huOdd) (hEq ▸ x.property)
  have hxv : (x : V) ≠ v := by
    intro hEq
    exact hux (hEq.symm ▸ huvAdj)
  have hneU : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ u := by
    intro a hEq
    exact (Nat.not_even_iff_odd.mpr huOdd) (hEq ▸ a.val.property)
  have hneV : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ v :=
    fun a hEq => hvx (hEq ▸ a.property.symm)
  have hneX : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ (x : V) := by
    intro a hEq
    exact a.property.ne (Subtype.ext hEq.symm)
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) v).mp
      (Finset.mem_of_mem_erase hv)
    exact hneV a ha
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, _, hhbare, _⟩
  have hhu : h ≠ u := by
    intro hEq
    exact (Nat.not_even_iff_odd.mpr huOdd) (hEq ▸ hhEven)
  have hneH : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, h ≠ a.val.val := by
    intro a hEq
    have hd := bare_windmillPrivateSet_leaf_guards h x H ({a} : Finset _)
      a.val.val ((mem_windmillPrivateSet x {a} a.val.val).mpr ⟨a, by simp, rfl⟩)
    rw [← hEq, hhbare] at hd
    omega
  have hhS : h ∉ S := by
    intro hh
    obtain ⟨a, _, ha⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp
      (Finset.mem_of_mem_erase hh)
    exact hneH a ha.symm
  exact restore_contact_E5 u v x (f r).val.val p.val.val (f p).val.val r.val.val h S
    huS hvS huv huOdd hodd huvAdj
    (fun t ht => hstar.2 t (Finset.mem_of_mem_erase ht))
    (fun t ht => (hcap t (Finset.mem_of_mem_erase ht)).1)
    hrS (fun t ht _ => (hcap t (Finset.mem_of_mem_erase ht)).2.le)
    (fun t ht => by
      obtain ⟨a, _, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp
        (Finset.mem_of_mem_erase ht)
      exact hseparate a)
    hxu hxv hxS (hneU (f r)) (f r).property x.property (f r).val.property
    (fun ha => hseparate p ha.symm)
    (bare_windmill_private_even_neighbors h x H f hedge p)
    (hneU p) (hneV p) hpS (hneX p) (hcross p (by simp) (f r) (by simp))
    (hneU (f p)) (hneV (f p)) hqS (hneX (f p))
    (hcross (f p) (by simp) (f r) (by simp))
    ((hedge p (f p)).mpr rfl).symm p.val.property (f p).val.property
    (fun ha => hsA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩))
    (fun ha => hseparate (f r) ha.symm)
    (by
      intro t ht htEven
      simpa only [hinv r] using
        bare_windmill_private_even_neighbors h x H f hedge (f r) t ht htEven)
    hvx (hseparate (f p)) hux
    (fun ha => hqA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
    hhu hhv hhS hhx (hneH (f r)) (hneH p) (hneH (f p)) D hretained hvpositive

end Gallai.TwoException
