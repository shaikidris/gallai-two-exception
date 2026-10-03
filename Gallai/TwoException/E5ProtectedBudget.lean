/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE5Budget
public import Gallai.TwoException.WindmillContactE5

@[expose] public section

/-! # Native two-petal protected E5 auxiliary budget -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance protectedE5StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance protectedE5SpokeAdj (u h x s : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance protectedE5MateAdj (u h x s p q : V) (S : Finset V) :
    DecidableRel (((starPuncture G u (insert h S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- Two disjoint singly contacted petals supply E5's actual floor-budget
puncture, with h as reserved endpoint and no other even-component contact. -/
theorem bare_windmill_E5_protected_floor
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpA : p ∈ windmillContacts x u) (hqA : f p ∉ windmillContacts x u)
    (hrA : r ∈ windmillContacts x u) (hsA : f r ∉ windmillContacts x u)
    (hdisj : Disjoint ({p, f p} : Finset _) {r, f r})
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) :
    HasPathBudget (((starPuncture G u
      (insert h ((ambientWindmillContacts x u).erase p.val.val))).deleteEdges
      {s((x : V),(f r).val.val)}).deleteEdges {s((f p).val.val,p.val.val)})
      (Fintype.card V / 2) := by
  classical
  let A := ambientWindmillContacts x u
  let S := A.erase p.val.val
  let B := insert h S
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hmem : ∀ a ∈ windmillContacts x u, a.val.val ∈ A :=
    fun a ha => (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩
  have hnot : ∀ a, a ∉ windmillContacts x u → a.val.val ∉ A := by
    intro a ha ht
    obtain ⟨b, hb, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp ht
    have hba : b = a := Subtype.ext (Subtype.ext heq)
    exact ha (hba ▸ hb)
  have hdeg : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a},
      eDegree G a.val.val = 2 := by
    intro a
    exact (bare_windmillPrivateSet_leaf_guards h x H {a} _
      ((mem_windmillPrivateSet x {a} _).mpr ⟨a, by simp, rfl⟩)).2
  have hneH : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ h := by
    intro a heq
    have hd := hdeg a
    rw [heq, hhzero] at hd
    omega
  have hneU : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ u := by
    intro a heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ a.val.property)
  have hneX : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ (x : V) := by
    intro a heq
    exact a.property.ne (Subtype.ext heq.symm)
  have hcross : ∀ a ∈ ({p, f p} : Finset _), ∀ b ∈ ({r, f r} : Finset _),
      a.val.val ≠ b.val.val := by
    intro a ha b hb heq
    have hab : a = b := Subtype.ext (Subtype.ext heq)
    exact (Finset.disjoint_left.mp hdisj) ha (hab.symm ▸ hb)
  have hhA : h ∉ A := by
    intro ht
    have hd := (hguard h ht).2
    rw [hhzero] at hd
    omega
  have hhS : h ∉ S := fun ht => hhA (Finset.mem_of_mem_erase ht)
  have huS : u ∉ S := fun ht => hstar.1 (Finset.mem_of_mem_erase ht)
  have hxA : (x : V) ∉ A := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have hxS : (x : V) ∉ S := fun ht => hxA (Finset.mem_of_mem_erase ht)
  have hxB : (x : V) ∉ B := by simp [B, hhx.symm, hxS]
  have hpB : p.val.val ∉ B := by simp [B, S, hneH p]
  have hqB : (f p).val.val ∉ B := by
    simp only [B, Finset.mem_insert, not_or]
    exact ⟨hneH _, fun ht => hnot _ hqA (Finset.mem_of_mem_erase ht)⟩
  have hsB : (f r).val.val ∉ B := by
    simp only [B, Finset.mem_insert, not_or]
    exact ⟨hneH _, fun ht => hnot _ hsA (Finset.mem_of_mem_erase ht)⟩
  have huB : u ∉ B := by simp [B, huh.ne, huS]
  have hxu : (x : V) ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hxEven)
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.1
      he _ (hmem p hpA)
  have hBeven : Even #B := by
    dsimp only [B]
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ B, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · exact hstar.2 t (Finset.mem_of_mem_erase ht)
  have hBEven : ∀ t ∈ B, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · exact (hguard t (Finset.mem_of_mem_erase ht)).1
  have hrfr : r.val.val ≠ (f r).val.val := by
    intro heq
    exact hfree r (Subtype.ext (Subtype.ext heq.symm))
  have hxr : (((starPuncture G u B).deleteEdges {s((x : V),(f r).val.val)}).deleteEdges
      {s((f p).val.val,p.val.val)}).Adj x r.val.val := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨?_, ?_⟩
    · apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨⟨r.property, ?_⟩, ?_⟩
      · intro ha
        exact hneU r ((star_sup_adj_off_center u B x r.val.val hxu).mp ha).2
      · intro ha
        have heq : s((x : V),r.val.val) = s((x : V),(f r).val.val) := by simpa using ha
        rcases Sym2.eq_iff.mp heq with heq | heq
        · exact hrfr heq.2
        · exact hneX (f r) heq.1.symm
    · intro ha
      have heq : s((x : V),r.val.val) = s((f p).val.val,p.val.val) := by simpa using ha
      rcases Sym2.eq_iff.mp heq with heq | heq
      · exact hneX (f p) heq.1.symm
      · exact hneX p heq.1.symm
  apply bare_contact_E5_floor h x H u (f r).val.val p.val.val (f p).val.val B huB
    hBAdj huOdd hBeven hBEven hxu (hneU _) hxB hsB (f r).property (f r).val.property
    (hneU _) (hneU _) hpB hqB (hneX _) (hcross p (by simp) (f r) (by simp))
    (hneX _) (hcross (f p) (by simp) (f r) (by simp))
    ((hedge p (f p)).mpr rfl).symm p.val.property (f p).val.property
    (hdeg _) p.property.symm (hdeg _) (f p).property.symm (hdeg _) ?_ ?_
    r.val.val hxr r.property.symm (hdeg _)
  · intro t hut htEven
    rcases hcontacts t hut htEven with ht | htA
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl ht))
    · by_cases htp : t = p.val.val
      · exact Or.inr (Or.inr (Or.inr (Or.inl htp)))
      · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨htp, htA⟩))
  · intro t ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact Or.inl ht
    · obtain ⟨a, ha, rfl⟩ := (mem_windmillPrivateSet x (windmillContacts x u) t).mp
        (Finset.mem_of_mem_erase ht)
      exact Or.inr ⟨a.property.symm, hdeg a⟩

end Gallai.TwoException
