/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.E5ProtectedBudget
public import Gallai.TwoException.ContactE5Reserved

@[expose] public section

/-! # Protected E5 reduction with derived endpoint reserves -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance reductionE5StarAdj (u h : V) (S : Finset V) :
    DecidableRel (starPuncture G u (insert h S)).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance reductionE5SpokeAdj (u h x s : V) (S : Finset V) :
    DecidableRel ((starPuncture G u (insert h S)).deleteEdges {s(x,s)}).Adj :=
  fun _ _ => Classical.propDecidable _
noncomputable local instance reductionE5MateAdj (u h x s p q : V) (S : Finset V) :
    DecidableRel (((starPuncture G u (insert h S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}).Adj := fun _ _ => Classical.propDecidable _

/-- The protected two-petal E5 branch derives its floor-budget decomposition
and reserves, then restores the graph with h exposed twice. -/
theorem bare_windmill_E5_protected_false
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (u : V)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f) (hfree : ∀ a, f a ≠ a)
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (he : Even #(singleContactPetals f P (windmillContacts x u)))
    (p r : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hpA : p ∈ windmillContacts x u) (hqA : f p ∉ windmillContacts x u)
    (hrA : r ∈ windmillContacts x u) (hsA : f r ∉ windmillContacts x u)
    (hdisj : Disjoint ({p, f p} : Finset _) {r, f r})
    (huOdd : Odd (G.degree u)) (huh : G.Adj u h)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t = h ∨ t ∈ ambientWindmillContacts x u) : False := by
  classical
  obtain ⟨D, hDsize⟩ := bare_windmill_E5_protected_floor h x H u f P hfree hindex
    hedge he p r hpA hqA hrA hsA hdisj huOdd huh hcontacts
  let A := ambientWindmillContacts x u
  let S := A.erase p.val.val
  rcases H.counterexample.1 with ⟨_, hhx, _, hhEven, hxEven, hhzero, _⟩
  have hguard := bare_windmillPrivateSet_leaf_guards h x H (windmillContacts x u)
  have hstar := windmillPrivateSet_contact_guards x u (windmillContacts x u)
    (fun a ha => (Finset.mem_filter.mp ha).2)
  have hnil : evenNeighbors G h = ∅ := Finset.card_eq_zero.mp hhzero
  have hno : ∀ t, G.Adj h t → Even (G.degree t) → False := by
    intro t ha ht
    have hm := (mem_evenNeighbors (G := G) h t).mpr ⟨ha, ht⟩
    simpa [hnil] using hm
  have hmem : ∀ a ∈ windmillContacts x u, a.val.val ∈ A :=
    fun a ha => (mem_windmillPrivateSet x (windmillContacts x u) _).mpr ⟨a, ha, rfl⟩
  have hnot : ∀ a, a ∉ windmillContacts x u → a.val.val ∉ A := by
    intro a ha ht
    obtain ⟨b, hb, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) _).mp ht
    have hba : b = a := Subtype.ext (Subtype.ext heq)
    exact ha (hba ▸ hb)
  have hneH : ∀ a : {a : evenVertices G // (evenSubgraph G).Adj x a}, a.val.val ≠ h :=
    fun a heq => hno x (heq ▸ a.property.symm) hxEven
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
  have hrp : r.val.val ≠ p.val.val :=
    fun heq => hcross p (by simp) r (by simp) heq.symm
  have hrS : r.val.val ∈ S := Finset.mem_erase.mpr ⟨hrp, hmem r hrA⟩
  have hpS : p.val.val ∉ S := Finset.notMem_erase _ _
  have hqS : (f p).val.val ∉ S :=
    fun ht => hnot _ hqA (Finset.mem_of_mem_erase ht)
  have hsS : (f r).val.val ∉ S :=
    fun ht => hnot _ hsA (Finset.mem_of_mem_erase ht)
  have hhA : h ∉ A := by
    intro ht
    obtain ⟨a, _, heq⟩ := (mem_windmillPrivateSet x (windmillContacts x u) h).mp ht
    exact hneH a heq
  have hhS : h ∉ S := fun ht => hhA (Finset.mem_of_mem_erase ht)
  have huS : u ∉ S := fun ht => hstar.1 (Finset.mem_of_mem_erase ht)
  have hxA : (x : V) ∉ A := hub_not_mem_windmillPrivateSet x (windmillContacts x u)
  have hxS : (x : V) ∉ S := fun ht => hxA (Finset.mem_of_mem_erase ht)
  have hxu : (x : V) ≠ u := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr huOdd) (heq ▸ hxEven)
  have hodd : Odd #S :=
    (windmill_contact_row_parities x f hfree P (windmillContacts x u) hindex).2.1
      he _ (hmem p hpA)
  have hadj : ∀ t ∈ S, G.Adj u t :=
    fun t ht => hstar.2 t (Finset.mem_of_mem_erase ht)
  have heven : ∀ t ∈ S, Even (G.degree t) :=
    fun t ht => (hguard t (Finset.mem_of_mem_erase ht)).1
  have huB : u ∉ insert h S := by simp [huh.ne, huS]
  have hBeven : Even #(insert h S) := by
    rw [Finset.card_insert_of_notMem hhS]
    rw [Nat.odd_iff] at hodd
    rw [Nat.even_iff]
    omega
  have hBAdj : ∀ t ∈ insert h S, G.Adj u t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact huh
    · exact hadj t ht
  have hBEven : ∀ t ∈ insert h S, Even (G.degree t) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hhEven
    · exact heven t ht
  have hprof := contact_E5_puncture_profile u x (f r).val.val p.val.val (f p).val.val
    (insert h S) huB hBAdj huOdd hBeven hBEven hxu (hneU _)
    (by simp [hhx.symm, hxS]) (by simp [hneH _, hsS])
    (f r).property hxEven (f r).val.property (hneU _) (hneU _)
    (by simp [hneH _, hpS]) (by simp [hneH _, hqS])
    (hneX _) (hcross p (by simp) (f r) (by simp))
    (hneX _) (hcross (f p) (by simp) (f r) (by simp))
    ((hedge p (f p)).mpr rfl).symm p.val.property (f p).val.property
  have hhOdd : Odd ((((starPuncture G u (insert h S)).deleteEdges
      {s((x : V),(f r).val.val)}).deleteEdges {s((f p).val.val,p.val.val)}).degree h) := by
    have ho := contact_spoke_puncture_leaf_odd u x (f r).val.val h (insert h S)
      (by simp) huh hhEven hhx (hneH _).symm
    have hd := degree_delete_edge_of_ne
      ((starPuncture G u (insert h S)).deleteEdges {s((x : V),(f r).val.val)})
      (f p).val.val p.val.val h (hneH _).symm (hneH _).symm
    simp only [← SimpleGraph.ncard_neighborSet] at hd ho ⊢
    rw [hd]
    exact ho
  have hDh : 0 < D.endpointCount h := D.endpointCount_pos_of_odd_degree h hhOdd
  have hretained : ∀ t, G.Adj u t → t ∉ S → t ≠ p.val.val →
      Odd (G.degree t) ∨ 0 < D.endpointCount t := by
    intro t hut htS htp
    by_cases htEven : Even (G.degree t)
    · rcases hcontacts t hut htEven with ht | htA
      · subst t
        exact Or.inr hDh
      · exact False.elim (htS (Finset.mem_erase.mpr ⟨htp, htA⟩))
    · exact Or.inl (Nat.not_even_iff_odd.mp htEven)
  have hvpositive : ∀ t, (starPuncture G u (insert h S)).Adj h t →
      0 < D.endpointCount t := by
    intro t ht
    apply D.endpointCount_pos_of_odd_degree
    apply Nat.not_even_iff_odd.mp
    intro htEven
    exact hno t ht.1 (hprof.1 t htEven)
  have hux : ¬ G.Adj u x := by
    intro ha
    rcases hcontacts x ha hxEven with ht | ht
    · exact hhx ht.symm
    · exact hxA ht
  obtain ⟨F, hFsize, _, hFh⟩ := restore_contact_E5_reserved_endpoint
    u h x (f r).val.val p.val.val (f p).val.val r.val.val S
    huS hhS huh.ne huOdd hodd huh hadj heven hrS
    (fun t ht _ => (hguard t (Finset.mem_of_mem_erase ht)).2.le)
    (fun t ht ha => hno t ha (heven t ht)) hxu hhx.symm hxS (hneU _)
    (f r).property hxEven (f r).val.property
    (fun ha => hno _ ha.symm p.val.property)
    (bare_windmill_private_even_neighbors h x H f hedge p)
    (hneU _) (hneH _) hpS (hneX _) (hcross p (by simp) (f r) (by simp))
    (hneU _) (hneH _) hqS (hneX _) (hcross (f p) (by simp) (f r) (by simp))
    ((hedge p (f p)).mpr rfl).symm p.val.property (f p).val.property
    (fun ha => hsA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩))
    (fun ha => hno _ ha.symm (f r).val.property)
    (by
      intro t ht htEven
      simpa only [hinv r] using
        bare_windmill_private_even_neighbors h x H f hedge (f r) t ht htEven)
    (fun ha => hno _ ha hxEven) (fun ha => hno _ ha (f p).val.property) hux
    (fun ha => hqA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))
    D hretained hvpositive
  apply H.counterexample.2
  refine ⟨F, ?_, ?_⟩
  · have hs : F.size ≤ Fintype.card V / 2 := hFsize.le.trans hDsize
    omega
  · rw [hFh]
    omega

end Gallai.TwoException
