/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyHubPendingBound

@[expose] public section

/-! # Prescribed hub offsets the sole single-contact loss -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A selected new element offsets the loss of at most one other contact.
No disjointness between the double-family set and the remainder is needed. -/
theorem selected_hub_offsets_one_contact_loss
    (D R A : Finset V) (x : V) (hx : x ∉ D ∪ R) (hxA : x ∈ A)
    (hR : #R ≤ 1) (hgain : #(D \ A) ≤ #(D ∩ A)) :
    #((insert x (D ∪ R)) \ A) ≤ #((insert x (D ∪ R)) ∩ A) := by
  have hp : (insert x (D ∪ R)) \ A = (D \ A) ∪ (R \ A) := by
    ext t
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_union]
    constructor
    · rintro ⟨rfl | hd | hr,hn⟩
      · exact (hn hxA).elim
      · exact Or.inl ⟨hd,hn⟩
      · exact Or.inr ⟨hr,hn⟩
    · rintro (⟨hd,hn⟩ | ⟨hr,hn⟩)
      · exact ⟨Or.inr (Or.inl hd),hn⟩
      · exact ⟨Or.inr (Or.inr hr),hn⟩
  have hs : insert x (D ∩ A) ⊆ (insert x (D ∪ R)) ∩ A := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hxA⟩
    · obtain ⟨hd,ha⟩ := Finset.mem_inter.mp ht
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hd),ha⟩
  have hxD : x ∉ D ∩ A := fun ht => hx
    (Finset.mem_union_left _ (Finset.mem_inter.mp ht).1)
  have hsel := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hxD] at hsel
  have hpend := Finset.card_union_le (D \ A) (R \ A)
  have hrem := Finset.card_le_card (Finset.sdiff_subset (s := R) (t := A))
  rw [hp]
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance hubGainStar (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance hubGainHalf (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- With at most one single-contact petal, prescribing the hub gives a
nonnegative total windmill contribution on the actual half-star. The sole
contact need not itself be selected or have a restored mate reserve. -/
theorem bare_actual_early_prescribed_hub_windmill_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P C : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a}) (hpC : p ∈ C)
    (hsingle : ∀ r ∈ singleContactPetals f P C,
      ∀ a ∈ C ∩ ({r,f r} : Finset _), a = p)
    (u : V) (B A : Finset V) (hAB : A ⊆ B) (hxA : (x : V) ∈ A)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (hCB : ∀ r ∈ C, r.val.val ∈ B)
    (D : Decomposition (starPuncture G u B))
    (hmates : ∀ r ∈ C, 0 < D.endpointCount r.val.val)
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ t ∈ B \ A, passingNeighborCount E t = 2) :
    #((insert (x : V) (windmillPrivateSet x C)) \ A) ≤
      #((insert (x : V) (windmillPrivateSet x C)) ∩ A) := by
  classical
  have hpartition := ambient_early_sole_single_partition x f P C hindex p hpC hsingle
  have hgain := bare_indexed_early_double_gain h x H f hedge P C hindex
    u B A hAB hadj hleaves hCB D hmates E hvec htight
  rw [hpartition]
  apply selected_hub_offsets_one_contact_loss _ {p.val.val} A x _ hxA (by simp) hgain
  rw [← hpartition]
  exact hub_not_mem_windmillPrivateSet x C

end Gallai.TwoException
