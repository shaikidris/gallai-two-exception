/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalDelayedResidual
public import Gallai.TwoException.EarlySinglePetalCount
public import Gallai.TwoException.EarlyCanonicalSingleHubContradiction

@[expose] public section

/-! # The all-double residual with multiple ordinary components -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance canonicalHubAllDoubleComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- With a hub contact and at least two ordinary components, no petal has
exactly one contacted private. Delayed spare exclusion allows at most one;
the canonical hub contradiction excludes that last possibility. -/
theorem bare_canonical_hub_multiple_single_petals_empty
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) :
    singleContactPetals f P (windmillContacts x u) = ∅ := by
  classical
  let A := windmillContacts x u
  have hag := early_delayed_contact_agreement h u x C hxC
  have hcount := hag.1 ▸ hN
  have hsingleEq := bare_early_single_private_eq_selected h u x H C hxC p hup hu hcount
  obtain ⟨R,hRP,hunique⟩ := hindex p
  have hsub : singleContactPetals f P A ⊆ {R} := by
    intro r hr
    obtain ⟨q,hqr,hq,hfq⟩ := single_contact_orientation f hinv P A r hr
    have huq : G.Adj u q.val.val := (Finset.mem_filter.mp hq).2
    have hqsingle : ∀ a : evenVertices G, (evenSubgraph G).Adj q.val a →
        G.Adj u a.val → a = x := by
      intro a hqa hua
      have ht := bare_windmill_private_even_neighbors h x H f hedge q a.val hqa a.property
      rcases ht with ha | ha
      · exact Subtype.val_injective ha
      · have he : a = (f q).val := Subtype.val_injective ha
        have hfqA : f q ∈ A := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,he ▸ hua⟩
        exact False.elim (hfq hfqA)
    have hqp : q = p := hsingleEq q huq hqsingle
    have hrP : r ∈ P := (Finset.mem_filter.mp hr).1
    have hpPair : p = r ∨ p = f r := hqp ▸ hqr
    exact Finset.mem_singleton.mpr (hunique r ⟨hrP,hpPair⟩)
  have hle : #(singleContactPetals f P A) ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hzero : #(singleContactPetals f P A) = 0 := by
    by_contra hn
    have hone : #(singleContactPetals f P A) = 1 := by omega
    exact bare_canonical_one_single_hub_impossible h u x H C hxC f hinv hedge P hindex
      hu hux hone hN
  exact Finset.card_eq_zero.mp hzero

/-- A surviving multiple-component hub contact is all-double and has no
two-contact ordinary triangle. Thus the special packet cannot be the
remaining parity obstruction in this canonical branch. -/
theorem bare_canonical_hub_multiple_residual
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hinv : Function.Involutive f)
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (P : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hindex : ∀ a, ∃! r, r ∈ P ∧ (a = r ∨ a = f r))
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) (hux : G.Adj u x)
    (hN : 2 ≤ #(earlyOrdinaryContactComponents G h x u)) :
    singleContactPetals f P (windmillContacts x u) = ∅ ∧
    Even #(earlyOrdinaryContactComponents G h x u) ∧
    (earlyOrdinaryContactComponents G h x u).filter
      (fun Z => #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 2) = ∅ := by
  classical
  have hsingle := bare_canonical_hub_multiple_single_petals_empty h u x H C hxC
    f hinv hedge P hindex p hup hu hux hN
  have hres := bare_canonical_delayed_multiple_residual h u x H C hxC p hup hu hN
  refine ⟨hsingle,hres.1,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro Z hZ
  obtain ⟨hF,hx,hclass,hS,hcover⟩ := bare_early_canonical_contact_guards h u x H
  apply bare_selected_early_hub_impossible h u x H f hinv hedge P hindex p
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hup⟩) ?_
    (earlyOriginalContacts G h x u) (earlyOrdinaryContactComponents G h x u)
    hF hx hclass hS hcover hu hux hN (Or.inr ⟨Z,hZ⟩)
  intro r hr
  rw [hsingle] at hr
  exact False.elim (Finset.notMem_empty r hr)

end Gallai.TwoException
