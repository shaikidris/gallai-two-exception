/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyCanonicalContacts

@[expose] public section

/-! # Agreement of early and delayed ordinary contact data -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance contactAgreementComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- The delayed route removes the whole hub component from its original
contact set. Its touched ordinary components are exactly the canonical early
ones, and its packets agree on each such component. -/
theorem early_delayed_contact_agreement
    (h u : V) (x : evenVertices G)
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    let T : Finset (evenVertices G) := Finset.univ.filter
      (fun t => G.Adj u t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
    earlyOrdinaryContactComponents G h x u =
      T.image (evenSubgraph G).connectedComponentMk ∧
    ∀ Z ∈ earlyOrdinaryContactComponents G h x u,
      ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z =
        ordinaryComponentPacket G T Z := by
  classical
  let T : Finset (evenVertices G) := Finset.univ.filter
    (fun t => G.Adj u t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
  have hxEq := (SimpleGraph.ConnectedComponent.mem_supp_iff C x).mp hxC
  refine ⟨?_,?_⟩
  · ext Z
    constructor
    · intro hZ
      obtain ⟨himage,hxZ⟩ := Finset.mem_filter.mp hZ
      obtain ⟨t,ht,htZ⟩ := Finset.mem_image.mp himage
      have hp := (Finset.mem_filter.mp ht).2
      have htC : t ∉ C.supp := by
        intro hc
        have htEq := (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mp hc
        have hZC : Z = C := htZ.symm.trans htEq
        exact hxZ (hZC.symm ▸ hxC)
      exact Finset.mem_image.mpr ⟨t,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1,htC,hp.2.1⟩,htZ⟩
    · intro hZ
      obtain ⟨t,ht,htZ⟩ := Finset.mem_image.mp hZ
      have hp := (Finset.mem_filter.mp ht).2
      have htx : (t : V) ≠ x := by
        intro he
        exact hp.2.1 (Subtype.val_injective he ▸ hxC)
      have hxZ : x ∉ Z.supp := by
        intro hx
        have hZC : Z = C :=
          ((SimpleGraph.ConnectedComponent.mem_supp_iff Z x).mp hx).symm.trans hxEq
        have htC : t ∈ C.supp :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff C t).mpr (htZ.trans hZC)
        exact hp.2.1 htC
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨t,?_,htZ⟩,hxZ⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1,hp.2.2,htx⟩
  · intro Z hZ
    have hxZ := (Finset.mem_filter.mp hZ).2
    ext t
    constructor
    · intro ht
      obtain ⟨htS,htZ⟩ := Finset.mem_filter.mp ht
      have hp := (Finset.mem_filter.mp htS).2
      have htC : t ∉ C.supp := by
        intro hc
        have hZC : Z = C :=
          ((SimpleGraph.ConnectedComponent.mem_supp_iff Z t).mp htZ).symm.trans
            ((SimpleGraph.ConnectedComponent.mem_supp_iff C t).mp hc)
        exact hxZ (hZC.symm ▸ hxC)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1,htC,hp.2.1⟩,htZ⟩
    · intro ht
      obtain ⟨htT,htZ⟩ := Finset.mem_filter.mp ht
      have hp := (Finset.mem_filter.mp htT).2
      have htx : (t : V) ≠ x := by
        intro he
        exact hp.2.1 (Subtype.val_injective he ▸ hxC)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1,hp.2.2,htx⟩,htZ⟩

/-- Two-contact eligibility is invariant under the early/delayed contact
presentation, including the component filter used by the parity selector. -/
theorem early_delayed_two_contact_agreement
    (h u : V) (x : evenVertices G)
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp) :
    let T : Finset (evenVertices G) := Finset.univ.filter
      (fun t => G.Adj u t.val ∧ t ∉ C.supp ∧ t.val ≠ h)
    (earlyOrdinaryContactComponents G h x u).filter
      (fun Z => #(ordinaryComponentPacket G (earlyOriginalContacts G h x u) Z) = 2) =
    (T.image (evenSubgraph G).connectedComponentMk).filter
      (fun Z => #(ordinaryComponentPacket G T Z) = 2) := by
  classical
  have hag := early_delayed_contact_agreement h u x C hxC
  dsimp only
  ext Z
  constructor
  · intro hz
    obtain ⟨hZ,hcard⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hag.1 ▸ hZ,?_⟩
    rw [← hag.2 Z hZ]
    exact hcard
  · intro hz
    obtain ⟨hZ,hcard⟩ := Finset.mem_filter.mp hz
    have hZE := hag.1.symm ▸ hZ
    apply Finset.mem_filter.mpr
    refine ⟨hZE,?_⟩
    rw [hag.2 Z hZE]
    exact hcard

end Gallai.TwoException
