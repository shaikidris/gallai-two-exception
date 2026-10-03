/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryNativeTriangleGain
public import Gallai.TwoException.WindmillContactSets

@[expose] public section

/-! # Windmill contributions in early-payment tight failures -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G J : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel J.Adj]
noncomputable local instance (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- A double-contact petal has nonnegative gain in an early-payment
tight failure: at least one of its two contacts must be selected. -/
theorem bare_early_double_petal_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (D : Decomposition J) (u : V) (S A : Finset V)
    (hpS : p.val.val ∈ S) (hpu : p.val.val ≠ u)
    (hmissing : ¬ J.Adj p.val.val u) (hq : 0 < D.endpointCount (f p).val.val)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #({p.val.val,(f p).val.val} \ A) ≤ #({p.val.val,(f p).val.val} ∩ A) := by
  classical
  have hn : ∀ t, G.Adj p.val.val t → Even (G.degree t) →
      t = (f p).val.val ∨ t = (x : V) := by
    intro t ht he
    exact (bare_windmill_private_even_neighbors h x H f hedge p t ht he).symm
  have hsel := ordinary_special_contacts_selected D u p.val.val (f p).val.val x S A
    hpS hpu hq hmissing E hsub hprofile hn hvec htight
  have hne : p.val.val ≠ (f p).val.val :=
    fun he => ((hedge p (f p)).mpr rfl).ne (Subtype.ext he)
  apply ordinary_special_packet_contribution {p.val.val,(f p).val.val} A (by simp [hne])
  rcases hsel with hp | hq
  · exact ⟨p.val.val,Finset.mem_inter.mpr ⟨by simp,hp⟩⟩
  · exact ⟨(f p).val.val,Finset.mem_inter.mpr ⟨by simp,hq⟩⟩

/-- The sole single-contact spoke petal contributes one unit in an
early-payment tight failure. Its restored mate is positive and is not
a deleted contact, so the contact itself must be selected. -/
theorem bare_early_single_petal_gain
    (h : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (f : {a : evenVertices G // (evenSubgraph G).Adj x a} →
      {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hedge : ∀ a b, (evenSubgraph G).Adj a.val b.val ↔ f a = b)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (D : Decomposition J) (u : V) (S A : Finset V) (hAS : A ⊆ S)
    (hpS : p.val.val ∈ S) (hpu : p.val.val ≠ u) (hqS : (f p).val.val ∉ S)
    (hmissing : ¬ J.Adj p.val.val u) (hq : 2 ≤ D.endpointCount (f p).val.val)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hprofile : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2) :
    #({p.val.val} \ A) + 1 ≤ #({p.val.val} ∩ A) := by
  classical
  have hn : ∀ t, G.Adj p.val.val t → Even (G.degree t) →
      t = (f p).val.val ∨ t = (x : V) := by
    intro t ht he
    exact (bare_windmill_private_even_neighbors h x H f hedge p t ht he).symm
  have hsel := ordinary_special_contacts_selected D u p.val.val (f p).val.val x S A
    hpS hpu (by omega) hmissing E hsub hprofile hn hvec htight
  have hpA : p.val.val ∈ A := hsel.resolve_right (fun hqA => hqS (hAS hqA))
  simp [hpA]

end Gallai.TwoException
