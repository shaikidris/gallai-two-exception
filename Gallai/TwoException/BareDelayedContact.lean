/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.DelayedOddRegime

@[expose] public section

/-! # The five delayed-payment cases and their residual

The ordinary contact family is computed from the original graph. The
dispatcher covers the five rows of the delayed-payment table. Its residual
theorem identifies the multi-component cases left for early payment.
-/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance bareDelayedComponents : DecidableEq (evenSubgraph G).ConnectedComponent :=
  Classical.decEq _

/-- Each of the five delayed-payment rows contradicts bare minimality.
The spare-petal hypotheses refer to actual private contacts in G. -/
theorem bare_delayed_contact_reducible
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    ((#F = 1 ∧ ∀ D ∈ F, #(ordinaryComponentPacket G S D) ≠ 3) ∨
      (Odd #F ∧ 3 ≤ #F) ∨
      (Even #F ∧ 0 < #F ∧
        ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
          G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
          ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
            G.Adj u a.val → a = x) ∨
      (Even #F ∧ 4 ≤ #F ∧
        (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty) ∨
      (#F = 2 ∧
        (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty ∧
        ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
          G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
          ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
            a ≠ x → G.Adj u a.val)) → False := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro hcase
  change
    ((#F = 1 ∧ ∀ D ∈ F, #(ordinaryComponentPacket G S D) ≠ 3) ∨
      (Odd #F ∧ 3 ≤ #F) ∨
      (Even #F ∧ 0 < #F ∧
        ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
          G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
          ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
            G.Adj u a.val → a = x) ∨
      (Even #F ∧ 4 ≤ #F ∧
        (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty) ∨
      (#F = 2 ∧
        (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty ∧
        ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
          G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
          ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
            a ≠ x → G.Adj u a.val)) at hcase
  rcases hcase with hone | hodd | hsingle | hspecial | hdouble
  · have ho : Odd #F := by rw [hone.1]; decide
    exact bare_delayed_odd_or_single_ordinary_regime_false h u x H C hxC p hup hu
      ho (Or.inr hone)
  · exact bare_delayed_odd_ordinary_regime_false h u x H C hxC p hup hu
      hodd.1 (by change 1 < #F; omega)
  · obtain ⟨heven,hpos,r,hur,hpr,hprEdge,hsingle⟩ := hsingle
    exact bare_delayed_even_single_spare_regime_false h u x H C hxC p r
      hup hur hpr hprEdge hsingle hu heven hpos
  · exact bare_delayed_even_special_ordinary_regime_false h u x H C hxC p hup hu
      hspecial.1 hspecial.2.1 hspecial.2.2
  · obtain ⟨hcount,hT2,r,hur,hpr,hprEdge,hdouble⟩ := hdouble
    exact bare_delayed_two_special_double_spare_regime_false h u x H C hxC p r
      hup hur hpr hprEdge hdouble hu hcount hT2

/-- With at least two ordinary components, failure of delayed payment
leaves an even component count, no spare single petal, and either no
two-contact component or exactly two components with no spare double petal.
These are the residual conditions used by early payment. -/
theorem bare_delayed_multiple_contact_residual
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (C : (evenSubgraph G).ConnectedComponent) (hxC : x ∈ C.supp)
    (p : {a : evenVertices G // (evenSubgraph G).Adj x a})
    (hup : G.Adj u p.val.val) (hu : Odd (G.degree u)) :
    let S : Finset (evenVertices G) := Finset.univ.filter
      (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
    let F := S.image (evenSubgraph G).connectedComponentMk
    2 ≤ #F →
      Even #F ∧
      (¬ ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
        G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
        ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
          G.Adj u a.val → a = x) ∧
      (¬ (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty ∨
        (#F = 2 ∧
          ¬ ∃ r : {a : evenVertices G // (evenSubgraph G).Adj x a},
            G.Adj u r.val.val ∧ p ≠ r ∧ ¬ (evenSubgraph G).Adj p.val r.val ∧
            ∀ a : evenVertices G, (evenSubgraph G).Adj r.val a →
              a ≠ x → G.Adj u a.val)) := by
  classical
  dsimp only
  let S : Finset (evenVertices G) := Finset.univ.filter
    (fun a => G.Adj u a.val ∧ a ∉ C.supp ∧ a.val ≠ h)
  let F := S.image (evenSubgraph G).connectedComponentMk
  intro hcount
  change 2 ≤ #F at hcount
  have heven : Even #F := by
    rcases Nat.even_or_odd #F with he | ho
    · exact he
    · exact (bare_delayed_odd_ordinary_regime_false h u x H C hxC p hup hu
        ho (by change 1 < #F; omega)).elim
  refine ⟨heven,?_,?_⟩
  · rintro ⟨r,hur,hpr,hprEdge,hsingle⟩
    exact bare_delayed_even_single_spare_regime_false h u x H C hxC p r
      hup hur hpr hprEdge hsingle hu heven (by change 0 < #F; omega)
  · by_cases hT2 : (F.filter (fun D => #(ordinaryComponentPacket G S D) = 2)).Nonempty
    · right
      have htwo : #F = 2 := by
        by_contra hn
        have hfour : 4 ≤ #F := by
          rw [Nat.even_iff] at heven
          omega
        exact bare_delayed_even_special_ordinary_regime_false h u x H C hxC p hup hu
          heven hfour hT2
      refine ⟨htwo,?_⟩
      rintro ⟨r,hur,hpr,hprEdge,hdouble⟩
      exact bare_delayed_two_special_double_spare_regime_false h u x H C hxC p r
        hup hur hpr hprEdge hdouble hu htwo hT2
    · exact Or.inl hT2

end Gallai.TwoException
