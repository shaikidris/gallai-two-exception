/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryPreparedGain
public import Gallai.TwoException.OrdinaryNativeIsolateGain

@[expose] public section

/-! # Actual half-star gains summed over prepared ordinary packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance preparedHalfEq :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _
noncomputable local instance preparedHalfStarAdj (u : V) (B : Finset V) :
    DecidableRel (starPuncture G u B).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance preparedHalfAdj (u : V) (B A : Finset V) :
    DecidableRel ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Tight passing-neighbour failure forces the total prepared packet gain.
The inputs describe original packet shapes and restored mate endpoints;
no local selected-minus-pending inequality is assumed. -/
theorem ordinary_prepared_half_star_gain
    (u : V) (B A : Finset V) (hAB : A ⊆ B)
    (hadj : ∀ t ∈ B, G.Adj u t) (hleaves : ∀ t ∈ B, Even (G.degree t))
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hPB : ∀ C ∈ F, (P C).image Subtype.val ⊆ B)
    (D : Decomposition (starPuncture G u B))
    (E : Decomposition ((starPuncture G u B) ⊔ A.sup (SimpleGraph.edge u)))
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ B \ A, passingNeighborCount E w = 2)
    (hregular : ∀ C ∈ F, C ∉ special →
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)}))
    (hspecial : ∀ C ∈ F, C ∈ special →
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧ G.Adj a b ∧
        (P C).image Subtype.val = {(a : V),(b : V)}) :
    #((F.biUnion P).image Subtype.val \ A) + #F ≤
      #((F.biUnion P).image Subtype.val ∩ A) + #special := by
  classical
  apply ordinary_prepared_component_gain G F special P A hsupp
  · intro C hC hCs
    rcases hregular C hC hCs with ⟨a,hPa,hi⟩ | ⟨a,b,c,hs,hPa,hb⟩ | ⟨a,b,c,hs,hab,hbc,hca,hPabc⟩
    · have haB : (a : V) ∈ B := hPB C hC (by rw [hPa]; simp)
      rw [hPa]
      exact ordinary_native_isolate_gain u a B A hAB hadj hleaves haB hi E htight
    · have haB : (a : V) ∈ B := hPB C hC (by rw [hPa]; simp)
      rw [hPa]
      exact ordinary_native_regular_gain u B A hAB hadj hleaves C a b c hs
        haB D hb E hvec htight
    · have haB : (a : V) ∈ B := hPB C hC (by rw [hPabc]; simp)
      have hbB : (b : V) ∈ B := hPB C hC (by rw [hPabc]; simp)
      have hcB : (c : V) ∈ B := hPB C hC (by rw [hPabc]; simp)
      rw [hPabc]
      exact ordinary_native_t3_gain u B A hAB hadj hleaves C a b c hs hab hbc hca
        haB hbB hcB D E hvec htight
  · intro C hC hCs
    obtain ⟨a,b,c,hs,hab,hPab⟩ := hspecial C hC hCs
    have haB : (a : V) ∈ B := hPB C hC (by rw [hPab]; simp)
    have hbB : (b : V) ∈ B := hPB C hC (by rw [hPab]; simp)
    rw [hPab]
    exact ordinary_native_special_gain u B A hAB hadj hleaves C a b c hs hab
      haB hbB D E hvec htight

section Prepared
variable {J : SimpleGraph V} [DecidableRel J.Adj]
noncomputable local instance preparedGraphHalfAdj (u : V) (A : Finset V) :
    DecidableRel (J ⊔ A.sup (SimpleGraph.edge u)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Sum all ordinary packet types on the actual prepared residual graph.
The graph may still carry unpaid private mates and a reserved hub spoke. -/
theorem ordinary_prepared_graph_half_star_gain
    (u : V) (S A : Finset V) (huS : u ∉ S)
    (F special : Finset (evenSubgraph G).ConnectedComponent)
    (P : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G))
    (hsupp : ∀ C ∈ F, ∀ t ∈ P C, t ∈ C.supp)
    (hPS : ∀ C ∈ F, (P C).image Subtype.val ⊆ S)
    (D : Decomposition J)
    (E : Decomposition (J ⊔ A.sup (SimpleGraph.edge u)))
    (hsub : J ⊔ A.sup (SimpleGraph.edge u) ≤ G)
    (hp : ∀ t, Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) →
      Even (G.degree t) ∨ t = u)
    (hpos : ∀ t ∈ S, 0 < D.endpointCount t)
    (hmissing : ∀ t ∈ S, ¬ J.Adj t u)
    (hmissingE : ∀ t ∈ S \ A, ¬ (J ⊔ A.sup (SimpleGraph.edge u)).Adj t u)
    (hvec : ∀ t, E.endpointCount t + (if t ∈ A then 1 else 0) =
      D.endpointCount t + if u = t then #A else 0)
    (htight : ∀ w ∈ S \ A, passingNeighborCount E w = 2)
    (hregular : ∀ C ∈ F, C ∉ special →
      (∃ a : evenVertices G, (P C).image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        (P C).image Subtype.val = {(a : V)} ∧ 2 ≤ D.endpointCount b) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (P C).image Subtype.val = {(a : V),(b : V),(c : V)}))
    (hspecial : ∀ C ∈ F, C ∈ special →
      ∃ a b c : evenVertices G, C.supp = {a,b,c} ∧ G.Adj a b ∧
        (P C).image Subtype.val = {(a : V),(b : V)}) :
    #((F.biUnion P).image Subtype.val \ A) + #F ≤
      #((F.biUnion P).image Subtype.val ∩ A) + #special := by
  classical
  apply ordinary_prepared_component_gain G F special P A hsupp
  · intro C hC hCs
    rcases hregular C hC hCs with ⟨a,hPa,hi⟩ | ⟨a,b,c,hs,hPa,hb⟩ |
      ⟨a,b,c,hs,hab,hbc,hca,hPabc⟩
    · have haS : (a : V) ∈ S := hPS C hC (by rw [hPa]; simp)
      have haA : (a : V) ∈ A := by
        by_contra hn
        have ht := Finset.mem_sdiff.mpr ⟨haS,hn⟩
        have hempty : {t ∈ (J ⊔ A.sup (SimpleGraph.edge u)).neighborFinset a |
            E.endpointCount t = 0} = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t hm
          obtain ⟨htN,htZero⟩ := Finset.mem_filter.mp hm
          have hat := ((J ⊔ A.sup (SimpleGraph.edge u)).mem_neighborFinset
            (a : V) t).mp htN
          have he : Even ((J ⊔ A.sup (SimpleGraph.edge u)).degree t) := by
            rw [Nat.even_iff]
            have hv := E.endpointCount_mod_two t
            rw [htZero] at hv
            omega
          rcases hp t he with he | rfl
          · exact hi t (hsub hat) he
          · exact hmissingE a ht hat
        have hz : passingNeighborCount E a = 0 := by
          change #{t ∈ (J ⊔ A.sup (SimpleGraph.edge u)).neighborFinset a |
            E.endpointCount t = 0} = 0
          rw [hempty]
          rfl
        have htwo := htight a ht
        omega
      rw [hPa]
      simp [haA]
    · have haS : (a : V) ∈ S := hPS C hC (by rw [hPa]; simp)
      rw [hPa]
      exact ordinary_prepared_regular_triangle_gain D u S A C a b c hs haS
        (fun he => huS (he ▸ haS)) (hmissing a haS) hb E hsub hp hvec htight
    · have haS : (a : V) ∈ S := hPS C hC (by rw [hPabc]; simp)
      have hbS : (b : V) ∈ S := hPS C hC (by rw [hPabc]; simp)
      have hcS : (c : V) ∈ S := hPS C hC (by rw [hPabc]; simp)
      rw [hPabc]
      exact ordinary_prepared_t3_gain u S A C a b c hs hab hbc hca haS hbS hcS
        D E hsub hp hpos hmissingE hvec htight
  · intro C hC hCs
    obtain ⟨a,b,c,hs,hab,hPab⟩ := hspecial C hC hCs
    have haS : (a : V) ∈ S := hPS C hC (by rw [hPab]; simp)
    have hbS : (b : V) ∈ S := hPS C hC (by rw [hPab]; simp)
    rw [hPab]
    exact ordinary_prepared_special_triangle_gain D u S A C a b c hs hab haS
      (fun he => huS (he ▸ haS)) (hmissing a haS) (hpos b hbS)
      E hsub hp hvec htight
end Prepared

end Gallai.TwoException
