/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE5
public import Gallai.TwoException.EarlyT3MateRestoration

@[expose] public section

/-! # Two-single-petal restoration before the opposite triangle mate -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E5Graph (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- Restore E5 with the ordinary mate absent, then spend its reserved
endpoint surplus to restore that mate at constant path count. -/
theorem restore_t3_E5
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c) :
    let Q := G.deleteEdges {s((b : V),(c : V))}
    ∀ (u x s p q r h : V) (S : Finset V),
    u ∉ S → (a : V) ∉ S → u ≠ (a : V) →
    Odd (Q.degree u) → Odd #S → Q.Adj u a →
    (∀ t ∈ S, Q.Adj u t) → (∀ t ∈ S, Even (Q.degree t)) →
    r ∈ S → (∀ w ∈ S, w ≠ r → eDegree Q w ≤ 2) →
    (∀ w ∈ S, ¬ Q.Adj a w) →
    x ≠ u → x ≠ (a : V) → x ∉ S → s ≠ u →
    Q.Adj x s → Even (Q.degree x) → Even (Q.degree s) →
    ¬ Q.Adj p a →
    (∀ t, Q.Adj p t → Even (Q.degree t) → t = x ∨ t = q) →
    p ≠ u → p ≠ (a : V) → p ∉ S → p ≠ x → p ≠ s →
    q ≠ u → q ≠ (a : V) → q ∉ S → q ≠ x → q ≠ s →
    Q.Adj q p → Even (Q.degree p) → Even (Q.degree q) →
    ¬ Q.Adj s u → ¬ Q.Adj s a →
    (∀ t, Q.Adj s t → Even (Q.degree t) → t = x ∨ t = r) →
    ¬ Q.Adj a x → ¬ Q.Adj a q → ¬ Q.Adj u x → ¬ Q.Adj u q →
    h ≠ u → h ≠ (a : V) → h ∉ S →
    h ≠ x → h ≠ s → h ≠ p → h ≠ q → h ≠ (b : V) → h ≠ (c : V) →
    ∀ D : Decomposition (((starPuncture Q u (insert (a : V) S)).deleteEdges {s(x,s)}).deleteEdges
      {s(q,p)}),
    2 ≤ D.endpointCount h →
    (∀ t, Q.Adj u t → t ∉ S → t ≠ p →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t) →
    (∀ t, (starPuncture Q u (insert (a : V) S)).Adj a t →
      0 < D.endpointCount t) →
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  dsimp only
  intro u x s p q r h S hu ha hua huOdd hodd huAdj hadj heven hr hcap hsep
    hxu hxa hxS hsu hxs hxEven hsEven hpa hpairP hpu hpv hpS hpx hps
    hqu hqv hqS hqx hqs hqp hpEven hqEven hsuAdj hsa hpairS
    hax haq hux huq hhu hha hhS hhx hhs hhp hhq hhb hhc D hh hretained hpositive
  obtain ⟨F,hs,_,haF,hkeep⟩ := restore_contact_E5 u a x s p q r h S
    hu ha hua huOdd hodd huAdj hadj heven hr hcap hsep
    hxu hxa hxS hsu hxs hxEven hsEven hpa hpairP hpu hpv hpS hpx hps
    hqu hqv hqS hqx hqs hqp hpEven hqEven hsuAdj hsa hpairS
    hax haq hux huq hhu hha hhS hhx hhs hhp hhq D hretained hpositive
  obtain ⟨E,he,_,hkeepE⟩ := restore_t3_opposite_mate Z a b c hsupp hbc F (by omega)
  refine ⟨E,he.trans hs,?_⟩
  rw [hkeepE h hhb hhc,hkeep]
  exact hh

end Gallai.TwoException
