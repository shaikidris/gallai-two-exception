/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE1
public import Gallai.TwoException.EarlyT3MateRestoration

@[expose] public section

/-! # Non-hub single-spoke restoration followed by the T3 mate -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E1Graph (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- E1 restores the private spoke and contact packet with the opposite
ordinary mate absent. Its gained reserved endpoint restores that mate,
preserving the protected reserve and path count. -/
theorem restore_t3_E1
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c) :
    let Q := G.deleteEdges {s((b : V),(c : V))}
    ∀ (u x p q r h : V) (S : Finset V),
    u ∉ S → (a : V) ∉ S → u ≠ (a : V) →
    Odd (Q.degree u) → Odd #S → Q.Adj u a →
    (∀ t ∈ S, Q.Adj u t) → (∀ t ∈ S, Even (Q.degree t)) →
    p ∈ S → r ∈ S → (∀ w ∈ S, w ≠ r → eDegree Q w ≤ 2) →
    (∀ w ∈ S, ¬ Q.Adj a w) →
    x ≠ u → x ≠ (a : V) → x ∉ S →
    ¬ Q.Adj q u → ¬ Q.Adj q a → q ≠ u → q ≠ (a : V) →
    Q.Adj x q → Even (Q.degree x) →
    (∀ t, Q.Adj q t → Even (Q.degree t) → t = x ∨ t = p) →
    ¬ Q.Adj a x → ¬ Q.Adj u x →
    h ≠ u → h ≠ (a : V) → h ≠ x → h ≠ q → h ∉ S →
    h ≠ (b : V) → h ≠ (c : V) →
    ∀ D : Decomposition ((starPuncture Q u (insert (a : V) S)).deleteEdges {s(x,q)}),
    2 ≤ D.endpointCount h →
    (∀ t, Q.Adj u t → t ∉ S → Odd (Q.degree t) ∨ 0 < D.endpointCount t) →
    (∀ t, (starPuncture Q u (insert (a : V) S)).Adj a t → 0 < D.endpointCount t) →
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  dsimp only
  intro u x p q r h S hu ha hua huOdd hodd huAdj hadj heven hp hr hcap hsep
    hxu hxa hxS hquAdj hqaAdj hqu hqa hxq hxEven hpair hax hux
    hhu hha hhx hhq hhS hhb hhc D hh hretained hpositive
  obtain ⟨F,hs,_,haF,hkeep⟩ := restore_contact_E1 u a x p q r h S hu ha hua
    huOdd hodd huAdj hadj heven hp hr hcap hsep hxu hxa hxS hquAdj hqaAdj
    hqu hqa hxq hxEven hpair hax hux hhu hha hhx hhq hhS D hretained hpositive
  obtain ⟨E,he,_,hkeepE⟩ := restore_t3_opposite_mate Z a b c hsupp hbc F (by omega)
  refine ⟨E,he.trans hs,?_⟩
  rw [hkeepE h hhb hhc,hkeep]
  exact hh

end Gallai.TwoException
