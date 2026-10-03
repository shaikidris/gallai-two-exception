/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE2
public import Gallai.TwoException.EarlyT3E4Retained

@[expose] public section

/-! # Double-spoke restoration with the opposite triangle mate absent -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E2Graph (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- E2 restores its contact packet before the ordinary opposite mate.
The protected endpoint reserve survives both operations. -/
theorem restore_t3_E2
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c) :
    let Q := G.deleteEdges {s((b : V),(c : V))}
    ∀ (u x p q h : V) (S : Finset V),
    u ∉ S → (a : V) ∉ S → u ≠ (a : V) →
    Odd (Q.degree u) → Odd #S → Q.Adj u a →
    (∀ t ∈ S, Q.Adj u t) → (∀ t ∈ S, Even (Q.degree t)) →
    p ∈ S → (∀ w ∈ S, w ≠ p → eDegree Q w ≤ 2) →
    (∀ w ∈ S, ¬ Q.Adj a w) →
    x ≠ u → x ≠ (a : V) → x ∉ S →
    q ≠ u → q ≠ (a : V) → q ∉ S →
    Q.Adj x q → Even (Q.degree x) → Even (Q.degree q) →
    ¬ Q.Adj q a →
    (∀ t, Q.Adj q t → Even (Q.degree t) → t = x ∨ t = p) →
    ¬ Q.Adj a x → ¬ Q.Adj u x →
    h ≠ u → h ≠ (a : V) → h ≠ x → h ≠ q → h ∉ S →
    h ≠ (b : V) → h ≠ (c : V) →
    ∀ D : Decomposition ((starPuncture Q u (insert (a : V) S)).deleteEdges {s(x,q)}),
    2 ≤ D.endpointCount h →
    (∀ t, Q.Adj u t → t ∉ S → t ≠ q →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t) →
    (∀ t, (starPuncture Q u (insert (a : V) S)).Adj a t →
      0 < D.endpointCount t) →
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  dsimp only
  intro u x p q h S hu ha hua huOdd hodd huAdj hadj heven hp hcap hsep
    hxu hxa hxS hqu hqa hqS hxq hxEven hqEven hqaAdj hpair hax hux
    hhu hha hhx hhq hhS hhb hhc D hh hretained hpositive
  obtain ⟨F,hs,_,haF,hkeep⟩ := restore_contact_E2 u a x p q h S hu ha hua
    huOdd hodd huAdj hadj heven hp hcap hsep hxu hxa hxS hqu hqa hqS
    hxq hxEven hqEven hqaAdj hpair hax hux hhu hha hhx hhq hhS
    D hretained hpositive
  obtain ⟨E,he,_,hkeepE⟩ := restore_t3_opposite_mate Z a b c hsupp hbc F (by omega)
  refine ⟨E,he.trans hs,?_⟩
  rw [hkeepE h hhb hhc,hkeep]
  exact hh

/-- Original contact classification supplies E2's retained-neighbour
guard, exempting only the recipient of the restored double spoke. -/
theorem t3_E2_retained_guard
    (a b c : evenVertices G) (hbc : G.Adj b c)
    (u x q h : V) (S : Finset V)
    (hab : (a : V) ≠ (b : V)) (hac : (a : V) ≠ (c : V))
    (hau : (a : V) ≠ u) (hua : G.Adj u a)
    (haq : (a : V) ≠ q) (hax : (a : V) ≠ x)
    (hbu : (b : V) ≠ u) (hcu : (c : V) ≠ u)
    (hcontacts : ∀ t, G.Adj u t → Even (G.degree t) →
      t ∈ S ∨ t = (a : V) ∨ t = q ∨ t = (b : V) ∨ t = (c : V) ∨ t = h)
    (D : Decomposition ((starPuncture (G.deleteEdges {s((b : V),(c : V))}) u
      (insert (a : V) S)).deleteEdges {s(x,q)}))
    (hh : 2 ≤ D.endpointCount h) :
    ∀ t, (G.deleteEdges {s((b : V),(c : V))}).Adj u t → t ∉ S → t ≠ q →
      Odd ((G.deleteEdges {s((b : V),(c : V))}).degree t) ∨
      0 < D.endpointCount t := by
  exact t3_E4_retained_guard a b c hbc u q x h S hab hac hau hua haq hax
    hbu hcu hcontacts D hh

end Gallai.TwoException
