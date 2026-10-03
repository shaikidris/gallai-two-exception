/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.ContactE4
public import Gallai.TwoException.EarlyT3MateRestoration

@[expose] public section

/-! # E4 restoration with the opposite T3 mate still absent -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance t3E4Graph (Q : SimpleGraph V) : DecidableRel Q.Adj :=
  fun _ _ => Classical.propDecidable _

/-- The E4 contact schedule exposes the reserved triangle vertex; its
opposite mate then restores at no path cost, retaining the protected reserve.
The retained-neighbour guards concern the actual intermediate graphs. -/
theorem restore_t3_E4
    (Z : (evenSubgraph G).ConnectedComponent) (a b c : evenVertices G)
    (hsupp : Z.supp = {a,b,c}) (hbc : G.Adj b c) :
    let Q := G.deleteEdges {s((b : V),(c : V))}
    ∀ (u x p q h : V) (S : Finset V),
    u ∉ S → (a : V) ∉ S → u ≠ (a : V) →
    Odd (Q.degree u) → Odd #S → Q.Adj u a →
    (∀ t ∈ S, Q.Adj u t) → (∀ t ∈ S, Even (Q.degree t)) →
    x ∈ S → (∀ w ∈ S, w ≠ x → eDegree Q w ≤ 2) →
    (∀ w ∈ S, ¬ Q.Adj a w) →
    q ≠ u → q ≠ (a : V) → q ∉ S →
    p ≠ u → p ≠ (a : V) → p ∉ S →
    Q.Adj q p → Even (Q.degree q) → Even (Q.degree p) →
    ¬ Q.Adj p a →
    (∀ t, Q.Adj p t → Even (Q.degree t) → t = x ∨ t = q) →
    ¬ Q.Adj a q → ¬ Q.Adj u q →
    h ≠ u → h ≠ (a : V) → h ≠ q → h ≠ p → h ∉ S →
    h ≠ (b : V) → h ≠ (c : V) →
    ∀ D : Decomposition ((starPuncture Q u (insert (a : V) S)).deleteEdges {s(q,p)}),
    2 ≤ D.endpointCount h →
    (∀ t, Q.Adj u t → t ∉ S → t ≠ p →
      Odd (Q.degree t) ∨ 0 < D.endpointCount t) →
    (∀ t, (starPuncture Q u (insert (a : V) S)).Adj a t →
      0 < D.endpointCount t) →
    ∃ E : Decomposition G, E.size = D.size ∧ 2 ≤ E.endpointCount h := by
  dsimp only
  intro u x p q h S hu ha hua huOdd hodd huAdj hadj heven hx hcap hsep
    hqu hqa hqS hpu hpa hpS hqp hqEven hpEven hpaAdj hpair haq huq
    hhu hha hhq hhp hhS hhb hhc D hh hretained hpositive
  obtain ⟨F,hs,_,haF,hkeep⟩ := restore_contact_E4 u a x p q h S hu ha hua
    huOdd hodd huAdj hadj heven hx hcap hsep hqu hqa hqS hpu hpa hpS
    hqp hqEven hpEven hpaAdj hpair haq huq hhu hha hhq hhp hhS D
    hretained hpositive
  obtain ⟨E,he,_,hkeepE⟩ := restore_t3_opposite_mate Z a b c hsupp hbc F (by omega)
  refine ⟨E,he.trans hs,?_⟩
  rw [hkeepE h hhb hhc,hkeep]
  exact hh

end Gallai.TwoException
