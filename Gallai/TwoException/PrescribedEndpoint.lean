/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.PrescribedCutSelection
public import Gallai.TwoException.AdjacentFinal
public import Gallai.TwoException.SimultaneousEndpoint

@[expose] public section

/-! # One prescribed endpoint in the two-exception class -/

namespace Gallai.TwoException
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A positive even vertex can be exposed twice within the ceiling budget
when every even vertex outside it and one other even vertex has E-degree
at most three. Neither exception has a degree bound or a non-cut hypothesis. -/
theorem prescribed_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (h x : V)
    (hconn : G.Connected) (hhne : h ≠ x) (hhpos : 0 < G.degree h)
    (hhEven : Even (G.degree h)) (hxEven : Even (G.degree x))
    (hcap : ∀ a, Even (G.degree a) → a ≠ h → a ≠ x → eDegree G a ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount h := by
  classical
  have hall := lexicographic_finite_graph_induction
    (fun {W} _ _ (J : SimpleGraph W) _ =>
      ∀ a b : W, J.Connected → a ≠ b → 0 < J.degree a →
        Even (J.degree a) → Even (J.degree b) →
        (∀ t, Even (J.degree t) → t ≠ a → t ≠ b → eDegree J t ≤ 3) →
        BareConclusion J a)
    (by
      intro n W _ _ J _ hW hvertex hedge a b hc hab hp ha hb hcapJ
      by_cases hadj : J.Adj a b
      · exact (adjacent_endpoint J a b ⟨hc, hab, hadj, ha, hb, hcapJ⟩).1
      by_cases hn : Even (Fintype.card W)
      · have hv : ∀ (U : Type u) [Fintype U] [DecidableEq U]
            (K : SimpleGraph U) [DecidableRel K.Adj],
            Fintype.card U < Fintype.card W → K.Connected →
            ∀ c d : U, c ≠ d → 0 < K.degree c → Even (K.degree c) →
            Even (K.degree d) →
            (∀ t, Even (K.degree t) → t ≠ c → t ≠ d → eDegree K t ≤ 3) →
            BareConclusion K c := by
          intro U _ _ K _ hlt hK c d hcd hcp hce hde hcapK
          exact hvertex (Fintype.card U) (by omega) U K rfl
            c d hK hcd hcp hce hde hcapK
        have he : ∀ (K : SimpleGraph W) [DecidableRel K.Adj],
            K.edgeFinset.card < J.edgeFinset.card → K.Connected →
            ∀ c d : W, c ≠ d → 0 < K.degree c → Even (K.degree c) →
            Even (K.degree d) →
            (∀ t, Even (K.degree t) → t ≠ c → t ≠ d → eDegree K t ≤ 3) →
            BareConclusion K c := by
          intro K _ hlt hK c d hcd hcp hce hde hcapK
          exact hedge K hlt c d hK hcd hcp hce hde hcapK
        by_cases hcut : (J.induce {t | t ≠ a}).Connected
        · exact prescribed_noncut_reducible a b hc hab hp ha hb hadj hcut hcapJ he
        · exact prescribed_even_order_cut_reducible J a b hc hab hp ha hb hadj hn
            hcut hcapJ hv he
      · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hn
        obtain ⟨D, hd, hhD, _⟩ := odd_order_simultaneous m (by omega)
          hc a b hab ha hb hcapJ
        exact ⟨D, by omega, hhD⟩)
  exact hall V G h x hconn hhne hhpos hhEven hxEven hcap

end Gallai.TwoException
