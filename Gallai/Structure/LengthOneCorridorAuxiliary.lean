/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.ThreeSpokePuncture
public import Gallai.Structure.PendantExtension
public import Gallai.Structure.SET
public import Gallai.Inputs.FloorOrSET
public import Gallai.Inputs.HalfStar
public import Gallai.Operations.ComponentAssembly

@[expose] public section

/-! # The length-one corridor auxiliary

The first literal degree-three hub branch deletes the three spokes at `a` and
attaches one fresh pendant edge at the bare prescribed vertex `h`.  This file
only proves the degree-parity ledger of that auxiliary; it deliberately does
not assert the later component, SET, or path-decomposition consequences.
-/

namespace Gallai

open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The length-one corridor auxiliary: puncture three spokes at `a`, then add
a fresh pendant edge at the distinct bare vertex `h`. -/
abbrev lengthOneCorridorAuxiliary (h a x q r : V) : SimpleGraph (V ⊕ Unit) :=
  pendantExtension (threeSpokePuncture G a x q r) h

/-- The three old leaves of the literal length-one puncture, viewed in the
extended vertex type.  This is the star supplied to the prescribed half-star
interface during restoration. -/
def lengthOneCorridorLeaves (x q r : V) : Finset (V ⊕ Unit) :=
  {(.inl x : V ⊕ Unit), .inl q, .inl r}

/-- The literal three-spoke leaf set is exactly the lift of its old leaves. -/
theorem lengthOneCorridorLeaves_eq_pendantOldLeaves (x q r : V) :
    lengthOneCorridorLeaves x q r =
      pendantOldLeaves ({x, q, r} : Finset V) := by
  ext z
  cases z <;> simp [lengthOneCorridorLeaves, pendantOldLeaves]

/-- No selected subfamily of the literal three-spoke leaves contains the
fresh pendant vertex.  Hence it has the canonical old-vertex preimage. -/
theorem subset_lengthOneCorridorLeaves_not_mem_new
    (x q r : V) (B : Finset (V ⊕ Unit))
    (hB : B ⊆ lengthOneCorridorLeaves x q r) :
    (.inr () : V ⊕ Unit) ∉ B := by
  intro hnew
  have := hB hnew
  simp [lengthOneCorridorLeaves] at this

/-- A selected subfamily of the lifted literal three-spoke set which contains
the prescribed hub spoke has the same three cases as its old-vertex
preimage.  This discharges the only finite case split after a half-star
transformation without conflating the old and pendant vertex types. -/
theorem literal_three_star_selected_cases_lifted
    (B : Finset (V ⊕ Unit)) (x q r : V)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (hsub : B ⊆ lengthOneCorridorLeaves x q r)
    (hxB : (.inl x : V ⊕ Unit) ∈ B) (hBcard : 2 ≤ #B) :
    B = lengthOneCorridorLeaves x q r ∨
      B = ({(.inl x : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)) ∨
      B = ({(.inl x : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)) := by
  let C : Finset V := pendantOldPreimage B
  have hnew : (.inr () : V ⊕ Unit) ∉ B :=
    subset_lengthOneCorridorLeaves_not_mem_new x q r B hsub
  have hpre : pendantOldLeaves C = B := pendantOldLeaves_preimage_eq B hnew
  have hsubC : C ⊆ ({x, q, r} : Finset V) := by
    intro v hv
    have hvB : (.inl v : V ⊕ Unit) ∈ B := by
      simpa [C, pendantOldPreimage] using hv
    have hvL := hsub hvB
    rw [lengthOneCorridorLeaves_eq_pendantOldLeaves] at hvL
    simpa using hvL
  have hxC : x ∈ C := by
    simpa [C, pendantOldPreimage] using hxB
  have hcardC : 2 ≤ #C := by
    have hcard : #C = #B := by
      rw [← hpre]
      simp [pendantOldLeaves]
    omega
  rcases Decomposition.literal_three_star_selected_cases C x q r hxq hxr hqr
      hsubC hxC hcardC with hfull | hpair | hpair
  · left
    rw [← hpre, hfull, lengthOneCorridorLeaves_eq_pendantOldLeaves]
  · right; left
    rw [← hpre, hpair]
    ext z
    cases z <;> simp [pendantOldLeaves]
  · right; right
    rw [← hpre, hpair]
    ext z
    cases z <;> simp [pendantOldLeaves]

/-- The type-changing length-one auxiliary is exactly the old pendant
extension with the three `a`-spokes deleted.  This graph equality—not merely
an edge-set inclusion—aligns the literal corridor construction with the
half-star restoration interface. -/
theorem lengthOneCorridorAuxiliary_eq_starPuncture
    (h a x q r : V) :
    lengthOneCorridorAuxiliary G h a x q r =
      starPuncture (pendantExtension G h) (.inl a)
        (lengthOneCorridorLeaves x q r) := by
  ext u v
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      by_cases huv : G.Adj u v
      · have hne : u ≠ v := huv.ne
        simp [lengthOneCorridorAuxiliary, lengthOneCorridorLeaves, pendantExtension,
          threeSpokePuncture, starPuncture, SimpleGraph.deleteEdges_adj,
          SimpleGraph.sdiff_adj, SimpleGraph.map_adj, SimpleGraph.edge_adj, huv, hne]
        aesop
      · simp [lengthOneCorridorAuxiliary, lengthOneCorridorLeaves, pendantExtension,
          threeSpokePuncture, starPuncture, SimpleGraph.deleteEdges_adj,
          SimpleGraph.sdiff_adj, SimpleGraph.map_adj, SimpleGraph.edge_adj, huv]
    | inr z =>
      cases z
      simp [lengthOneCorridorAuxiliary, lengthOneCorridorLeaves, pendantExtension,
        threeSpokePuncture, starPuncture, SimpleGraph.deleteEdges_adj,
        SimpleGraph.sdiff_adj, SimpleGraph.map_adj, SimpleGraph.edge_adj]
  | inr z =>
    cases z
    cases v <;>
      simp [lengthOneCorridorAuxiliary, lengthOneCorridorLeaves, pendantExtension,
        threeSpokePuncture, starPuncture, SimpleGraph.deleteEdges_adj,
        SimpleGraph.sdiff_adj, SimpleGraph.map_adj, SimpleGraph.edge_adj]

/-- Restoring all three literal corridor spokes in the pendant auxiliary
returns exactly the pendant extension of the original old graph.  This is
the no-pending-leaf branch before the terminal pendant return. -/
theorem lengthOneCorridorAuxiliary_restore_all_eq_pendantExtension
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    lengthOneCorridorAuxiliary G h a x q r ⊔
      (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
        pendantExtension G h := by
  have hstar : ({x, q, r} : Finset V).sup (SimpleGraph.edge a) ≤ G := by
    apply Finset.sup_le
    intro v hv
    have hav : G.Adj a v := by
      rcases (by simpa using hv : v = x ∨ v = q ∨ v = r) with hV | hV | hV
      · simpa [hV] using hax
      · simpa [hV] using haq
      · simpa [hV] using har
    intro u w huv
    rw [SimpleGraph.edge_adj] at huv
    rcases huv.1 with ⟨hua, hwv⟩ | ⟨huv, hwa⟩
    · subst u
      subst w
      exact hav
    · subst u
      subst w
      exact hav.symm
  have hsup : G ⊔ ({x, q, r} : Finset V).sup (SimpleGraph.edge a) = G := by
    ext u v
    simp only [SimpleGraph.sup_adj]
    constructor
    · rintro (huv | huv)
      · exact huv
      · exact hstar huv
    · exact Or.inl
  calc
    lengthOneCorridorAuxiliary G h a x q r ⊔
        (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
        starPuncture (pendantExtension G h) (.inl a)
          (lengthOneCorridorLeaves x q r) ⊔
          (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)) := by
            rw [← lengthOneCorridorAuxiliary_eq_starPuncture]
    _ = pendantExtension G h ⊔
          (lengthOneCorridorLeaves x q r).sup (SimpleGraph.edge (.inl a : V ⊕ Unit)) :=
        starPuncture_sup_star_eq_sup _ _ _
    _ = pendantExtension G h ⊔ pendantOldStar a ({x, q, r} : Finset V) := by
        rw [lengthOneCorridorLeaves_eq_pendantOldLeaves]
        rfl
    _ = pendantExtension (G ⊔ ({x, q, r} : Finset V).sup (SimpleGraph.edge a)) h := by
        rw [pendantExtension_sup_star]
    _ = pendantExtension G h := by rw [hsup]

/-- Restoring `ax` and `aq` in the literal pendant auxiliary leaves exactly
the lifted one-edge puncture at `ar`.  This is the first singleton-pending
branch that will consume the strict final-edge restoration. -/
theorem lengthOneCorridorAuxiliary_restore_ax_aq_eq_pendantDelete_ar
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    lengthOneCorridorAuxiliary G h a x q r ⊔
      ({(.inl x : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)).sup
        (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
      pendantExtension (G.deleteEdges {s(a, r)}) h := by
  have hleaves : ({(.inl x : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)) =
      pendantOldLeaves ({x, q} : Finset V) := by
    ext z
    cases z <;> simp [pendantOldLeaves]
  calc
    lengthOneCorridorAuxiliary G h a x q r ⊔
        ({(.inl x : V ⊕ Unit), .inl q} : Finset (V ⊕ Unit)).sup
          (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
        pendantExtension (threeSpokePuncture G a x q r) h ⊔
          pendantOldStar a ({x, q} : Finset V) := by
            rw [hleaves]
            rfl
    _ = pendantExtension
          (threeSpokePuncture G a x q r ⊔
            ({x, q} : Finset V).sup (SimpleGraph.edge a)) h := by
          rw [pendantExtension_sup_star]
    _ = pendantExtension (G.deleteEdges {s(a, r)}) h := by
          rw [threeSpokePuncture_restore_ax_aq_eq_delete_ar G a x q r
            hax haq hxq hxr hqr]

/-- Symmetrically, restoring `ax` and `ar` leaves the lifted one-edge
puncture at `aq`. -/
theorem lengthOneCorridorAuxiliary_restore_ax_ar_eq_pendantDelete_aq
    (h a x q r : V)
    (hax : G.Adj a x) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r) :
    lengthOneCorridorAuxiliary G h a x q r ⊔
      ({(.inl x : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)).sup
        (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
      pendantExtension (G.deleteEdges {s(a, q)}) h := by
  have hleaves : ({(.inl x : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)) =
      pendantOldLeaves ({x, r} : Finset V) := by
    ext z
    cases z <;> simp [pendantOldLeaves]
  calc
    lengthOneCorridorAuxiliary G h a x q r ⊔
        ({(.inl x : V ⊕ Unit), .inl r} : Finset (V ⊕ Unit)).sup
          (SimpleGraph.edge (.inl a : V ⊕ Unit)) =
        pendantExtension (threeSpokePuncture G a x q r) h ⊔
          pendantOldStar a ({x, r} : Finset V) := by
            rw [hleaves]
            rfl
    _ = pendantExtension
          (threeSpokePuncture G a x q r ⊔
            ({x, r} : Finset V).sup (SimpleGraph.edge a)) h := by
          rw [pendantExtension_sup_star]
    _ = pendantExtension (G.deleteEdges {s(a, q)}) h := by
          rw [threeSpokePuncture_restore_ax_ar_eq_delete_aq G a x q r
            hax har hxq hxr hqr]

/-- The old vertices belonging to an auxiliary component.  When the component
does not contain the fresh pendant leaf, this is its entire vertex type up to
the canonical `inl` embedding. -/
def lengthOneCorridorAuxiliary_oldSet
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent) : Set V :=
  {v | (.inl v : V ⊕ Unit) ∈ C.supp}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_lengthOneCorridorAuxiliary_oldSet
    (h a x q r v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent) :
    v ∈ lengthOneCorridorAuxiliary_oldSet G h a x q r C ↔
      (.inl v : V ⊕ Unit) ∈ C.supp := Iff.rfl

/-- If the fresh pendant leaf is outside an auxiliary component, the old
component set and the component support have canonically equivalent vertex
types.  This is the type-level half of the later induced-SET transport. -/
noncomputable def lengthOneCorridorAuxiliary_oldComponentEquiv
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    C.supp ≃ lengthOneCorridorAuxiliary_oldSet G h a x q r C where
  toFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl v => exact ⟨v, hz⟩
    | inr u => cases u; exact False.elim (hleaf hz)
  invFun z := ⟨.inl z.val, z.property⟩
  left_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl v => rfl
    | inr u => cases u; exact False.elim (hleaf hz)
  right_inv z := by
    rcases z with ⟨z, hz⟩
    rfl

/-- Once the fresh leaf and deleted centre lie outside an auxiliary component,
its induced graph is isomorphic to the original graph induced on its old
vertices.  Every deleted spoke is incident with the excluded centre, while the
pendant edge is incident with the excluded fresh leaf. -/
noncomputable def lengthOneCorridorAuxiliary_oldComponentIso
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp) :
    (lengthOneCorridorAuxiliary G h a x q r).induce C.supp ≃g
      G.induce (lengthOneCorridorAuxiliary_oldSet G h a x q r C) where
  __ := lengthOneCorridorAuxiliary_oldComponentEquiv G h a x q r C hleaf
  map_rel_iff' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        change G.Adj u v ↔
          (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl u) (.inl v)
        rw [pendantExtension_adj_old]
        symm
        apply threeSpokePuncture_adj_iff_of_ne_center
        · intro e
          exact ha (e ▸ hu)
        · intro e
          exact ha (e ▸ hv)
      | inr z =>
        cases z
        exact False.elim (hleaf hv)
    | inr z =>
      cases z
      exact False.elim (hleaf hu)

omit [DecidableEq V] in
/-- A SET certificate on an all-old component of the pendant auxiliary
transports to the original graph induced on that component's old vertices.
The only graph changes are incident with the excluded deleted centre or the
excluded fresh pendant leaf. -/
theorem lengthOneCorridorAuxiliary_old_component_isSET
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    [DecidablePred (· ∈ lengthOneCorridorAuxiliary_oldSet G h a x q r C)]
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    IsSET (G.induce (lengthOneCorridorAuxiliary_oldSet G h a x q r C)) := by
  classical
  exact SimpleGraph.Iso.isSET_map
    (lengthOneCorridorAuxiliary_oldComponentIso G h a x q r C hleaf ha) hset

omit [DecidableRel G.Adj] in
/-- A SET component of the pendant auxiliary that contains an old vertex `q`
and excludes the fresh leaf contains a second, distinct old vertex.  This is
an intrinsic SET consequence: the induced degree of `q` is at least two. -/
theorem lengthOneCorridorAuxiliary_set_component_exists_second_old
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hq : (.inl q : V ⊕ Unit) ∈ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    ∃ t : V, (.inl t : V ⊕ Unit) ∈ C.supp ∧ t ≠ q := by
  let qC : C.supp := ⟨.inl q, hq⟩
  have hdegree : 2 ≤ ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).degree qC :=
    hset.two_le_degree qC
  have hcard : 0 <
      (((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).neighborFinset qC).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  cases hzval : z.val with
  | inl t =>
    have hzC : (.inl t : V ⊕ Unit) ∈ C.supp := by
      simpa [hzval] using z.property
    refine ⟨t, hzC, ?_⟩
    intro htq
    have hAdj : ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).Adj qC z := by
      simpa using hz
    apply hAdj.ne
    apply Subtype.ext
    simp [qC, hzval, htq]
  | inr u =>
    cases u
    apply False.elim
    apply hleaf
    simpa [hzval] using z.property

omit [DecidableRel G.Adj] in
/-- A SET component of the pendant auxiliary containing any old vertex and
excluding the fresh leaf contains a distinct second old vertex. -/
theorem lengthOneCorridorAuxiliary_set_component_exists_second_old_of_mem
    (h a x q r v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hv : (.inl v : V ⊕ Unit) ∈ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    ∃ t : V, (.inl t : V ⊕ Unit) ∈ C.supp ∧ t ≠ v := by
  let vC : C.supp := ⟨.inl v, hv⟩
  have hdegree : 2 ≤ ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).degree vC :=
    hset.two_le_degree vC
  have hcard : 0 <
      (((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).neighborFinset vC).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
  cases hzval : z.val with
  | inl t =>
    have hzC : (.inl t : V ⊕ Unit) ∈ C.supp := by
      simpa [hzval] using z.property
    refine ⟨t, hzC, ?_⟩
    intro htv
    have hAdj : ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).Adj vC z := by
      simpa using hz
    apply hAdj.ne
    apply Subtype.ext
    simp [vC, hzval, htv]
  | inr u =>
    cases u
    apply False.elim
    apply hleaf
    simpa [hzval] using z.property

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every original old--old edge crossing a component of the length-one
pendant auxiliary is one of the three removed spokes.  This transports the
puncture-boundary invariant directly to an auxiliary component without first
constructing a separate component equivalence. -/
theorem lengthOneCorridorAuxiliary_component_crossing_is_deleted
    (h a x q r u v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    s(u, v) = s(a, x) ∨ s(u, v) = s(a, q) ∨ s(u, v) = s(a, r) := by
  by_contra hbad
  push Not at hbad
  have h₁ : (G.deleteEdges {s(a, x)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simp [hbad.1]⟩
  have h₂ : ((G.deleteEdges {s(a, x)}).deleteEdges {s(a, q)}).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨h₁, by simp [hbad.2.1]⟩
  have h₃ : (threeSpokePuncture G a x q r).Adj u v :=
    SimpleGraph.deleteEdges_adj.mpr ⟨h₂, by simp [hbad.2.2]⟩
  have haux : (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl u) (.inl v) :=
    (pendantExtension_adj_old (threeSpokePuncture G a x q r) h u v).mpr h₃
  exact hv (C.mem_supp_of_adj_mem_supp hu haux)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The `q`-side orientation of the preceding auxiliary-component boundary
extraction. -/
theorem lengthOneCorridorAuxiliary_component_crossing_is_qa
    (h a x q r u v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    u = q ∧ v = a := by
  rcases lengthOneCorridorAuxiliary_component_crossing_is_deleted
      G h a x q r u v C hu hv huv with hax | haq | har
  · rcases Sym2.eq_iff.mp hax with ⟨hua, hvx⟩ | ⟨hux, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hx (hux ▸ hu)).elim
  · rcases Sym2.eq_iff.mp haq with ⟨hua, hvq⟩ | ⟨huq, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact ⟨huq, hva⟩
  · rcases Sym2.eq_iff.mp har with ⟨hua, hvr⟩ | ⟨hur, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hr (hur ▸ hu)).elim

omit [Fintype V] [DecidableRel G.Adj] in
/-- The symmetric `r`-side orientation of an auxiliary-component boundary. -/
theorem lengthOneCorridorAuxiliary_component_crossing_is_ra
    (h a x q r u v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hx : (.inl x : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    u = r ∧ v = a := by
  rcases lengthOneCorridorAuxiliary_component_crossing_is_deleted
      G h a x q r u v C hu hv huv with hax | haq | har
  · rcases Sym2.eq_iff.mp hax with ⟨hua, hvx⟩ | ⟨hux, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hx (hux ▸ hu)).elim
  · rcases Sym2.eq_iff.mp haq with ⟨hua, hvq⟩ | ⟨huq, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hq (huq ▸ hu)).elim
  · rcases Sym2.eq_iff.mp har with ⟨hua, hvr⟩ | ⟨hur, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact ⟨hur, hva⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- If an auxiliary component contains only the `x`-side of the three
deleted spokes, its original boundary is exactly the deleted spoke `x-a`.
This is the boundary form used after deleting `x`: all remaining vertices of
the component are then separated from the pendant attachment. -/
theorem lengthOneCorridorAuxiliary_component_crossing_is_xa
    (h a x q r u v : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hq : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hr : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hu : (.inl u : V ⊕ Unit) ∈ C.supp)
    (hv : (.inl v : V ⊕ Unit) ∉ C.supp) (huv : G.Adj u v) :
    u = x ∧ v = a := by
  rcases lengthOneCorridorAuxiliary_component_crossing_is_deleted
      G h a x q r u v C hu hv huv with hax | haq | har
  · rcases Sym2.eq_iff.mp hax with ⟨hua, hvx⟩ | ⟨hux, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact ⟨hux, hva⟩
  · rcases Sym2.eq_iff.mp haq with ⟨hua, hvq⟩ | ⟨huq, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hq (huq ▸ hu)).elim
  · rcases Sym2.eq_iff.mp har with ⟨hua, hvr⟩ | ⟨hur, hva⟩
    · exact (ha (hua ▸ hu)).elim
    · exact (hr (hur ▸ hu)).elim

omit [DecidableRel G.Adj] in
/-- In a connected original graph, every length-one auxiliary component that
avoids the fresh pendant leaf and the deleted centre meets one of the three
deleted-spoke leaves.  Otherwise its old vertices are closed under every
original edge, contradicting connectedness to the deleted centre. -/
theorem lengthOneCorridorAuxiliary_component_meets_deleted_support
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (hconn : G.Connected)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (ha : (.inl a : V ⊕ Unit) ∉ C.supp) :
    (.inl x : V ⊕ Unit) ∈ C.supp ∨
      (.inl q : V ⊕ Unit) ∈ C.supp ∨ (.inl r : V ⊕ Unit) ∈ C.supp := by
  by_contra hnone
  have hx : (.inl x : V ⊕ Unit) ∉ C.supp := fun hx => hnone (Or.inl hx)
  have hq : (.inl q : V ⊕ Unit) ∉ C.supp := fun hq => hnone (Or.inr (Or.inl hq))
  have hr : (.inl r : V ⊕ Unit) ∉ C.supp := fun hr => hnone (Or.inr (Or.inr hr))
  obtain ⟨z, hz⟩ := C.nonempty_supp
  obtain ⟨u, hu⟩ : ∃ u : V, (.inl u : V ⊕ Unit) ∈ C.supp := by
    cases z with
    | inl u => exact ⟨u, hz⟩
    | inr z => cases z; exact False.elim (hleaf hz)
  have hclosed : ∀ u v : V, (.inl u : V ⊕ Unit) ∈ C.supp → G.Adj u v →
      (.inl v : V ⊕ Unit) ∈ C.supp := by
    intro u v hu huv
    by_contra hv
    rcases lengthOneCorridorAuxiliary_component_crossing_is_deleted
        G h a x q r u v C hu hv huv with huv | huv | huv
    · rcases Sym2.eq_iff.mp huv with ⟨hua, hvx⟩ | ⟨hux, hva⟩
      · exact ha (hua ▸ hu)
      · exact hx (hux ▸ hu)
    · rcases Sym2.eq_iff.mp huv with ⟨hua, hvq⟩ | ⟨huq, hva⟩
      · exact ha (hua ▸ hu)
      · exact hq (huq ▸ hu)
    · rcases Sym2.eq_iff.mp huv with ⟨hua, hvr⟩ | ⟨hur, hva⟩
      · exact ha (hua ▸ hu)
      · exact hr (hur ▸ hu)
  have hreach : G.Reachable u a := hconn u a
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hpreserve : ∀ {v : V}, Relation.ReflTransGen G.Adj u v →
      (.inl u : V ⊕ Unit) ∈ C.supp → (.inl v : V ⊕ Unit) ∈ C.supp := by
    intro v hv hu
    induction hv with
    | refl => exact hu
    | tail _ huv ih => exact hclosed _ _ ih huv
  have haC : (.inl a : V ⊕ Unit) ∈ C.supp := by
    exact hpreserve hreach hu
  exact ha haC

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Any auxiliary component excluding the fresh pendant leaf also excludes
its old attachment `h`. -/
theorem lengthOneCorridorAuxiliary_attachment_not_mem_of_leaf_not_mem
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp) :
    (.inl h : V ⊕ Unit) ∉ C.supp := by
  intro hh
  apply hleaf
  apply C.mem_supp_of_adj_mem_supp hh
  exact (pendantExtension_adj_new (threeSpokePuncture G a x q r) h (.inl h)).mpr rfl |>.symm

/-- All four vertices affected by the three-spoke puncture remain odd after a
pendant attachment at a distinct vertex; the attachment point and new leaf are
odd whenever the old attachment degree was even. -/
theorem lengthOneCorridorAuxiliary_odd_affected (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h)) :
    Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl a)) ∧
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl x)) ∧
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl q)) ∧
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl r)) ∧
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl h)) ∧
      Odd ((lengthOneCorridorAuxiliary G h a x q r).degree (.inr ())) := by
  obtain ⟨oa, ox, oq, or⟩ :=
    threeSpokePuncture_odd_affected G a x q r hax haq har hxq hxr hqr ha hx hq hr
  have ph : Even ((threeSpokePuncture G a x q r).degree h) := by
    rw [threeSpokePuncture_degree_away G a x q r h hha hhx hhq hhr]
    exact hh
  exact ⟨(pendantExtension_odd_old_ne (threeSpokePuncture G a x q r) h a hha.symm).mpr oa,
    (pendantExtension_odd_old_ne (threeSpokePuncture G a x q r) h x hhx.symm).mpr ox,
    (pendantExtension_odd_old_ne (threeSpokePuncture G a x q r) h q hhq.symm).mpr oq,
    (pendantExtension_odd_old_ne (threeSpokePuncture G a x q r) h r hhr.symm).mpr or,
    (pendantExtension_odd_attach_iff (threeSpokePuncture G a x q r) h).mpr ph,
    pendantExtension_odd_new (threeSpokePuncture G a x q r) h⟩

/-- Every old vertex that is even in the literal length-one auxiliary was
already even in the original graph.  The fresh pendant attachment has only
one exceptional old vertex, `h`, and it is odd here; the three-spoke parity
ledger handles the remaining old vertices. -/
theorem lengthOneCorridorAuxiliary_even_old_implies_original_even (h a x q r v : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hv : Even ((lengthOneCorridorAuxiliary G h a x q r).degree (.inl v))) :
    Even (G.degree v) := by
  obtain ⟨_, _, _, _, oh, _⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
  by_cases hvh : v = h
  · subst v
    exact False.elim ((Nat.not_even_iff_odd.mpr oh) hv)
  have hvP : Even ((threeSpokePuncture G a x q r).degree v) :=
    (pendantExtension_even_old_ne (threeSpokePuncture G a x q r) h v hvh).mp hv
  exact threeSpokePuncture_even_implies_original_even G a x q r
    hax haq har hxq hxr hqr ha hx hq hr v hvP

/-- An even neighbour of an old vertex in the length-one auxiliary is an old
vertex and is an even neighbour in the original graph.  This is the concrete
membership transport used to compare an auxiliary SET triangle with original
E-degree capacity. -/
theorem lengthOneCorridorAuxiliary_evenNeighbor_old_original
    (h a x q r v : V) (z : V ⊕ Unit)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hz : z ∈ evenNeighbors (lengthOneCorridorAuxiliary G h a x q r) (.inl v)) :
    ∃ w : V, z = .inl w ∧ w ∈ evenNeighbors G v := by
  obtain ⟨hvz, hzEven⟩ :=
    (mem_evenNeighbors (G := lengthOneCorridorAuxiliary G h a x q r) (.inl v) z).mp hz
  cases z with
  | inr u =>
    cases u
    obtain ⟨_, _, _, _, _, oleaf⟩ :=
      lengthOneCorridorAuxiliary_odd_affected G h a x q r
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
    exact False.elim ((Nat.not_even_iff_odd.mpr oleaf) hzEven)
  | inl w =>
    refine ⟨w, rfl, ?_⟩
    apply (mem_evenNeighbors (G := G) v w).mpr
    refine ⟨?_, ?_⟩
    · have hvwP : (threeSpokePuncture G a x q r).Adj v w :=
        (pendantExtension_adj_old (threeSpokePuncture G a x q r) h v w).mp hvz
      exact threeSpokePuncture_le G a x q r hvwP
    · exact lengthOneCorridorAuxiliary_even_old_implies_original_even G h a x q r w
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hzEven

/-- The preceding transport also applies to the induced graph on an actual
auxiliary component.  Component closure identifies induced degree parity with
auxiliary degree parity, so every SET-even neighbour inside that component is
an original even neighbour of the corresponding old vertex. -/
theorem lengthOneCorridorAuxiliary_component_evenNeighbor_old_original
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (v : V) (hv : (.inl v : V ⊕ Unit) ∈ C.supp) (z : C.supp)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hz : z ∈ evenNeighbors ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)
      ⟨.inl v, hv⟩) :
    ∃ w : V, z.val = .inl w ∧ w ∈ evenNeighbors G v := by
  obtain ⟨hvz, hzEven⟩ :=
    (mem_evenNeighbors (G := (lengthOneCorridorAuxiliary G h a x q r).induce C.supp)
      ⟨.inl v, hv⟩ z).mp hz
  have hclosed : ∀ u ∈ C.supp,
      (lengthOneCorridorAuxiliary G h a x q r).neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  have hzEvenAux : Even ((lengthOneCorridorAuxiliary G h a x q r).degree z.val) := by
    rw [← SimpleGraph.degree_induce_of_neighborSet_subset (hclosed z.val z.property)]
    exact hzEven
  have hvzAux : (lengthOneCorridorAuxiliary G h a x q r).Adj (.inl v) z.val := hvz
  have hzAux : z.val ∈ evenNeighbors (lengthOneCorridorAuxiliary G h a x q r) (.inl v) :=
    (mem_evenNeighbors (G := lengthOneCorridorAuxiliary G h a x q r) (.inl v) z.val).mpr
      ⟨hvzAux, hzEvenAux⟩
  exact lengthOneCorridorAuxiliary_evenNeighbor_old_original G h a x q r v z.val
    hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hzAux

/-- A SET component of the length-one auxiliary cannot contain both affected
vertices `x` and `q` under the original nonexceptional E-degree cap.  A common
SET-even neighbour supplies two internal original even neighbours; together
with `x` and `q` these are four distinct original even neighbours. -/
theorem lengthOneCorridorAuxiliary_set_component_not_contains_xq
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcap : ∀ u, Even (G.degree u) → u ≠ h → u ≠ x → eDegree G u ≤ 3)
    (hxC : (.inl x : V ⊕ Unit) ∈ C.supp)
    (hqC : (.inl q : V ⊕ Unit) ∈ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    False := by
  let A := lengthOneCorridorAuxiliary G h a x q r
  let K := A.induce C.supp
  have hclosed : ∀ u ∈ C.supp, A.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  obtain ⟨_, ox, oq, _, oh, _⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
  have hoddK : ∀ (u : V) (hu : (.inl u : V ⊕ Unit) ∈ C.supp),
      Odd (A.degree (.inl u)) → Odd (K.degree ⟨.inl u, hu⟩) := by
    intro u hu hou
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inl u) hu)]
    exact hou
  have oxK : Odd (K.degree ⟨.inl x, hxC⟩) := hoddK x hxC ox
  have oqK : Odd (K.degree ⟨.inl q, hqC⟩) := hoddK q hqC oq
  obtain ⟨wC, hxw, hqw, hwEvenK⟩ :=
    hset.exists_common_even_neighbor_of_odd ⟨.inl x, hxC⟩ ⟨.inl q, hqC⟩ oxK oqK
  have hxwMem : wC ∈ evenNeighbors K ⟨.inl x, hxC⟩ :=
    (mem_evenNeighbors (G := K) ⟨.inl x, hxC⟩ wC).mpr ⟨hxw, hwEvenK⟩
  obtain ⟨w, hwval, hwGx⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      x hxC wC hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hxwMem
  have hwC : (.inl w : V ⊕ Unit) ∈ C.supp := by
    simpa [hwval] using wC.property
  have hwCeq : wC = ⟨.inl w, hwC⟩ := Subtype.ext hwval
  subst wC
  have hdegW : eDegree K ⟨.inl w, hwC⟩ = 2 :=
    hset.eDegree_even ⟨.inl w, hwC⟩ hwEvenK
  change (evenNeighbors K ⟨.inl w, hwC⟩).card = 2 at hdegW
  obtain ⟨z₁, z₂, hz₁₂, hN⟩ := Finset.card_eq_two.mp hdegW
  have hz₁ : z₁ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  have hz₂ : z₂ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  obtain ⟨u₁, hz₁val, hu₁G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₁ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₁
  obtain ⟨u₂, hz₂val, hu₂G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₂ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₂
  have hz₁Even : Even (K.degree z₁) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₁).mp hz₁ |>.2
  have hz₂Even : Even (K.degree z₂) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₂).mp hz₂ |>.2
  have hu₁u₂ : u₁ ≠ u₂ := by
    intro e
    apply hz₁₂
    apply Subtype.ext
    calc
      z₁.val = .inl u₁ := hz₁val
      _ = .inl u₂ := by rw [e]
      _ = z₂.val := hz₂val.symm
  have hu₁x : u₁ ≠ x := by
    intro e
    have hz : z₁ = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr oxK) hz₁Even
  have hu₁q : u₁ ≠ q := by
    intro e
    have hz : z₁ = ⟨.inl q, hqC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr oqK) hz₁Even
  have hu₂x : u₂ ≠ x := by
    intro e
    have hz : z₂ = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr oxK) hz₂Even
  have hu₂q : u₂ ≠ q := by
    intro e
    have hz : z₂ = ⟨.inl q, hqC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr oqK) hz₂Even
  have hxGw : x ∈ evenNeighbors G w := by
    obtain ⟨hxwG, _⟩ := (mem_evenNeighbors (G := G) x w).mp hwGx
    exact (mem_evenNeighbors (G := G) w x).mpr ⟨hxwG.symm, hx⟩
  have hqGw : q ∈ evenNeighbors G w := by
    obtain ⟨hqwG, _⟩ := (mem_evenNeighbors (G := G) q w).mp
      (by
        have hqwMem : ⟨.inl w, hwC⟩ ∈ evenNeighbors K ⟨.inl q, hqC⟩ :=
          (mem_evenNeighbors (G := K) ⟨.inl q, hqC⟩ ⟨.inl w, hwC⟩).mpr
            ⟨hqw, hwEvenK⟩
        obtain ⟨w', hw'val, hw'Gq⟩ :=
          lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
            q hqC ⟨.inl w, hwC⟩ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hqwMem
        have ew : w' = w := by simpa using hw'val.symm
        simpa [ew] using hw'Gq)
    exact (mem_evenNeighbors (G := G) w q).mpr ⟨hqwG.symm, hq⟩
  have hwEvenG : Even (G.degree w) := (mem_evenNeighbors (G := G) x w).mp hwGx |>.2
  have hwx : w ≠ x := by
    intro e
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr oxK) hwEvenK
  have hwh : w ≠ h := by
    intro e
    have hhC : (.inl h : V ⊕ Unit) ∈ C.supp := by simpa [e] using hwC
    have ohK := hoddK h hhC oh
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl h, hhC⟩ := Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr ohK) hwEvenK
  have hfour := eDegree_ge_four_of_four_distinct_evenNeighbors (G := G) w u₁ u₂ x q
    hu₁G hu₂G hxGw hqGw hu₁u₂ hu₁x hu₁q hu₂x hu₂q hxq
  have hupper := hcap w hwEvenG hwh hwx
  omega

/-- A SET component of the length-one auxiliary cannot contain both affected
vertices `x` and `r` under the original nonexceptional E-degree cap.  This is
the companion capacity contradiction to the `x,q` case. -/
theorem lengthOneCorridorAuxiliary_set_component_not_contains_xr
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcap : ∀ u, Even (G.degree u) → u ≠ h → u ≠ x → eDegree G u ≤ 3)
    (hxC : (.inl x : V ⊕ Unit) ∈ C.supp)
    (hrC : (.inl r : V ⊕ Unit) ∈ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    False := by
  let A := lengthOneCorridorAuxiliary G h a x q r
  let K := A.induce C.supp
  have hclosed : ∀ u ∈ C.supp, A.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  obtain ⟨_, ox, _, or, oh, _⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
  have hoddK : ∀ (u : V) (hu : (.inl u : V ⊕ Unit) ∈ C.supp),
      Odd (A.degree (.inl u)) → Odd (K.degree ⟨.inl u, hu⟩) := by
    intro u hu hou
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inl u) hu)]
    exact hou
  have oxK : Odd (K.degree ⟨.inl x, hxC⟩) := hoddK x hxC ox
  have orK : Odd (K.degree ⟨.inl r, hrC⟩) := hoddK r hrC or
  obtain ⟨wC, hxw, hrw, hwEvenK⟩ :=
    hset.exists_common_even_neighbor_of_odd ⟨.inl x, hxC⟩ ⟨.inl r, hrC⟩ oxK orK
  have hxwMem : wC ∈ evenNeighbors K ⟨.inl x, hxC⟩ :=
    (mem_evenNeighbors (G := K) ⟨.inl x, hxC⟩ wC).mpr ⟨hxw, hwEvenK⟩
  obtain ⟨w, hwval, hwGx⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      x hxC wC hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hxwMem
  have hwC : (.inl w : V ⊕ Unit) ∈ C.supp := by
    simpa [hwval] using wC.property
  have hwCeq : wC = ⟨.inl w, hwC⟩ := Subtype.ext hwval
  subst wC
  have hdegW : eDegree K ⟨.inl w, hwC⟩ = 2 :=
    hset.eDegree_even ⟨.inl w, hwC⟩ hwEvenK
  change (evenNeighbors K ⟨.inl w, hwC⟩).card = 2 at hdegW
  obtain ⟨z₁, z₂, hz₁₂, hN⟩ := Finset.card_eq_two.mp hdegW
  have hz₁ : z₁ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  have hz₂ : z₂ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  obtain ⟨u₁, hz₁val, hu₁G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₁ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₁
  obtain ⟨u₂, hz₂val, hu₂G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₂ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₂
  have hz₁Even : Even (K.degree z₁) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₁).mp hz₁ |>.2
  have hz₂Even : Even (K.degree z₂) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₂).mp hz₂ |>.2
  have hu₁u₂ : u₁ ≠ u₂ := by
    intro e
    apply hz₁₂
    apply Subtype.ext
    calc
      z₁.val = .inl u₁ := hz₁val
      _ = .inl u₂ := by rw [e]
      _ = z₂.val := hz₂val.symm
  have hu₁x : u₁ ≠ x := by
    intro e
    have hz : z₁ = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr oxK) hz₁Even
  have hu₁r : u₁ ≠ r := by
    intro e
    have hz : z₁ = ⟨.inl r, hrC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr orK) hz₁Even
  have hu₂x : u₂ ≠ x := by
    intro e
    have hz : z₂ = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr oxK) hz₂Even
  have hu₂r : u₂ ≠ r := by
    intro e
    have hz : z₂ = ⟨.inl r, hrC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr orK) hz₂Even
  have hxGw : x ∈ evenNeighbors G w := by
    obtain ⟨hxwG, _⟩ := (mem_evenNeighbors (G := G) x w).mp hwGx
    exact (mem_evenNeighbors (G := G) w x).mpr ⟨hxwG.symm, hx⟩
  have hrGw : r ∈ evenNeighbors G w := by
    obtain ⟨hrwG, _⟩ := (mem_evenNeighbors (G := G) r w).mp
      (by
        have hrwMem : ⟨.inl w, hwC⟩ ∈ evenNeighbors K ⟨.inl r, hrC⟩ :=
          (mem_evenNeighbors (G := K) ⟨.inl r, hrC⟩ ⟨.inl w, hwC⟩).mpr
            ⟨hrw, hwEvenK⟩
        obtain ⟨w', hw'val, hw'Gr⟩ :=
          lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
            r hrC ⟨.inl w, hwC⟩ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hrwMem
        have ew : w' = w := by simpa using hw'val.symm
        simpa [ew] using hw'Gr)
    exact (mem_evenNeighbors (G := G) w r).mpr ⟨hrwG.symm, hr⟩
  have hwEvenG : Even (G.degree w) := (mem_evenNeighbors (G := G) x w).mp hwGx |>.2
  have hwx : w ≠ x := by
    intro e
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl x, hxC⟩ := Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr oxK) hwEvenK
  have hwh : w ≠ h := by
    intro e
    have hhC : (.inl h : V ⊕ Unit) ∈ C.supp := by simpa [e] using hwC
    have ohK := hoddK h hhC oh
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl h, hhC⟩ := Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr ohK) hwEvenK
  have hfour := eDegree_ge_four_of_four_distinct_evenNeighbors (G := G) w u₁ u₂ x r
    hu₁G hu₂G hxGw hrGw hu₁u₂ hu₁x hu₁r hu₂x hu₂r hxr
  have hupper := hcap w hwEvenG hwh hwx
  omega

/-- A SET component of the length-one auxiliary cannot contain both non-hub
affected vertices `q` and `r`.  Unlike the two pairs containing `x`, this
uses component membership to show that the shared SET-even witness is not the
uncapped hub `x`. -/
theorem lengthOneCorridorAuxiliary_set_component_not_contains_qr
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcap : ∀ u, Even (G.degree u) → u ≠ h → u ≠ x → eDegree G u ≤ 3)
    (hqC : (.inl q : V ⊕ Unit) ∈ C.supp)
    (hrC : (.inl r : V ⊕ Unit) ∈ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    False := by
  let A := lengthOneCorridorAuxiliary G h a x q r
  let K := A.induce C.supp
  have hclosed : ∀ u ∈ C.supp, A.neighborSet u ⊆ C.supp := by
    intro u hu w huw
    exact C.mem_supp_of_adj_mem_supp hu huw
  obtain ⟨_, ox, oq, or, oh, _⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
  have hoddK : ∀ (u : V) (hu : (.inl u : V ⊕ Unit) ∈ C.supp),
      Odd (A.degree (.inl u)) → Odd (K.degree ⟨.inl u, hu⟩) := by
    intro u hu hou
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inl u) hu)]
    exact hou
  have oqK : Odd (K.degree ⟨.inl q, hqC⟩) := hoddK q hqC oq
  have orK : Odd (K.degree ⟨.inl r, hrC⟩) := hoddK r hrC or
  obtain ⟨wC, hqw, hrw, hwEvenK⟩ :=
    hset.exists_common_even_neighbor_of_odd ⟨.inl q, hqC⟩ ⟨.inl r, hrC⟩ oqK orK
  have hqwMem : wC ∈ evenNeighbors K ⟨.inl q, hqC⟩ :=
    (mem_evenNeighbors (G := K) ⟨.inl q, hqC⟩ wC).mpr ⟨hqw, hwEvenK⟩
  obtain ⟨w, hwval, hwGq⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      q hqC wC hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hqwMem
  have hwC : (.inl w : V ⊕ Unit) ∈ C.supp := by
    simpa [hwval] using wC.property
  have hwCeq : wC = ⟨.inl w, hwC⟩ := Subtype.ext hwval
  subst wC
  have hdegW : eDegree K ⟨.inl w, hwC⟩ = 2 :=
    hset.eDegree_even ⟨.inl w, hwC⟩ hwEvenK
  change (evenNeighbors K ⟨.inl w, hwC⟩).card = 2 at hdegW
  obtain ⟨z₁, z₂, hz₁₂, hN⟩ := Finset.card_eq_two.mp hdegW
  have hz₁ : z₁ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  have hz₂ : z₂ ∈ evenNeighbors K ⟨.inl w, hwC⟩ := by
    rw [hN]
    simp
  obtain ⟨u₁, hz₁val, hu₁G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₁ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₁
  obtain ⟨u₂, hz₂val, hu₂G⟩ :=
    lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
      w hwC z₂ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hz₂
  have hz₁Even : Even (K.degree z₁) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₁).mp hz₁ |>.2
  have hz₂Even : Even (K.degree z₂) :=
    (mem_evenNeighbors (G := K) ⟨.inl w, hwC⟩ z₂).mp hz₂ |>.2
  have hu₁u₂ : u₁ ≠ u₂ := by
    intro e
    apply hz₁₂
    apply Subtype.ext
    calc
      z₁.val = .inl u₁ := hz₁val
      _ = .inl u₂ := by rw [e]
      _ = z₂.val := hz₂val.symm
  have hu₁q : u₁ ≠ q := by
    intro e
    have hz : z₁ = ⟨.inl q, hqC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr oqK) hz₁Even
  have hu₁r : u₁ ≠ r := by
    intro e
    have hz : z₁ = ⟨.inl r, hrC⟩ := Subtype.ext (by simpa [e] using hz₁val)
    rw [hz] at hz₁Even
    exact (Nat.not_even_iff_odd.mpr orK) hz₁Even
  have hu₂q : u₂ ≠ q := by
    intro e
    have hz : z₂ = ⟨.inl q, hqC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr oqK) hz₂Even
  have hu₂r : u₂ ≠ r := by
    intro e
    have hz : z₂ = ⟨.inl r, hrC⟩ := Subtype.ext (by simpa [e] using hz₂val)
    rw [hz] at hz₂Even
    exact (Nat.not_even_iff_odd.mpr orK) hz₂Even
  have hqGw : q ∈ evenNeighbors G w := by
    obtain ⟨hqwG, _⟩ := (mem_evenNeighbors (G := G) q w).mp hwGq
    exact (mem_evenNeighbors (G := G) w q).mpr ⟨hqwG.symm, hq⟩
  have hrGw : r ∈ evenNeighbors G w := by
    obtain ⟨hrwG, _⟩ := (mem_evenNeighbors (G := G) r w).mp
      (by
        have hrwMem : ⟨.inl w, hwC⟩ ∈ evenNeighbors K ⟨.inl r, hrC⟩ :=
          (mem_evenNeighbors (G := K) ⟨.inl r, hrC⟩ ⟨.inl w, hwC⟩).mpr
            ⟨hrw, hwEvenK⟩
        obtain ⟨w', hw'val, hw'Gr⟩ :=
          lengthOneCorridorAuxiliary_component_evenNeighbor_old_original G h a x q r C
            r hrC ⟨.inl w, hwC⟩ hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hrwMem
        have ew : w' = w := by simpa using hw'val.symm
        simpa [ew] using hw'Gr)
    exact (mem_evenNeighbors (G := G) w r).mpr ⟨hrwG.symm, hr⟩
  have hwEvenG : Even (G.degree w) := (mem_evenNeighbors (G := G) q w).mp hwGq |>.2
  have hwx : w ≠ x := by
    by_cases hxC : (.inl x : V ⊕ Unit) ∈ C.supp
    · intro e
      have oxK : Odd (K.degree ⟨.inl x, hxC⟩) := hoddK x hxC ox
      have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl x, hxC⟩ :=
        Subtype.ext (by simpa [e])
      rw [he] at hwEvenK
      exact (Nat.not_even_iff_odd.mpr oxK) hwEvenK
    · intro e
      apply hxC
      simpa [e] using hwC
  have hwh : w ≠ h := by
    intro e
    have hhC : (.inl h : V ⊕ Unit) ∈ C.supp := by simpa [e] using hwC
    have ohK := hoddK h hhC oh
    have he : (⟨.inl w, hwC⟩ : C.supp) = ⟨.inl h, hhC⟩ := Subtype.ext (by simpa [e])
    rw [he] at hwEvenK
    exact (Nat.not_even_iff_odd.mpr ohK) hwEvenK
  have hfour := eDegree_ge_four_of_four_distinct_evenNeighbors (G := G) w u₁ u₂ q r
    hu₁G hu₂G hqGw hrGw hu₁u₂ hu₁q hu₁r hu₂q hu₂r hqr
  have hupper := hcap w hwEvenG hwh hwx
  omega

/-- A SET component away from the fresh pendant leaf and deleted centre meets
exactly one of the three deleted-spoke leaves.  Connectedness forces contact,
and the three capacity contradictions make that contact unique. -/
theorem lengthOneCorridorAuxiliary_set_component_exactly_one_deleted_leaf
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hconn : G.Connected)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcap : ∀ u, Even (G.degree u) → u ≠ h → u ≠ x → eDegree G u ≤ 3)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    ((.inl x : V ⊕ Unit) ∈ C.supp ∧
        (.inl q : V ⊕ Unit) ∉ C.supp ∧ (.inl r : V ⊕ Unit) ∉ C.supp) ∨
      ((.inl q : V ⊕ Unit) ∈ C.supp ∧
        (.inl x : V ⊕ Unit) ∉ C.supp ∧ (.inl r : V ⊕ Unit) ∉ C.supp) ∨
      ((.inl r : V ⊕ Unit) ∈ C.supp ∧
        (.inl x : V ⊕ Unit) ∉ C.supp ∧ (.inl q : V ⊕ Unit) ∉ C.supp) := by
  rcases lengthOneCorridorAuxiliary_component_meets_deleted_support G h a x q r C
      hconn hleaf haC with hxC | hqC | hrC
  · refine Or.inl ⟨hxC, ?_, ?_⟩
    · intro hqC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_xq G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hxC hqC hset
    · intro hrC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_xr G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hxC hrC hset
  · refine Or.inr (Or.inl ⟨hqC, ?_, ?_⟩)
    · intro hxC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_xq G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hxC hqC hset
    · intro hrC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_qr G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hqC hrC hset
  · refine Or.inr (Or.inr ⟨hrC, ?_, ?_⟩)
    · intro hxC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_xr G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hxC hrC hset
    · intro hqC
      exact lengthOneCorridorAuxiliary_set_component_not_contains_qr G h a x q r C
        hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcap hqC hrC hset

omit [DecidableRel G.Adj] in
/-- An `x`-side SET component away from the pendant leaf makes `x` a cut
vertex of the original graph.  The SET condition supplies a second old vertex
of the component.  After deleting `x`, a path from the pendant attachment to
that vertex would have to cross the original component boundary; the only
such boundary edge is the deleted spoke `x-a`. -/
theorem lengthOneCorridorAuxiliary_x_side_set_forces_not_connected
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hhx : h ≠ x)
    (hxC : (.inl x : V ⊕ Unit) ∈ C.supp)
    (haC : (.inl a : V ⊕ Unit) ∉ C.supp)
    (hqC : (.inl q : V ⊕ Unit) ∉ C.supp)
    (hrC : (.inl r : V ⊕ Unit) ∉ C.supp)
    (hleaf : (.inr () : V ⊕ Unit) ∉ C.supp)
    (hset : IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    ¬ (G.induce {v | v ≠ x}).Connected := by
  have hhC : (.inl h : V ⊕ Unit) ∉ C.supp :=
    lengthOneCorridorAuxiliary_attachment_not_mem_of_leaf_not_mem G h a x q r C hleaf
  obtain ⟨t, htC, htx⟩ :=
    lengthOneCorridorAuxiliary_set_component_exists_second_old_of_mem
      G h a x q r x C hxC hleaf hset
  have htx' : t ≠ x := htx
  intro hconn
  have hreach : (G.induce {v | v ≠ x}).Reachable ⟨h, hhx⟩ ⟨t, htx'⟩ :=
    hconn ⟨h, hhx⟩ ⟨t, htx'⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have hnoenter : ∀ {u v : {v : V | v ≠ x}},
      (.inl u.val : V ⊕ Unit) ∉ C.supp →
        (.inl v.val : V ⊕ Unit) ∈ C.supp →
          (G.induce {v | v ≠ x}).Adj u v → False := by
    intro u v huC hvC huv
    rcases lengthOneCorridorAuxiliary_component_crossing_is_xa
        G h a x q r v.val u.val C haC hqC hrC hvC huC huv.symm with ⟨hvx, _⟩
    exact v.property hvx
  have hstay : ∀ {v : {v : V | v ≠ x}},
      Relation.ReflTransGen (G.induce {v | v ≠ x}).Adj ⟨h, hhx⟩ v →
        (.inl v.val : V ⊕ Unit) ∉ C.supp := by
    intro v hv
    induction hv with
    | refl => exact hhC
    | tail _ huv ih => exact fun hvC => hnoenter ih hvC huv
  exact hstay hreach htC

/-- The same literal auxiliary satisfies the floor-or-SET subcubic cap. This
is only the cap interface: connectedness, component budgets, SET exclusion,
and reconstruction are deliberately separate obligations. -/
theorem lengthOneCorridorAuxiliary_cap_of_bare_data (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h)) (hbare : eDegree G h = 0)
    (hcap : ∀ v, Even (G.degree v) → v ≠ h → v ≠ x → eDegree G v ≤ 3) :
    ∀ v, Even ((lengthOneCorridorAuxiliary G h a x q r).degree v) →
      eDegree (lengthOneCorridorAuxiliary G h a x q r) v ≤ 3 := by
  have ph : Even ((threeSpokePuncture G a x q r).degree h) := by
    rw [threeSpokePuncture_degree_away G a x q r h hha hhx hhq hhr]
    exact hh
  apply pendantExtension_cap (threeSpokePuncture G a x q r) h ph
  exact threeSpokePuncture_cap_of_bare_data G h a x q r
    hax haq har hxq hxr hqr ha hx hq hr hbare hcap

/-- If the three punctured spokes are exactly the old even neighbours of the
centre, then the centre has no even neighbour in the length-one auxiliary.
This is the local SET obstruction used for the centre-containing component. -/
theorem lengthOneCorridorAuxiliary_center_eDegree_zero
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r) :
    eDegree (lengthOneCorridorAuxiliary G h a x q r) (.inl a) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨haz, hzEven⟩ :=
    (mem_evenNeighbors (G := lengthOneCorridorAuxiliary G h a x q r) (.inl a) z).mp hz
  obtain ⟨oa, ox, oq, or, oh, oleaf⟩ :=
    lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh
  cases z with
  | inr u =>
    cases u
    exact False.elim ((Nat.not_even_iff_odd.mpr oleaf) hzEven)
  | inl w =>
    have hwh : w ≠ h := by
      intro e
      subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr oh) hzEven)
    have hwP : Even ((threeSpokePuncture G a x q r).degree w) :=
      (pendantExtension_even_old_ne (threeSpokePuncture G a x q r) h w hwh).mp hzEven
    have hwG : Even (G.degree w) :=
      threeSpokePuncture_even_implies_original_even G a x q r
        hax haq har hxq hxr hqr ha hx hq hr w hwP
    have hawP : (threeSpokePuncture G a x q r).Adj a w :=
      (pendantExtension_adj_old (threeSpokePuncture G a x q r) h a w).mp haz
    have hawG : G.Adj a w := threeSpokePuncture_le G a x q r hawP
    rcases hcover w hawG hwG with hwx | hwq | hwr
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr ox) hzEven)
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr oq) hzEven)
    · subst w
      exact False.elim ((Nat.not_even_iff_odd.mpr or) hzEven)

/-- A component containing the punctured centre is not SET when the centre's
three deleted spokes exhausted its old even neighbourhood. -/
theorem lengthOneCorridorAuxiliary_center_component_not_set
    (h a x q r : V)
    (hax : G.Adj a x) (haq : G.Adj a q) (har : G.Adj a r)
    (hxq : x ≠ q) (hxr : x ≠ r) (hqr : q ≠ r)
    (ha : Even (G.degree a)) (hx : Even (G.degree x))
    (hq : Even (G.degree q)) (hr : Even (G.degree r))
    (hha : h ≠ a) (hhx : h ≠ x) (hhq : h ≠ q) (hhr : h ≠ r)
    (hh : Even (G.degree h))
    (hcover : ∀ w, G.Adj a w → Even (G.degree w) → w = x ∨ w = q ∨ w = r)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (haC : (.inl a : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp) := by
  intro hset
  have hclosed : ∀ v ∈ C.supp,
      (lengthOneCorridorAuxiliary G h a x q r).neighborSet v ⊆ C.supp := by
    intro v hv w hw
    exact C.mem_supp_of_adj_mem_supp hv hw
  have hzero : eDegree ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)
      ⟨.inl a, haC⟩ = 0 := by
    rw [eDegree_induce_of_closed (lengthOneCorridorAuxiliary G h a x q r)
      C.supp hclosed]
    exact lengthOneCorridorAuxiliary_center_eDegree_zero G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh hcover
  have hodd : Odd (((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).degree
      ⟨.inl a, haC⟩) := by
    have hdeg : ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).degree
        ⟨.inl a, haC⟩ = (lengthOneCorridorAuxiliary G h a x q r).degree (.inl a) := by
      rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inl a) haC)]
    rw [hdeg]
    exact lengthOneCorridorAuxiliary_odd_affected G h a x q r
      hax haq har hxq hxr hqr ha hx hq hr hha hhx hhq hhr hh |>.1
  have htwo := hset.odd_neighbors ⟨.inl a, haC⟩ hodd
  omega

omit [DecidableRel G.Adj] in
/-- The actual component containing the fresh pendant leaf is never SET: its
induced degree at that leaf is still one, while every SET vertex has degree at
least two. This discharges one of the explicit non-SET cases in the
length-one auxiliary component audit. -/
theorem lengthOneCorridorAuxiliary_pendant_component_not_set
    (h a x q r : V)
    (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
    [DecidablePred (· ∈ C.supp)]
    (hleaf : (.inr () : V ⊕ Unit) ∈ C.supp) :
    ¬ IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp) := by
  classical
  intro hset
  have hclosed : ∀ v ∈ C.supp,
      (lengthOneCorridorAuxiliary G h a x q r).neighborSet v ⊆ C.supp := by
    intro v hv w hw
    exact C.mem_supp_of_adj_mem_supp hv hw
  have hdeg : ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp).degree
      ⟨.inr (), hleaf⟩ = 1 := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed (.inr ()) hleaf)]
    exact pendantExtension_degree_new (threeSpokePuncture G a x q r) h
  have htwo := hset.two_le_degree ⟨.inr (), hleaf⟩
  omega

omit [DecidableRel G.Adj] in
/-- Once every actual auxiliary component has been structurally excluded from
the SET alternative, the checked subcubic cap supplies a floor decomposition
of the whole length-one auxiliary. This theorem intentionally leaves the
component-specific non-SET boundary as an explicit input. -/
theorem lengthOneCorridorAuxiliary_floor_of_component_nonSET
    (h a x q r : V)
    (hcap : ∀ v, Even ((lengthOneCorridorAuxiliary G h a x q r).degree v) →
      eDegree (lengthOneCorridorAuxiliary G h a x q r) v ≤ 3)
    (hnot : ∀ (C : (lengthOneCorridorAuxiliary G h a x q r).ConnectedComponent)
      [DecidablePred (· ∈ C.supp)],
      ¬ IsSET ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)) :
    HasPathBudget (lengthOneCorridorAuxiliary G h a x q r)
      (Fintype.card (V ⊕ Unit) / 2) := by
  apply floor_of_components
  intro C
  classical
  apply (floor_or_set ((lengthOneCorridorAuxiliary G h a x q r).induce C.supp)
    C.connected_toSimpleGraph ?_).resolve_right
  · exact hnot C
  · have hclosed : ∀ v ∈ C.supp,
        (lengthOneCorridorAuxiliary G h a x q r).neighborSet v ⊆ C.supp := by
      intro v hv w hw
      exact C.mem_supp_of_adj_mem_supp hv hw
    exact even_degree_cap_induce_of_closed
      (lengthOneCorridorAuxiliary G h a x q r) C.supp hclosed 3 hcap

end Gallai
