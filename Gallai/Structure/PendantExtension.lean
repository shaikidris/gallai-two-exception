/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Structure.EdgeDeletion
public import Gallai.Structure.EvenSubgraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! # Adding a pendant edge on a fresh vertex

The degree-three hub reduction punctures a graph on its old vertex type and
then adds a fresh pendant edge at the prescribed bare vertex.  This is not a
leaf transfer: no old edge is replaced.  The small constructor and its degree
formulas keep that type change explicit for the component and parity audit.
-/

namespace Gallai

universe u

variable {V : Type u}

/-- Embed an old graph and attach a single fresh leaf to `h`. -/
abbrev pendantExtension (G : SimpleGraph V) (h : V) : SimpleGraph (V ⊕ Unit) :=
  G.map (Function.Embedding.inl : V ↪ V ⊕ Unit) ⊔
    SimpleGraph.edge (Sum.inl h) (Sum.inr ())

/-- The canonical lifted copy of a finite old-vertex leaf set. -/
def pendantOldLeaves (B : Finset V) : Finset (V ⊕ Unit) :=
  B.map (Function.Embedding.inl : V ↪ V ⊕ Unit)

/-- The canonical old-vertex preimage of a finite set in the pendant type. -/
def pendantOldPreimage [Fintype V] [DecidableEq V]
    (B : Finset (V ⊕ Unit)) : Finset V :=
  Finset.univ.filter fun v => (.inl v : V ⊕ Unit) ∈ B

@[simp]
theorem mem_pendantOldLeaves [DecidableEq V] (B : Finset V) (v : V) :
    (.inl v : V ⊕ Unit) ∈ pendantOldLeaves B ↔ v ∈ B := by
  simp [pendantOldLeaves]

/-- A lifted finite set containing no fresh leaf is exactly the lift of its
canonical old-vertex preimage. -/
theorem pendantOldLeaves_preimage_eq [Fintype V] [DecidableEq V]
    (B : Finset (V ⊕ Unit)) (hnew : (.inr () : V ⊕ Unit) ∉ B) :
    pendantOldLeaves (pendantOldPreimage B) = B := by
  ext z
  cases z with
  | inl v => simp [pendantOldPreimage]
  | inr u =>
    cases u
    simp [pendantOldLeaves, hnew]

/-- The lifted copy of an old-centred finite star. -/
def pendantOldStar (a : V) (B : Finset V) : SimpleGraph (V ⊕ Unit) :=
  (pendantOldLeaves (V := V) B).sup
    (fun b : V ⊕ Unit => SimpleGraph.edge (.inl a : V ⊕ Unit) b)

/-- The old-vertex restriction of a pendant extension is exactly the old graph. -/
theorem pendantExtension_adj_old (G : SimpleGraph V) (h a b : V) :
    (pendantExtension G h).Adj (.inl a) (.inl b) ↔ G.Adj a b := by
  simp [pendantExtension, SimpleGraph.edge_adj]

/-- The fresh vertex has exactly the specified old neighbour. -/
theorem pendantExtension_adj_new (G : SimpleGraph V) (h : V) (v : V ⊕ Unit) :
    (pendantExtension G h).Adj (.inr ()) v ↔ v = .inl h := by
  cases v <;> simp [pendantExtension, SimpleGraph.map_adj, SimpleGraph.edge_adj, eq_comm]

private theorem map_sup_embedding {U W : Type*} (f : U ↪ W)
    (A B : SimpleGraph U) :
    (A ⊔ B).map f = A.map f ⊔ B.map f := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  aesop

private theorem map_edge_embedding {U W : Type*} (f : U ↪ W) (a b : U) :
    (SimpleGraph.edge a b).map f = SimpleGraph.edge (f a) (f b) := by
  ext u v
  simp only [SimpleGraph.map_adj, SimpleGraph.edge_adj]
  aesop

private theorem map_starSup_inl [DecidableEq V] (a : V) (B : Finset V) :
    (B.sup (SimpleGraph.edge a)).map (Function.Embedding.inl : V ↪ V ⊕ Unit) =
      pendantOldStar a B := by
  induction B using Finset.induction with
  | empty =>
    ext u v
    simp [pendantOldLeaves, pendantOldStar, SimpleGraph.map_adj]
  | @insert b B hb ih =>
    simp only [pendantOldStar, pendantOldLeaves, Finset.map_insert, Finset.sup_insert]
    rw [map_sup_embedding, map_edge_embedding, ih]
    rfl

/-- Pendant extension commutes with adding an old-centred finite star.  This
is the graph-level transport used to return a selected half-star output from
the lifted auxiliary to its old puncture while retaining the pendant edge. -/
theorem pendantExtension_sup_star [DecidableEq V]
    (G : SimpleGraph V) (h a : V) (B : Finset V) :
    pendantExtension (V := V) (G ⊔
      (B.sup (fun b : V => SimpleGraph.edge a b) : SimpleGraph V)) h =
      pendantExtension (V := V) G h ⊔ pendantOldStar (V := V) a B := by
  unfold pendantExtension
  rw [map_sup_embedding, map_starSup_inl]
  ac_rfl

/-- Deleting the unique pendant edge leaves precisely the old graph image.
This is the graph identity used after terminally trimming the fresh-leaf
carrier; the isolated fresh vertex is removed separately at the decomposition
level. -/
theorem pendantExtension_delete_pendant (G : SimpleGraph V) (h : V) :
    (pendantExtension G h).deleteEdges {s((.inl h : V ⊕ Unit), .inr ())} =
      G.map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
  ext u v
  cases u <;> cases v <;>
    simp [pendantExtension, SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The fresh-pendant auxiliary has exactly one more vertex than its old
puncture. This is the order term used by the Section 5 component budget. -/
theorem pendantExtension_card : Fintype.card (V ⊕ Unit) = Fintype.card V + 1 := by
  rw [Fintype.card_sum, Fintype.card_unit]

/-- Local classical adjacency decision for degree calculations on the extension. -/
noncomputable instance instDecidableRelAdjPendantExtension (h : V) :
    DecidableRel (pendantExtension G h).Adj :=
  fun _ _ => Classical.propDecidable _

/-- An old vertex keeps its degree, except for the pendant attachment vertex. -/
theorem pendantExtension_degree_old (h v : V) :
    (pendantExtension G h).degree (.inl v) = G.degree v + if v = h then 1 else 0 := by
  classical
  have hset : (pendantExtension G h).neighborFinset (.inl v) =
      (G.neighborFinset v).map (Function.Embedding.inl : V ↪ V ⊕ Unit) ∪
        (if v = h then {Sum.inr ()} else ∅) := by
    ext w
    cases w with
    | inl w => by_cases hv : v = h <;> simp [pendantExtension, SimpleGraph.edge_adj, hv]
    | inr w =>
      cases w
      by_cases hv : v = h
      · subst v
        simp [pendantExtension, SimpleGraph.edge_adj]
      · simp [pendantExtension, SimpleGraph.edge_adj, hv]
  have hdis : Disjoint
      ((G.neighborFinset v).map (Function.Embedding.inl : V ↪ V ⊕ Unit))
      (if v = h then {Sum.inr ()} else ∅) := by
    split <;> simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_union_of_disjoint hdis]
  simp only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
  split <;> simp_all

/-- Away from its attachment vertex, a pendant extension leaves every old
vertex degree unchanged. -/
theorem pendantExtension_degree_old_ne (h v : V) (hv : v ≠ h) :
    (pendantExtension G h).degree (.inl v) = G.degree v := by
  rw [pendantExtension_degree_old]
  simp [hv]

/-- Away from the attachment, the pendant extension has exactly the lifted old
neighbour set.  This is the finite-set interface used to transfer a local
passing-neighbour count through the type-changing auxiliary. -/
theorem pendantExtension_neighborFinset_old_ne (h v : V) (hv : v ≠ h) :
    (pendantExtension G h).neighborFinset (.inl v) =
      (G.neighborFinset v).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
  ext w
  cases w with
  | inl w =>
    simp [SimpleGraph.mem_neighborFinset, pendantExtension, SimpleGraph.edge_adj, hv]
  | inr u =>
    cases u
    simp [SimpleGraph.mem_neighborFinset, pendantExtension, SimpleGraph.edge_adj, hv]

/-- The attachment vertex gains exactly the new pendant edge. -/
theorem pendantExtension_degree_attach (h : V) :
    (pendantExtension G h).degree (.inl h) = G.degree h + 1 := by
  simpa using pendantExtension_degree_old G h h

/-- Away from the attachment point, even-degree status is preserved. -/
theorem pendantExtension_even_old_ne (h v : V) (hv : v ≠ h) :
    Even ((pendantExtension G h).degree (.inl v)) ↔ Even (G.degree v) := by
  rw [pendantExtension_degree_old_ne G h v hv]

/-- Away from the attachment point, odd-degree status is also preserved. -/
theorem pendantExtension_odd_old_ne (h v : V) (hv : v ≠ h) :
    Odd ((pendantExtension G h).degree (.inl v)) ↔ Odd (G.degree v) := by
  rw [pendantExtension_degree_old_ne G h v hv]

/-- Attaching one pendant edge flips the parity at its old attachment vertex. -/
theorem pendantExtension_even_attach_iff (h : V) :
    Even ((pendantExtension G h).degree (.inl h)) ↔ Odd (G.degree h) := by
  rw [pendantExtension_degree_attach]
  exact Nat.even_add_one.trans Nat.not_even_iff_odd

/-- At the attachment point, oddness after extension is precisely old
evenness. -/
theorem pendantExtension_odd_attach_iff (h : V) :
    Odd ((pendantExtension G h).degree (.inl h)) ↔ Even (G.degree h) := by
  rw [pendantExtension_degree_attach]
  exact Nat.odd_add_one.trans Nat.not_odd_iff_even

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The fresh pendant vertex has degree one. -/
theorem pendantExtension_degree_new (G : SimpleGraph V) (h : V) :
    (pendantExtension G h).degree (.inr ()) = 1 := by
  have hset : (pendantExtension G h).neighborFinset (.inr ()) = {Sum.inl h} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, pendantExtension_adj_new,
      Finset.mem_singleton]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset, Finset.card_singleton]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The fresh pendant vertex is odd. -/
theorem pendantExtension_odd_new (G : SimpleGraph V) (h : V) :
    Odd ((pendantExtension G h).degree (.inr ())) := by
  rw [pendantExtension_degree_new]
  exact ⟨0, by omega⟩

/-- Attaching one pendant edge at an even old vertex preserves a subcubic
E-degree cap. The attachment and the fresh leaf are odd in the extension, and
every remaining even neighbour maps injectively to an old even neighbour. -/
theorem pendantExtension_cap (h : V) (hh : Even (G.degree h))
    (hcap : ∀ v, Even (G.degree v) → eDegree G v ≤ 3) :
    ∀ v, Even ((pendantExtension G h).degree v) →
      eDegree (pendantExtension G h) v ≤ 3 := by
  intro v hv
  cases v with
  | inr u =>
    cases u
    exact False.elim ((Nat.not_even_iff_odd.mpr (pendantExtension_odd_new G h)) hv)
  | inl v =>
    have hvh : v ≠ h := by
      intro e
      subst v
      exact False.elim
        ((Nat.not_even_iff_odd.mpr
          ((pendantExtension_odd_attach_iff G h).mpr hh)) hv)
    have hvOld : Even (G.degree v) :=
      (pendantExtension_even_old_ne G h v hvh).mp hv
    have hsubset : evenNeighbors (pendantExtension G h) (.inl v) ⊆
        (evenNeighbors G v).map (Function.Embedding.inl : V ↪ V ⊕ Unit) := by
      intro w hw
      obtain ⟨hvw, hwEven⟩ :=
        (mem_evenNeighbors (G := pendantExtension G h) (.inl v) w).mp hw
      cases w with
      | inr u =>
        cases u
        exact False.elim
          ((Nat.not_even_iff_odd.mpr (pendantExtension_odd_new G h)) hwEven)
      | inl w =>
        have hwAdj : G.Adj v w :=
          (pendantExtension_adj_old G h v w).mp hvw
        have hwh : w ≠ h := by
          intro e
          subst w
          exact False.elim
            ((Nat.not_even_iff_odd.mpr
              ((pendantExtension_odd_attach_iff G h).mpr hh)) hwEven)
        have hwOld : Even (G.degree w) :=
          (pendantExtension_even_old_ne G h w hwh).mp hwEven
        exact Finset.mem_map.mpr ⟨w,
          (mem_evenNeighbors (G := G) v w).mpr ⟨hwAdj, hwOld⟩, rfl⟩
    have hle : eDegree (pendantExtension G h) (.inl v) ≤ eDegree G v := by
      change (evenNeighbors (pendantExtension G h) (.inl v)).card ≤
        (evenNeighbors G v).card
      rw [← Finset.card_map (Function.Embedding.inl : V ↪ V ⊕ Unit)]
      exact Finset.card_le_card hsubset
    exact hle.trans (hcap v hvOld)

end Gallai
