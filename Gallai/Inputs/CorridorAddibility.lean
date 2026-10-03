/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Inputs.SingleEdge
public import Gallai.Foundations.EndpointBounds
public import Gallai.Structure.CorridorAuxiliary

@[expose] public section

/-!
# Sequential single-edge addibility

The longer-corridor branch of the bare two-exception reduction restores
successive missing corridor edges towards the next vertex.  This module keeps
the graph-indexed intermediate decomposition explicit and records the exact
endpoint telescoping law for two consecutive restorations.  It does not prove
the strict inequalities needed at either step; those are structural premises
of the shortest-corridor argument.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

/-- The exact output of one endpoint-preserving edge restoration.  Naming the
graph-indexed decomposition, size equality, and endpoint-transfer equation
keeps sequential corridor proofs from re-expanding the same dependent
existential at every step. -/
structure SingleEdgeRestore (D : Decomposition G) (a b : V) where
  decomposition : Decomposition (G ⊔ SimpleGraph.edge a b)
  size_eq : decomposition.size = D.size
  endpoint_transfer : ∀ w,
    decomposition.endpointCount w + (if b = w then 1 else 0) =
      D.endpointCount w + if a = w then 1 else 0

/-- Adding an edge disjoint from a vertex and from its current neighbourhood
does not create an even neighbour there.  This is the local parity transport
needed after one corridor edge has been restored: the next punctured centre
has E-degree zero, and the newly added edge is invisible to it. -/
theorem eDegree_zero_sup_edge_of_disjoint_neighbourhood [Fintype V] [DecidableRel G.Adj]
    (a b w : V) (hwa : w ≠ a) (hwb : w ≠ b)
    (hnoa : ¬ G.Adj w a) (hnob : ¬ G.Adj w b)
    (hzero : eDegree G w = 0) :
    eDegree (G ⊔ SimpleGraph.edge a b) w = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro z hz
  obtain ⟨hwz, hzEven⟩ := (mem_evenNeighbors (G := G ⊔ SimpleGraph.edge a b) w z).mp hz
  have hwzG : G.Adj w z := by
    rw [SimpleGraph.sup_adj] at hwz
    rcases hwz with hG | hedge
    · exact hG
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact False.elim (hwa (by simpa only [he]))
      · exact False.elim (hwb (by simpa only [he]))
  have hza : z ≠ a := fun hza => hnoa (hza ▸ hwzG)
  have hzb : z ≠ b := fun hzb => hnob (hzb ▸ hwzG)
  have hdegree : (G ⊔ SimpleGraph.edge a b).degree z = G.degree z := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup]
    congr 1
    ext t
    simp [SimpleGraph.edge_adj, hza, hzb]
  have hzEvenG : Even (G.degree z) := by simpa only [hdegree] using hzEven
  have : z ∈ evenNeighbors G w := (mem_evenNeighbors (G := G) w z).mpr ⟨hwzG, hzEvenG⟩
  rw [Finset.card_eq_zero.mp hzero] at this
  simpa using this

/-- An edge into an auxiliary E-degree-zero centre is strictly addible as
soon as its donor has an endpoint: every current centre neighbour is odd, so
the zero-endpoint obstruction set is empty.  This is the local first-step
rule used when restoring a punctured even corridor. -/
theorem single_edge_addibility_of_eDegree_zero_center [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hmissing : ¬ G.Adj a b)
    (hzero : eDegree G a = 0) (hdb : 0 < D.endpointCount b) :
    ∃ E : Decomposition (G ⊔ SimpleGraph.edge a b), E.size = D.size ∧
      ∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  have hpassing : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hva, hvzero⟩ := Finset.mem_filter.mp hv
    have hvpos := D.endpointCount_pos_of_neighbor_of_eDegree_zero a v
      ((G.mem_neighborFinset a v).mp hva) hzero
    omega
  exact D.single_edge_addibility a b hab hmissing (by rw [hpassing]; exact hdb)

/-- Choose the E-degree-zero restoration output for subsequent dependent
steps.  This is definitionally backed by the same one-edge transformation as
`single_edge_addibility_of_eDegree_zero_center`; choice is necessary because
the decomposition itself is data rather than a proposition. -/
noncomputable def singleEdgeRestoreOfEDegreeZero [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (a b : V)
    (hab : a ≠ b) (hmissing : ¬ G.Adj a b)
    (hzero : eDegree G a = 0) (hdb : 0 < D.endpointCount b) :
    SingleEdgeRestore D a b :=
  let h := D.single_edge_addibility_of_eDegree_zero_center a b hab hmissing hzero hdb
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

/-- The receiving centre of a restoration has a positive endpoint count
afterward.  This is the one-unit endpoint transfer in a form suited to the
next corridor edge. -/
theorem SingleEdgeRestore.endpointCount_pos_center
    {D : Decomposition G} {a b : V}
    (R : SingleEdgeRestore D a b) (hba : b ≠ a) :
    0 < R.decomposition.endpointCount a := by
  have h := R.endpoint_transfer a
  simp only [hba, if_false, if_true, Nat.add_one] at h
  omega

/-- Two consecutive restorations at fixed centres preserve the path count
when the second centre is initially E-degree zero and both endpoints of the
first restored edge are absent from its current neighbourhood.  The corridor
argument supplies these separation hypotheses from path deletion and
shortest-path geometry. -/
theorem two_edge_restore_of_zero_centres [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (p₀ p₁ p₂ : V)
    (h10 : p₁ ≠ p₀) (h21 : p₂ ≠ p₁) (h20 : p₂ ≠ p₀)
    (hmissing1 : ¬ G.Adj p₁ p₀)
    (hzero1 : eDegree G p₁ = 0) (hstart : 0 < D.endpointCount p₀)
    (hzero2 : eDegree G p₂ = 0)
    (hno21 : ¬ G.Adj p₂ p₁) (hno20 : ¬ G.Adj p₂ p₀) :
    ∃ F : Decomposition
      ((G ⊔ SimpleGraph.edge p₁ p₀) ⊔ SimpleGraph.edge p₂ p₁),
      F.size = D.size := by
  let R := D.singleEdgeRestoreOfEDegreeZero p₁ p₀ h10 hmissing1 hzero1 hstart
  have hRprev : 0 < R.decomposition.endpointCount p₁ :=
    R.endpointCount_pos_center h10.symm
  have hzeroAfter : eDegree (G ⊔ SimpleGraph.edge p₁ p₀) p₂ = 0 :=
    eDegree_zero_sup_edge_of_disjoint_neighbourhood p₁ p₀ p₂ h21 h20 hno21 hno20 hzero2
  have hmissing2 : ¬ (G ⊔ SimpleGraph.edge p₁ p₀).Adj p₂ p₁ := by
    intro hadj
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hold | hedge
    · exact hno21 hold
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact h21 (by simpa only [he])
      · exact h20 (by simpa only [he])
  obtain ⟨F, hFsize, _⟩ := R.decomposition.single_edge_addibility_of_eDegree_zero_center
    p₂ p₁ h21 hmissing2 hzeroAfter hRprev
  exact ⟨F, hFsize.trans R.size_eq⟩

/-- Three consecutive restorations preserve the path count when each later
centre is initially isolated in the even subgraph and is disjoint from all
earlier restored endpoints.  The returned graph is literal, so a shortest
corridor consumer need not hide any intermediate graph equality. -/
theorem three_edge_restore_of_zero_centres [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (p₀ p₁ p₂ p₃ : V)
    (h10 : p₁ ≠ p₀) (h21 : p₂ ≠ p₁) (h20 : p₂ ≠ p₀)
    (h32 : p₃ ≠ p₂) (h31 : p₃ ≠ p₁) (h30 : p₃ ≠ p₀)
    (hmissing1 : ¬ G.Adj p₁ p₀)
    (hzero1 : eDegree G p₁ = 0) (hstart : 0 < D.endpointCount p₀)
    (hzero2 : eDegree G p₂ = 0)
    (hno21 : ¬ G.Adj p₂ p₁) (hno20 : ¬ G.Adj p₂ p₀)
    (hzero3 : eDegree G p₃ = 0)
    (hno32 : ¬ G.Adj p₃ p₂) (hno31 : ¬ G.Adj p₃ p₁) (hno30 : ¬ G.Adj p₃ p₀) :
    ∃ K : Decomposition
      (((G ⊔ SimpleGraph.edge p₁ p₀) ⊔ SimpleGraph.edge p₂ p₁) ⊔
        SimpleGraph.edge p₃ p₂),
      K.size = D.size := by
  let R := D.singleEdgeRestoreOfEDegreeZero p₁ p₀ h10 hmissing1 hzero1 hstart
  have hRprev : 0 < R.decomposition.endpointCount p₁ :=
    R.endpointCount_pos_center h10.symm
  have hzero2After : eDegree (G ⊔ SimpleGraph.edge p₁ p₀) p₂ = 0 :=
    eDegree_zero_sup_edge_of_disjoint_neighbourhood p₁ p₀ p₂ h21 h20 hno21 hno20 hzero2
  have hmissing2 : ¬ (G ⊔ SimpleGraph.edge p₁ p₀).Adj p₂ p₁ := by
    intro hadj
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hold | hedge
    · exact hno21 hold
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact h21 (by simpa only [he])
      · exact h20 (by simpa only [he])
  let S := R.decomposition.singleEdgeRestoreOfEDegreeZero p₂ p₁ h21 hmissing2
    hzero2After hRprev
  have hSprev : 0 < S.decomposition.endpointCount p₂ :=
    S.endpointCount_pos_center h21.symm
  have hzero3After1 : eDegree (G ⊔ SimpleGraph.edge p₁ p₀) p₃ = 0 :=
    eDegree_zero_sup_edge_of_disjoint_neighbourhood p₁ p₀ p₃ h31 h30 hno31 hno30 hzero3
  have hno32After1 : ¬ (G ⊔ SimpleGraph.edge p₁ p₀).Adj p₃ p₂ := by
    intro hadj
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hold | hedge
    · exact hno32 hold
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact h31 (by simpa only [he])
      · exact h30 (by simpa only [he])
  have hno31After1 : ¬ (G ⊔ SimpleGraph.edge p₁ p₀).Adj p₃ p₁ := by
    intro hadj
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hold | hedge
    · exact hno31 hold
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact h31 (by simpa only [he])
      · exact h30 (by simpa only [he])
  have hzero3After2 : eDegree ((G ⊔ SimpleGraph.edge p₁ p₀) ⊔
      SimpleGraph.edge p₂ p₁) p₃ = 0 :=
    eDegree_zero_sup_edge_of_disjoint_neighbourhood p₂ p₁ p₃ h32 h31 hno32After1 hno31After1 hzero3After1
  have hmissing3 : ¬ ((G ⊔ SimpleGraph.edge p₁ p₀) ⊔
      SimpleGraph.edge p₂ p₁).Adj p₃ p₂ := by
    intro hadj
    rw [SimpleGraph.sup_adj] at hadj
    rcases hadj with hold | hedge
    · rw [SimpleGraph.sup_adj] at hold
      rcases hold with hold | hedge
      · exact hno32 hold
      · rw [SimpleGraph.edge_adj] at hedge
        rcases hedge with he | he
        · exact h31 (by simpa only [he])
        · exact h30 (by simpa only [he])
    · rw [SimpleGraph.edge_adj] at hedge
      rcases hedge with he | he
      · exact h32 (by simpa only [he])
      · exact h31 (by simpa only [he])
  obtain ⟨K, hKsize, _⟩ := S.decomposition.single_edge_addibility_of_eDegree_zero_center
    p₃ p₂ h32 hmissing3 hzero3After2 hSprev
  exact ⟨K, hKsize.trans S.size_eq |>.trans R.size_eq⟩

/-- The literal graph obtained after restoring the first `n` edges of an
oriented vertex sequence.  Edge `i` is restored towards `v i` from its
predecessor `v (i - 1)`. -/
def restorationChainGraph (G : SimpleGraph V) (v : ℕ → V) : ℕ → SimpleGraph V
  | 0 => G
  | n + 1 => restorationChainGraph G v n ⊔ SimpleGraph.edge (v (n + 1)) (v n)

/-- Literal adjacency normal form for a restored prefix: an edge is either an
old edge or one of the named consecutive restored edges.  This separates the
graph identity needed at a corridor terminal from any path-decomposition
argument. -/
theorem restorationChainGraph_adj_iff [DecidableRel G.Adj]
    (v : ℕ → V) (n : ℕ) (x y : V) :
    (restorationChainGraph G v n).Adj x y ↔
      G.Adj x y ∨ ∃ i, 0 < i ∧ i ≤ n ∧ v i ≠ v (i - 1) ∧
        s(x, y) = s(v i, v (i - 1)) := by
  induction n with
  | zero =>
      simp [restorationChainGraph]
  | succ n ih =>
      rw [restorationChainGraph, SimpleGraph.sup_adj, ih, SimpleGraph.edge_adj]
      constructor
      · intro h
        rcases h with h | h
        · rcases h with hG | ⟨i, hi, hile, hne, he⟩
          · exact Or.inl hG
          · exact Or.inr ⟨i, hi, Nat.le_trans hile (Nat.le_succ _), hne, he⟩
        · rcases h with ⟨h | h, hxy⟩
          · rcases h with ⟨rfl, rfl⟩
            refine Or.inr ⟨n + 1, by omega, by omega, ?_, rfl⟩
            intro he
            exact hxy (by simpa [he])
          · rcases h with ⟨rfl, rfl⟩
            refine Or.inr ⟨n + 1, by omega, by omega, ?_, ?_⟩
            · intro he
              exact hxy (by simpa [he])
            · simp only [Nat.add_sub_cancel]
              rw [Sym2.eq_swap]
      · intro h
        rcases h with hG | ⟨i, hi, hile, hne, he⟩
        · exact Or.inl (Or.inl hG)
        · by_cases hin : i ≤ n
          · exact Or.inl (Or.inr ⟨i, hi, hin, hne, he⟩)
          · have hi' : i = n + 1 := by omega
            subst i
            have he' : s(x, y) = s(v (n + 1), v n) := by
              simpa only [Nat.add_sub_cancel] using he
            right
            refine ⟨Sym2.eq_iff.mp he', ?_⟩
            intro hxy
            apply hne
            rcases Sym2.eq_iff.mp he' with h | h
            · exact h.1.symm.trans (hxy.trans h.2)
            · exact h.2.symm.trans (hxy.symm.trans h.1)

/-- Restoring the indexed edges of a walk puncture through its full length
recovers the original graph.  Unlike the finite-edge-set restoration identity,
this names the same intermediate graph family used by the ordered
path-decomposition restoration theorem. -/
theorem restorationChainGraph_walkPuncture_eq [Fintype V] [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) :
    restorationChainGraph (walkPuncture G p) (fun i => p.getVert i) p.length = G := by
  classical
  ext x y
  rw [restorationChainGraph_adj_iff]
  constructor
  · intro hxy
    rcases hxy with hpuncture | ⟨i, hi, hile, _, he⟩
    · exact (walkPuncture_adj_iff G p).mp hpuncture |>.1
    · rcases Sym2.eq_iff.mp he with h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)] using
          (p.adj_getVert_succ (i := i - 1) (by omega)).symm
      · rcases h with ⟨rfl, rfl⟩
        simpa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hi)] using
          p.adj_getVert_succ (i := i - 1) (by omega)
  · intro hxy
    by_cases hmem : s(x, y) ∈ p.edges
    · obtain ⟨j, hj, hej⟩ := p.mk_mem_edges_iff_exists.mp hmem
      right
      refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
      · intro hsame
        have hloop : (p.getVert j) = p.getVert (j + 1) := by
          rw [hsame, Nat.add_sub_cancel]
        exact (p.adj_getVert_succ (i := j) hj).ne hloop
      · rw [Nat.add_sub_cancel]
        exact hej.symm.trans Sym2.eq_swap
    · left
      exact (walkPuncture_adj_iff G p).mpr ⟨hxy, hmem⟩

/-- Restoring a finite sequence of old-vertex edges commutes with adjoining a
pendant leaf.  It reduces a lifted corridor-prefix graph identity to the
corresponding old-vertex identity. -/
theorem restorationChainGraph_pendantExtension
    (G : SimpleGraph V) (h : V) (v : ℕ → V) (n : ℕ) :
    restorationChainGraph (pendantExtension G h)
      (fun i => (.inl (v i) : V ⊕ Unit)) n =
      pendantExtension (restorationChainGraph G v n) h := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [restorationChainGraph, ih, restorationChainGraph]
      have hstar : pendantOldStar (V := V) (v (n + 1)) ({v n} : Finset V) =
          SimpleGraph.edge (.inl (v (n + 1)) : V ⊕ Unit) (.inl (v n) : V ⊕ Unit) := by
        simp [pendantOldStar, pendantOldLeaves]
      rw [← hstar, ← pendantExtension_sup_star]
      simp

/-- The recursively restored graph retains decidable adjacency whenever the
initial graph does.  Giving the recursion a named instance keeps the
graph-indexed E-degree conditions in the chain theorem literal. -/
@[instance_reducible] def restorationChainGraphDecidableRel [DecidableRel G.Adj] (v : ℕ → V) :
    ∀ n, DecidableRel (restorationChainGraph G v n).Adj
  | 0 => by
      change DecidableRel G.Adj
      infer_instance
  | n + 1 => by
      change DecidableRel
        ((restorationChainGraph G v n ⊔ SimpleGraph.edge (v (n + 1)) (v n)).Adj)
      letI : DecidableRel (restorationChainGraph G v n).Adj :=
        restorationChainGraphDecidableRel v n
      exact inferInstance

attribute [local instance] restorationChainGraphDecidableRel

/-- A restoration prefix cannot create an adjacency from `w` to an old vertex
`z` when `w` was initially separated from `z` and from every endpoint of the
restored prefix.  This is the graph-side invariant behind the E-degree ledger:
the only new edges are the restored consecutive edges themselves. -/
theorem restorationChainGraph_not_adj_of_base [DecidableRel G.Adj]
    (v : ℕ → V) (n : ℕ) (w z : V)
    (hbase : ¬ G.Adj w z)
    (hne : ∀ i, i ≤ n → w ≠ v i) :
    ¬ (restorationChainGraph G v n).Adj w z := by
  induction n with
  | zero =>
      simpa only [restorationChainGraph] using hbase
  | succ n ih =>
      intro hadj
      rw [restorationChainGraph, SimpleGraph.sup_adj] at hadj
      rcases hadj with hold | hedge
      · exact ih (fun i hi => hne i (Nat.le_trans hi (Nat.le_succ _))) hold
      · rw [SimpleGraph.edge_adj] at hedge
        rcases hedge with he | he
        · exact hne (n + 1) (by omega) (by simpa only [he])
        · exact hne n (by omega) (by simpa only [he])

/-- If a vertex has auxiliary E-degree zero and is separated in the initial
graph from every endpoint of a finite restoration prefix, it retains E-degree
zero after that prefix.  The theorem indexes the *actual* intermediate graph,
so a shortest-corridor consumer only has to establish its original no-chord
facts once. -/
theorem restorationChainGraph_eDegree_zero_of_base [Fintype V] [DecidableRel G.Adj]
    (v : ℕ → V) (n : ℕ) (w : V)
    (hzero : eDegree G w = 0)
    (hbase : ∀ i, i ≤ n → ¬ G.Adj w (v i))
    (hne : ∀ i, i ≤ n → w ≠ v i) :
    eDegree (restorationChainGraph G v n) w = 0 := by
  induction n with
  | zero =>
      simpa only [restorationChainGraph] using hzero
  | succ n ih =>
      apply eDegree_zero_sup_edge_of_disjoint_neighbourhood
        (v (n + 1)) (v n) w
      · exact hne (n + 1) (by omega)
      · exact hne n (by omega)
      · exact restorationChainGraph_not_adj_of_base v n w (v (n + 1))
          (hbase (n + 1) (by omega))
          (fun i hi => hne i (Nat.le_trans hi (Nat.le_succ _)))
      · exact restorationChainGraph_not_adj_of_base v n w (v n)
          (hbase n (by omega))
          (fun i hi => hne i (Nat.le_trans hi (Nat.le_succ _)))
      · exact ih
          (fun i hi => hbase i (Nat.le_trans hi (Nat.le_succ _)))
          (fun i hi => hne i (Nat.le_trans hi (Nat.le_succ _)))

/-- Restore an arbitrary finite prefix at unchanged path count when every
centre is E-degree zero in its *actual preceding restoration graph*.  This
is the induction form behind the two- and three-edge corridor transports:
the only nonlocal input is the explicit graph-indexed zero-degree and missing
edge ledger. -/
theorem restore_chain_of_zero_centres [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (v : ℕ → V) (n : ℕ)
    (hstart : 0 < D.endpointCount (v 0))
    (hne : ∀ i, 0 < i → i ≤ n → v i ≠ v (i - 1))
    (hmissing : ∀ i, 0 < i → i ≤ n →
      ¬ (restorationChainGraph G v (i - 1)).Adj (v i) (v (i - 1)))
    (hzero : ∀ i, 0 < i → i ≤ n →
      eDegree (restorationChainGraph G v (i - 1)) (v i) = 0) :
    ∃ E : Decomposition (restorationChainGraph G v n),
      E.size = D.size ∧ 0 < E.endpointCount (v n) := by
  induction n with
  | zero =>
      exact ⟨D, rfl, hstart⟩
  | succ n ih =>
      obtain ⟨E, hEsize, hEend⟩ := ih
        (fun i hi hile => hne i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hmissing i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hzero i hi (Nat.le_trans hile (Nat.le_succ _)))
      obtain ⟨F, hFsize, hFends⟩ := E.single_edge_addibility_of_eDegree_zero_center
        (v (n + 1)) (v n)
        (hne (n + 1) (by omega) (by omega))
        (hmissing (n + 1) (by omega) (by omega))
        (hzero (n + 1) (by omega) (by omega)) hEend
      refine ⟨F, ?_, ?_⟩
      · simpa only [restorationChainGraph] using hFsize.trans hEsize
      · have hends := hFends (v (n + 1))
        have hne' : v n ≠ v (n + 1) :=
          (hne (n + 1) (by omega) (by omega)).symm
        have hFcount : F.endpointCount (v (n + 1)) =
            E.endpointCount (v (n + 1)) + 1 := by
          simpa only [hne', if_false, if_true, Nat.add_zero, Nat.succ_eq_add_one] using hends
        have hFpos : 0 < F.endpointCount (v (n + 1)) := by
          rw [hFcount]
          exact Nat.zero_lt_succ _
        simpa only [restorationChainGraph] using hFpos

/-- The finite zero-centre restoration chain preserves the endpoint count of
every protected vertex which is disjoint from the restored vertex sequence.
This is the endpoint ledger needed when a corridor prefix is restored before
a terminal star is handled separately. -/
theorem restore_chain_of_zero_centres_preserving [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (v : ℕ → V) (n : ℕ) (z : V)
    (hstart : 0 < D.endpointCount (v 0))
    (hne : ∀ i, 0 < i → i ≤ n → v i ≠ v (i - 1))
    (hmissing : ∀ i, 0 < i → i ≤ n →
      ¬ (restorationChainGraph G v (i - 1)).Adj (v i) (v (i - 1)))
    (hzero : ∀ i, 0 < i → i ≤ n →
      eDegree (restorationChainGraph G v (i - 1)) (v i) = 0)
    (hz : ∀ i, i ≤ n → z ≠ v i) :
    ∃ E : Decomposition (restorationChainGraph G v n),
      E.size = D.size ∧ 0 < E.endpointCount (v n) ∧
        E.endpointCount z = D.endpointCount z := by
  induction n with
  | zero =>
      exact ⟨D, rfl, hstart, rfl⟩
  | succ n ih =>
      obtain ⟨E, hEsize, hEend, hEz⟩ := ih
        (fun i hi hile => hne i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hmissing i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hzero i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi => hz i (Nat.le_trans hi (Nat.le_succ _)))
      obtain ⟨F, hFsize, hFends⟩ := E.single_edge_addibility_of_eDegree_zero_center
        (v (n + 1)) (v n)
        (hne (n + 1) (by omega) (by omega))
        (hmissing (n + 1) (by omega) (by omega))
        (hzero (n + 1) (by omega) (by omega)) hEend
      refine ⟨F, ?_, ?_, ?_⟩
      · simpa only [restorationChainGraph] using hFsize.trans hEsize
      · have hends := hFends (v (n + 1))
        have hne' : v n ≠ v (n + 1) :=
          (hne (n + 1) (by omega) (by omega)).symm
        have hFcount : F.endpointCount (v (n + 1)) =
            E.endpointCount (v (n + 1)) + 1 := by
          simpa only [hne', if_false, if_true, Nat.add_zero, Nat.succ_eq_add_one] using hends
        have hFpos : 0 < F.endpointCount (v (n + 1)) := by
          rw [hFcount]
          exact Nat.zero_lt_succ _
        simpa only [restorationChainGraph] using hFpos
      · have hends := hFends z
        have hzn : v n ≠ z := (hz n (by omega)).symm
        have hznext : v (n + 1) ≠ z := (hz (n + 1) (by omega)).symm
        have hFz : F.endpointCount z = E.endpointCount z := by
          simpa only [hzn, hznext, if_false, Nat.add_zero] using hends
        simpa only [restorationChainGraph] using hFz.trans hEz

/-- The full protected-endpoint ledger for a zero-centre restoration chain.
All vertices outside the restored sequence retain their endpoint counts in the
same output decomposition.  This avoids an invalid combination of separately
chosen existential chain restorations. -/
theorem restore_chain_of_zero_centres_with_endpoint_ledger [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (v : ℕ → V) (n : ℕ)
    (hstart : 0 < D.endpointCount (v 0))
    (hne : ∀ i, 0 < i → i ≤ n → v i ≠ v (i - 1))
    (hmissing : ∀ i, 0 < i → i ≤ n →
      ¬ (restorationChainGraph G v (i - 1)).Adj (v i) (v (i - 1)))
    (hzero : ∀ i, 0 < i → i ≤ n →
      eDegree (restorationChainGraph G v (i - 1)) (v i) = 0) :
    ∃ E : Decomposition (restorationChainGraph G v n),
      E.size = D.size ∧ 0 < E.endpointCount (v n) ∧
        ∀ z, (∀ i, i ≤ n → z ≠ v i) → E.endpointCount z = D.endpointCount z := by
  induction n with
  | zero =>
      refine ⟨D, rfl, hstart, ?_⟩
      intro z _
      rfl
  | succ n ih =>
      obtain ⟨E, hEsize, hEend, hEledger⟩ := ih
        (fun i hi hile => hne i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hmissing i hi (Nat.le_trans hile (Nat.le_succ _)))
        (fun i hi hile => hzero i hi (Nat.le_trans hile (Nat.le_succ _)))
      obtain ⟨F, hFsize, hFends⟩ := E.single_edge_addibility_of_eDegree_zero_center
        (v (n + 1)) (v n)
        (hne (n + 1) (by omega) (by omega))
        (hmissing (n + 1) (by omega) (by omega))
        (hzero (n + 1) (by omega) (by omega)) hEend
      refine ⟨F, ?_, ?_, ?_⟩
      · simpa only [restorationChainGraph] using hFsize.trans hEsize
      · have hends := hFends (v (n + 1))
        have hne' : v n ≠ v (n + 1) :=
          (hne (n + 1) (by omega) (by omega)).symm
        have hFcount : F.endpointCount (v (n + 1)) =
            E.endpointCount (v (n + 1)) + 1 := by
          simpa only [hne', if_false, if_true, Nat.add_zero, Nat.succ_eq_add_one] using hends
        have hFpos : 0 < F.endpointCount (v (n + 1)) := by
          rw [hFcount]
          exact Nat.zero_lt_succ _
        simpa only [restorationChainGraph] using hFpos
      · intro z hz
        have hends := hFends z
        have hzn : v n ≠ z := (hz n (by omega)).symm
        have hznext : v (n + 1) ≠ z := (hz (n + 1) (by omega)).symm
        have hFz : F.endpointCount z = E.endpointCount z := by
          simpa only [hzn, hznext, if_false, Nat.add_zero] using hends
        have hEz : E.endpointCount z = D.endpointCount z := hEledger z
          (fun i hi => hz i (Nat.le_trans hi (Nat.le_succ _)))
        simpa only [restorationChainGraph] using hFz.trans hEz

/-- Restore the predecessor edge at a proper punctured-corridor position when
that position has auxiliary E-degree zero.  The graph equality is literal:
the output differs from the corridor auxiliary by exactly this one path edge.
The theorem is deliberately local; it does not assert that the next restored
position still has E-degree zero. -/
theorem restore_corridor_internal_previous [Fintype V] [DecidableRel G.Adj]
    {x a q r h : V} (p : G.Walk x a) (hp : p.IsPath) (i : ℕ)
    (hi : 0 < i) (hiend : i < p.length)
    (D : Decomposition (corridorAuxiliary G p q r h))
    (hzero : eDegree (corridorAuxiliary G p q r h) (.inl (p.getVert i)) = 0)
    (hdonor : 0 < D.endpointCount (.inl (p.getVert (i - 1))) ) :
    ∃ E : Decomposition
        ((corridorAuxiliary G p q r h) ⊔
          SimpleGraph.edge (.inl (p.getVert i)) (.inl (p.getVert (i - 1)))),
      E.size = D.size ∧
      ∀ w, E.endpointCount w + (if (.inl (p.getVert (i - 1)) : V ⊕ Unit) = w then 1 else 0) =
        D.endpointCount w + if (.inl (p.getVert i) : V ⊕ Unit) = w then 1 else 0 := by
  have hne : (.inl (p.getVert i) : V ⊕ Unit) ≠ .inl (p.getVert (i - 1)) := by
    intro he
    have hindex : i = i - 1 := hp.getVert_injOn
      (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega)
      (Sum.inl.inj he)
    omega
  exact D.single_edge_addibility_of_eDegree_zero_center
    (.inl (p.getVert i)) (.inl (p.getVert (i - 1))) hne
    (corridorAuxiliary_not_adj_internal_previous G p i hi hiend) hzero hdonor

/-- Two consecutive strict single-edge additions move one endpoint from the
initial donor to the final recipient without changing the number of paths.
The second strict inequality is deliberately quantified over the exact
intermediate endpoint-transfer certificate produced by the first step. -/
theorem two_edge_corridor_addibility [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hmissing₁ : ¬ G.Adj a b)
    (hstrict₁ : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} <
      D.endpointCount b)
    (hmissing₂ : ¬ (G ⊔ SimpleGraph.edge a b).Adj b c)
    (hstrict₂ : ∀ E : Decomposition (G ⊔ SimpleGraph.edge a b),
      E.size = D.size →
      (∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0) →
      #{v ∈ (G ⊔ SimpleGraph.edge a b).neighborFinset b |
          E.endpointCount v = 0} < E.endpointCount c) :
    ∃ F : Decomposition ((G ⊔ SimpleGraph.edge a b) ⊔ SimpleGraph.edge b c),
      F.size = D.size ∧
      ∀ w, F.endpointCount w + (if c = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  obtain ⟨E, hEsize, hEends⟩ :=
    D.single_edge_addibility a b hab hmissing₁ hstrict₁
  obtain ⟨F, hFsize, hFends⟩ :=
    E.single_edge_addibility b c hbc hmissing₂ (hstrict₂ E hEsize hEends)
  refine ⟨F, hFsize.trans hEsize, ?_⟩
  intro w
  have hE := hEends w
  have hF := hFends w
  omega

/-- Three consecutive strict single-edge additions transfer one endpoint from
the initial donor to the final recipient without changing the path count.

This is the length-three form needed by the terminal-corridor branch.  As in
`two_edge_corridor_addibility`, the strict addibility inequalities are kept as
premises on the graphs on which they are actually used; establishing them is
the separate structural part of the bare-hub argument. -/
theorem three_edge_corridor_addibility [Fintype V] [DecidableRel G.Adj]
    (D : Decomposition G) (a b c d : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d)
    (hmissing₁ : ¬ G.Adj a b)
    (hstrict₁ : #{v ∈ G.neighborFinset a | D.endpointCount v = 0} <
      D.endpointCount b)
    (hmissing₂ : ¬ (G ⊔ SimpleGraph.edge a b).Adj b c)
    (hstrict₂ : ∀ E : Decomposition (G ⊔ SimpleGraph.edge a b),
      E.size = D.size →
      (∀ w, E.endpointCount w + (if b = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0) →
      #{v ∈ (G ⊔ SimpleGraph.edge a b).neighborFinset b |
          E.endpointCount v = 0} < E.endpointCount c)
    (hmissing₃ : ¬ ((G ⊔ SimpleGraph.edge a b) ⊔ SimpleGraph.edge b c).Adj c d)
    (hstrict₃ : ∀ F : Decomposition ((G ⊔ SimpleGraph.edge a b) ⊔ SimpleGraph.edge b c),
      F.size = D.size →
      (∀ w, F.endpointCount w + (if c = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0) →
      #{v ∈ ((G ⊔ SimpleGraph.edge a b) ⊔ SimpleGraph.edge b c).neighborFinset c |
          F.endpointCount v = 0} < F.endpointCount d) :
    ∃ K : Decomposition
        (((G ⊔ SimpleGraph.edge a b) ⊔ SimpleGraph.edge b c) ⊔ SimpleGraph.edge c d),
      K.size = D.size ∧
      ∀ w, K.endpointCount w + (if d = w then 1 else 0) =
        D.endpointCount w + if a = w then 1 else 0 := by
  obtain ⟨F, hFsize, hFends⟩ :=
    D.two_edge_corridor_addibility a b c hab hbc hmissing₁ hstrict₁ hmissing₂ hstrict₂
  obtain ⟨K, hKsize, hKends⟩ :=
    F.single_edge_addibility c d hcd hmissing₃ (hstrict₃ F hFsize hFends)
  refine ⟨K, hKsize.trans hFsize, ?_⟩
  intro w
  have hF := hFends w
  have hK := hKends w
  omega

end Gallai.Decomposition
