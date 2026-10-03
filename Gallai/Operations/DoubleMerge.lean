/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.Foundations.HubProfiles
public import Gallai.Operations.Orient
public import Gallai.Operations.Concatenate
public import Gallai.Operations.DecompositionInduce
public import Gallai.Operations.Union
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Distinct exposed carriers and safe cross-graph joins -/

namespace Gallai.Decomposition

universe u
variable {V : Type u} [DecidableEq V] {G H : SimpleGraph V}

/-- Two endpoint incidences on nonempty simple paths select two distinct carriers. -/
theorem two_terminal_carriers (D : Decomposition G) (v : V)
    (hv : 2 ≤ D.endpointCount v) :
    ∃ i j : Fin D.size, i ≠ j ∧
      ((D.path i).start = v ∨ (D.path i).finish = v) ∧
      ((D.path j).start = v ∨ (D.path j).finish = v) := by
  have hc : 1 < (D.terminalCarriers v).card := by
    rw [D.card_terminalCarriers]
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc
  exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩

omit [DecidableEq V] in
/-- Distinct decomposition carriers have disjoint edge lists. -/
theorem distinct_carriers_edges (D : Decomposition G) (i j : Fin D.size) (hij : i ≠ j) :
    (D.path i).walk.edges.Disjoint (D.path j).walk.edges := by
  intro e hi hj
  obtain ⟨k, _, hu⟩ := D.covers e ((D.path i).walk.edges_subset_edgeSet hi)
  exact hij ((hu i hi).trans (hu j hj).symm)

omit [DecidableEq V] in
/-- Join two carriers from graphs meeting only at their exposed common end. -/
theorem join_exposed (P : NonemptyPath G) (Q : NonemptyPath H) (v : V)
    (hp : P.finish = v) (hq : Q.finish = v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ R : NonemptyPath (G ⊔ H), R.start = P.start ∧ R.finish = Q.start ∧
      R.walk.edges = P.walk.edges ++ Q.walk.edges.reverse := by
  let P' := P.transfer (G ⊔ H) (fun _ he =>
    SimpleGraph.edgeSet_mono le_sup_left (P.walk.edges_subset_edgeSet he))
  let Q' := Q.reverse.transfer (G ⊔ H) (fun _ he =>
    SimpleGraph.edgeSet_mono le_sup_right
      (Q.walk.edges_subset_edgeSet (by simpa using he)))
  have hj : P'.finish = Q'.start := hp.trans hq.symm
  have hinter : ∀ w, w ∈ P'.walk.support → w ∈ Q'.walk.support → w = P'.finish := by
    intro w hwP hwQ
    have hwP' : w ∈ P.walk.support := by simpa [P'] using hwP
    have hwQ' : w ∈ Q.walk.support := by
      simp only [Q', NonemptyPath.transfer_support] at hwQ
      change w ∈ Q.walk.reverse.support at hwQ
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hwQ
    obtain ⟨a, _, ha⟩ := SimpleGraph.adj_of_mem_walk_support P.walk P.nonempty hwP'
    obtain ⟨b, _, hb⟩ := SimpleGraph.adj_of_mem_walk_support Q.walk Q.nonempty hwQ'
    exact (hmeet w ⟨a, ha⟩ ⟨b, hb⟩).trans hp.symm
  refine ⟨P'.append Q' hj hinter, rfl, rfl, ?_⟩
  rw [NonemptyPath.append_edges]
  simp [P', Q']

/-- Two distinct carriers on each side join to two edge-disjoint simple paths.
This is the local certificate; retaining the unselected carriers is separate. -/
theorem two_exposed_joins (D : Decomposition G) (E : Decomposition H) (v : V)
    (hD : 2 ≤ D.endpointCount v) (hE : 2 ≤ E.endpointCount v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ i j : Fin D.size, ∃ k l : Fin E.size,
      i ≠ j ∧ k ≠ l ∧ ∃ P Q : NonemptyPath (G ⊔ H),
      ((D.orientToward v).path i).finish = v ∧
      ((D.orientToward v).path j).finish = v ∧
      ((E.orientToward v).path k).finish = v ∧
      ((E.orientToward v).path l).finish = v ∧
      P.start = ((D.orientToward v).path i).start ∧
      P.finish = ((E.orientToward v).path k).start ∧
      Q.start = ((D.orientToward v).path j).start ∧
      Q.finish = ((E.orientToward v).path l).start ∧
      P.walk.edges = ((D.orientToward v).path i).walk.edges ++
        ((E.orientToward v).path k).walk.edges.reverse ∧
      Q.walk.edges = ((D.orientToward v).path j).walk.edges ++
        ((E.orientToward v).path l).walk.edges.reverse ∧
      P.walk.edges.Disjoint Q.walk.edges := by
  obtain ⟨i, j, hij, hi, hj⟩ := D.two_terminal_carriers v hD
  obtain ⟨k, l, hkl, hk, hl⟩ := E.two_terminal_carriers v hE
  obtain ⟨P, hPs, hPf, hP⟩ := join_exposed ((D.orientToward v).path i)
    ((E.orientToward v).path k) v (D.orientToward_terminal v i hi)
    (E.orientToward_terminal v k hk) hmeet
  obtain ⟨Q, hQs, hQf, hQ⟩ := join_exposed ((D.orientToward v).path j)
    ((E.orientToward v).path l) v (D.orientToward_terminal v j hj)
    (E.orientToward_terminal v l hl) hmeet
  have hdis : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have hg' : G.Adj a b := hg
      have hh' : H.Adj a b := hh
      exact hg'.ne ((hmeet a ⟨b, hg'⟩ ⟨b, hh'⟩).trans
        (hmeet b ⟨a, hg'.symm⟩ ⟨a, hh'.symm⟩).symm)
  refine ⟨i, j, k, l, hij, hkl, P, Q,
    D.orientToward_terminal v i hi, D.orientToward_terminal v j hj,
    E.orientToward_terminal v k hk, E.orientToward_terminal v l hl,
    hPs, hPf, hQs, hQf, hP, hQ, ?_⟩
  rw [hP, hQ]
  intro e hp hq
  simp only [List.mem_append, List.mem_reverse] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact (D.orientToward v).distinct_carriers_edges i j hij hp hq
  · exact Set.disjoint_left.mp hdis
      (((D.orientToward v).path i).walk.edges_subset_edgeSet hp)
      (((E.orientToward v).path l).walk.edges_subset_edgeSet hq)
  · exact Set.disjoint_left.mp hdis
      (((D.orientToward v).path j).walk.edges_subset_edgeSet hq)
      (((E.orientToward v).path k).walk.edges_subset_edgeSet hp)
  · exact (E.orientToward v).distinct_carriers_edges k l hkl hp hq

set_option maxHeartbeats 0 in
private theorem pair_decomposition (P Q : NonemptyPath G)
    (hd : P.walk.edges.Disjoint Q.walk.edges) :
    ∃ D : Decomposition (P.walk.toSubgraph.spanningCoe ⊔ Q.walk.toSubgraph.spanningCoe),
      D.size = 2 ∧ ∀ w, D.endpointCount w =
        ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
        ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) := by
  classical
  let K := P.walk.toSubgraph.spanningCoe ⊔ Q.walk.toSubgraph.spanningCoe
  have he (e : Sym2 V) : e ∈ K.edgeSet ↔ e ∈ P.walk.edges ∨ e ∈ Q.walk.edges := by
    simp only [K, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph]
  let P' := P.transfer K (fun e h => (he e).mpr (Or.inl h))
  let Q' := Q.transfer K (fun e h => (he e).mpr (Or.inr h))
  let paths : Fin 2 → NonemptyPath K := fun i => if i = 0 then P' else Q'
  have index_cases (i : Fin 2) : i = 0 ∨ i = 1 := by omega
  have hc : ∀ e ∈ K.edgeSet, ∃! i, e ∈ (paths i).walk.edges := by
    intro e hh
    rcases (he e).mp hh with hp | hq
    · refine ⟨0, by simpa [paths, P'] using hp, ?_⟩
      intro i hi
      rcases index_cases i with rfl | rfl
      · rfl
      · exact (hd hp (by simpa [paths, Q'] using hi)).elim
    · refine ⟨1, by simpa [paths, Q'] using hq, ?_⟩
      intro i hi
      rcases index_cases i with rfl | rfl
      · exact (hd (by simpa [paths, P'] using hi) hq).elim
      · rfl
  let D : Decomposition K := { size := 2, path := paths, covers := hc }
  refine ⟨D, rfl, ?_⟩
  intro w
  change (∑ i : Fin 2,
    ((if (paths i).start = w then 1 else 0) +
      (if (paths i).finish = w then 1 else 0))) = _
  rw [Fin.sum_univ_two]
  simp [paths, P', Q', NonemptyPath.transfer]

/-- Retain all unselected carriers and replace four selected ones by two joins. -/
theorem repack_two_pairs (D : Decomposition G) (E : Decomposition H)
    (i j : Fin D.size) (k l : Fin E.size) (hij : i ≠ j) (hkl : k ≠ l)
    (P Q : NonemptyPath (G ⊔ H))
    (hP : P.walk.edges = (D.path i).walk.edges ++ (E.path k).walk.edges.reverse)
    (hQ : Q.walk.edges = (D.path j).walk.edges ++ (E.path l).walk.edges.reverse)
    (hPQ : P.walk.edges.Disjoint Q.walk.edges) (hd : Disjoint G.edgeSet H.edgeSet) :
    ∃ F : Decomposition (G ⊔ H), F.size = D.size + E.size - 2 ∧ ∀ w,
      F.endpointCount w +
        ((if (D.path i).start = w then 1 else 0) + (if (D.path i).finish = w then 1 else 0)) +
        ((if (D.path j).start = w then 1 else 0) + (if (D.path j).finish = w then 1 else 0)) +
        ((if (E.path k).start = w then 1 else 0) + (if (E.path k).finish = w then 1 else 0)) +
        ((if (E.path l).start = w then 1 else 0) + (if (E.path l).finish = w then 1 else 0)) =
      D.endpointCount w + E.endpointCount w +
        ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) +
        ((if Q.start = w then 1 else 0) + (if Q.finish = w then 1 else 0)) := by
  classical
  let RD := G.deleteEdges {e | ∃ t ∈ ({i, j} : Finset (Fin D.size)),
    e ∈ (D.path t).walk.edges}
  let RE := H.deleteEdges {e | ∃ t ∈ ({k, l} : Finset (Fin E.size)),
    e ∈ (E.path t).walk.edges}
  let T := P.walk.toSubgraph.spanningCoe ⊔ Q.walk.toSubgraph.spanningCoe
  have hrD (e : Sym2 V) : e ∈ RD.edgeSet ↔ e ∈ G.edgeSet ∧
      ¬ (e ∈ (D.path i).walk.edges ∨ e ∈ (D.path j).walk.edges) := by
    simp [RD, SimpleGraph.edgeSet_deleteEdges]
  have hrE (e : Sym2 V) : e ∈ RE.edgeSet ↔ e ∈ H.edgeSet ∧
      ¬ (e ∈ (E.path k).walk.edges ∨ e ∈ (E.path l).walk.edges) := by
    simp [RE, SimpleGraph.edgeSet_deleteEdges]
  have ht (e : Sym2 V) : e ∈ T.edgeSet ↔
      (e ∈ (D.path i).walk.edges ∨ e ∈ (E.path k).walk.edges) ∨
      (e ∈ (D.path j).walk.edges ∨ e ∈ (E.path l).walk.edges) := by
    simp only [T, SimpleGraph.edgeSet_sup, Set.mem_union,
      SimpleGraph.Subgraph.edgeSet_spanningCoe, SimpleGraph.Walk.mem_edges_toSubgraph,
      hP, hQ, List.mem_append, List.mem_reverse]
  have hdR : Disjoint RD.edgeSet RE.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e ha hb
    exact Set.disjoint_left.mp hd ((hrD e).mp ha).1 ((hrE e).mp hb).1
  obtain ⟨R, hsR, hendsR⟩ :=
    (D.eraseCarriers {i, j}).union_disjoint_endpoints (E.eraseCarriers {k, l}) hdR
  have hdT : Disjoint T.edgeSet (RD ⊔ RE).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e ha hb
    rw [SimpleGraph.edgeSet_sup] at hb
    have ht' := (ht e).mp ha
    have hdi := (D.path i).walk.edges_subset_edgeSet (e := e)
    have hdj := (D.path j).walk.edges_subset_edgeSet (e := e)
    have hek := (E.path k).walk.edges_subset_edgeSet (e := e)
    have hel := (E.path l).walk.edges_subset_edgeSet (e := e)
    have hnot : ¬ (e ∈ G.edgeSet ∧ e ∈ H.edgeSet) :=
      fun h => Set.disjoint_left.mp hd h.1 h.2
    rcases hb with hb | hb
    · have hh := (hrD e).mp hb
      tauto
    · have hh := (hrE e).mp hb
      tauto
  obtain ⟨A, hsA, hendsA⟩ := pair_decomposition P Q hPQ
  obtain ⟨F, hsF, hendsF⟩ := A.union_disjoint_endpoints R hdT
  have hgraph : T ⊔ (RD ⊔ RE) = G ⊔ H := by
    apply SimpleGraph.edgeSet_injective
    ext e
    simp only [SimpleGraph.edgeSet_sup, Set.mem_union]
    rw [ht, hrD, hrE]
    have hdi := (D.path i).walk.edges_subset_edgeSet (e := e)
    have hdj := (D.path j).walk.edges_subset_edgeSet (e := e)
    have hek := (E.path k).walk.edges_subset_edgeSet (e := e)
    have hel := (E.path l).walk.edges_subset_edgeSet (e := e)
    constructor
    · rintro (((ha | ha) | (ha | ha)) | ha | ha)
      · exact Or.inl (hdi ha)
      · exact Or.inr (hek ha)
      · exact Or.inl (hdj ha)
      · exact Or.inr (hel ha)
      · exact Or.inl ha.1
      · exact Or.inr ha.1
    · intro ha
      rcases ha with ha | ha
      · by_cases hi : e ∈ (D.path i).walk.edges
        · exact Or.inl (Or.inl (Or.inl hi))
        by_cases hj : e ∈ (D.path j).walk.edges
        · exact Or.inl (Or.inr (Or.inl hj))
        exact Or.inr (Or.inl ⟨ha, not_or.mpr ⟨hi, hj⟩⟩)
      · by_cases hk : e ∈ (E.path k).walk.edges
        · exact Or.inl (Or.inl (Or.inr hk))
        by_cases hl : e ∈ (E.path l).walk.edges
        · exact Or.inl (Or.inr (Or.inr hl))
        exact Or.inr (Or.inr ⟨ha, not_or.mpr ⟨hk, hl⟩⟩)
  have hcD : 2 ≤ D.size := by
    have : 1 < Fintype.card (Fin D.size) := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
    simp only [Fintype.card_fin] at this
    omega
  have hcE : 2 ≤ E.size := by
    have : 1 < Fintype.card (Fin E.size) := Fintype.one_lt_card_iff.mpr ⟨k, l, hkl⟩
    simp only [Fintype.card_fin] at this
    omega
  have hs : F.size = D.size + E.size - 2 := by
    simp only [eraseCarriers_size, Finset.card_pair hij, Finset.card_pair hkl] at hsR
    omega
  have castSize {L M : SimpleGraph V} (h : L = M) (B : Decomposition L) :
      (h ▸ B).size = B.size := by subst M; rfl
  have castEnds {L M : SimpleGraph V} (h : L = M) (P : Decomposition L) (w : V) :
      (h ▸ P).endpointCount w = P.endpointCount w := by subst M; rfl
  refine ⟨hgraph ▸ F, (castSize hgraph F).trans hs, ?_⟩
  intro w
  rw [castEnds hgraph F w, hendsF, hendsA, hendsR]
  have hD := D.eraseCarriers_endpointCount ({i, j} : Finset (Fin D.size)) w
  have hE := E.eraseCarriers_endpointCount ({k, l} : Finset (Fin E.size)) w
  simp only [Finset.sum_pair hij, Finset.sum_pair hkl] at hD hE
  omega

/-- Two exposed pairs across a single-vertex intersection save exactly two paths. -/
theorem double_merge (D : Decomposition G) (E : Decomposition H) (v : V)
    (hD : 2 ≤ D.endpointCount v) (hE : 2 ≤ E.endpointCount v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ F : Decomposition (G ⊔ H), F.size = D.size + E.size - 2 := by
  obtain ⟨i, j, k, l, hij, hkl, P, Q, _, _, _, _, _, _, _, _, hP, hQ, hPQ⟩ :=
    D.two_exposed_joins E v hD hE hmeet
  have hd : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have hg' : G.Adj a b := hg
      have hh' : H.Adj a b := hh
      exact hg'.ne ((hmeet a ⟨b, hg'⟩ ⟨b, hh'⟩).trans
        (hmeet b ⟨a, hg'.symm⟩ ⟨a, hh'.symm⟩).symm)
  obtain ⟨F, hs, _⟩ := (D.orientToward v).repack_two_pairs (E.orientToward v) i j k l hij hkl
    P Q hP hQ hPQ hd
  exact ⟨F, hs⟩

/-- Two exposed joins save two carriers while preserving every endpoint count
away from their common joining vertex. -/
theorem double_merge_endpoints (D : Decomposition G) (E : Decomposition H) (v : V)
    (hD : 2 ≤ D.endpointCount v) (hE : 2 ≤ E.endpointCount v)
    (hmeet : ∀ w, (∃ a, G.Adj w a) → (∃ b, H.Adj w b) → w = v) :
    ∃ F : Decomposition (G ⊔ H), F.size = D.size + E.size - 2 ∧
      ∀ w, w ≠ v → F.endpointCount w = D.endpointCount w + E.endpointCount w := by
  obtain ⟨i, j, k, l, hij, hkl, P, Q, hi, hj, hk, hl,
    hPs, hPf, hQs, hQf, hP, hQ, hPQ⟩ := D.two_exposed_joins E v hD hE hmeet
  have hd : Disjoint G.edgeSet H.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hg hh
      have hg' : G.Adj a b := hg
      have hh' : H.Adj a b := hh
      exact hg'.ne ((hmeet a ⟨b, hg'⟩ ⟨b, hh'⟩).trans
        (hmeet b ⟨a, hg'.symm⟩ ⟨a, hh'.symm⟩).symm)
  obtain ⟨F, hs, hends⟩ := (D.orientToward v).repack_two_pairs
    (E.orientToward v) i j k l hij hkl P Q hP hQ hPQ hd
  refine ⟨F, hs, ?_⟩
  intro w hw
  have hvw : v ≠ w := Ne.symm hw
  specialize hends w
  rw [D.orientToward_endpointCount, E.orientToward_endpointCount] at hends
  simp [hi, hj, hk, hl, hPs, hPf, hQs, hQf, hvw] at hends
  omega

end Gallai.Decomposition
