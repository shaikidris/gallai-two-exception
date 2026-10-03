/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.OrdinaryRestoredPacketShape
public import Gallai.TwoException.OrdinaryMateFlattening
public import Gallai.TwoException.OrdinaryPreparationExistence

@[expose] public section

/-! # Structural ordinary guards for early restoration -/
namespace Gallai.TwoException
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The regular packet construction determines the recipient membership
needed by early restoration before any decomposition is selected. -/
theorem bare_early_ordinary_regular_guard
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S)
    (P : Finset (evenVertices G)) (mates : List (evenVertices G × evenVertices G))
    (O : List (V × V))
    (hsupp : ∀ t ∈ P, t ∈ C.supp)
    (hcover : ∀ t ∈ C.supp, t ∈ P ∨ ∃ e ∈ mates, t = e.1 ∨ t = e.2)
    (havoid : ∀ e ∈ mates, e.1 ∉ P ∧ e.2 ∉ P)
    (hlabels : ∀ e ∈ mates, ∃ a : evenVertices G,
      C.supp = {a,e.1,e.2} ∧ a ∈ P)
    (hglobal : ∀ e ∈ mates, ((e.1 : V),(e.2 : V)) ∈ O) :
    (∃ a : evenVertices G, P.image Subtype.val = {(a : V)} ∧
      ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
    (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      P.image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
    (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      P.image Subtype.val = {(a : V),(b : V),(c : V)}) := by
  classical
  cases hm : mates with
  | nil =>
    have hc : ∀ t ∈ C.supp, t ∈ P := by
      intro t ht
      rcases hcover t ht with hp | ⟨e,he,_⟩
      · exact hp
      · simp [hm] at he
    rcases bare_ordinary_mate_empty_packet_shape h x w H S C hx hwC hwS
      P hsupp hc with hi | ht
    · exact Or.inl hi
    · exact Or.inr (Or.inr ht)
  | cons e rest =>
    have he : e ∈ mates := by simp [hm]
    obtain ⟨a,hs,ha⟩ := hlabels e he
    have hP : P = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨ha,?_⟩
      intro t ht
      have htC := hsupp t ht
      rw [hs] at htC
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at htC
      rcases htC with hta | htb | htc
      · exact hta
      · exact False.elim ((havoid e he).1 (htb ▸ ht))
      · exact False.elim ((havoid e he).2 (htc ▸ ht))
    exact Or.inr (Or.inl ⟨a,e.1,e.2,hs,by simp [hP],
      ((e.1 : V),(e.2 : V)),hglobal e he,rfl⟩)

/-- Component-local mates retain their orientation in the flattened
ambient list used by the actual early auxiliary. -/
theorem ordinary_flattened_recipient_mem
    (Cs : List (evenSubgraph G).ConnectedComponent)
    (mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G))
    (C : (evenSubgraph G).ConnectedComponent) (hC : C ∈ Cs)
    (e : evenVertices G × evenVertices G) (he : e ∈ mates C) :
    ((e.1 : V),(e.2 : V)) ∈
      (Cs.flatMap mates).map (fun e => ((e.1 : V),(e.2 : V))) := by
  exact List.mem_map.mpr ⟨e,List.mem_flatMap.mpr ⟨C,hC,he⟩,rfl⟩

/-- A native touched ordinary component supplies an early packet together
with its structural regular guard. No restored decomposition is an input. -/
theorem bare_early_regular_packet_exists
    (h : V) (x w : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (S : Finset (evenVertices G)) (C : (evenSubgraph G).ConnectedComponent)
    (hx : x ∉ C.supp) (hwC : w ∈ C.supp) (hwS : w ∈ S) :
    ∃ P : Finset (evenVertices G), ∃ M : List (evenVertices G × evenVertices G),
      P.Nonempty ∧ P ⊆ ordinaryComponentPacket G S C ∧
      M.length ≤ 1 ∧
      (∀ t, t ∈ C.supp → t ∈ P ∨ ∃ e ∈ M, t = e.1 ∨ t = e.2) ∧
      (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ C.supp ∧ e.2 ∈ C.supp ∧
        e.1 ∉ P ∧ e.2 ∉ P) ∧
      ((∃ a : evenVertices G, P.image Subtype.val = {(a : V)} ∧
        ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        P.image Subtype.val = {(a : V)} ∧
        ∃ e ∈ M.map (fun e => ((e.1 : V),(e.2 : V))), e.1 = (b : V)) ∨
      (∃ a b c : evenVertices G, C.supp = {a,b,c} ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        P.image Subtype.val = {(a : V),(b : V),(c : V)})) := by
  classical
  obtain ⟨P,M,hnon,hsub,hcover,hmates,hlen,_,_,hlabels⟩ :=
    bare_ordinary_regular_preparation_exists h x w H S C hx hwC hwS
  refine ⟨P,M,hnon,hsub,hlen,hcover,hmates,?_⟩
  apply bare_early_ordinary_regular_guard h x w H S C hx hwC hwS P M
    (M.map (fun e => ((e.1 : V),(e.2 : V))))
  · intro t ht
    exact (Finset.mem_filter.mp (hsub ht)).2
  · exact hcover
  · intro e he
    exact ⟨(hmates e he).2.2.2.1,(hmates e he).2.2.2.2⟩
  · intro e he
    obtain ⟨a,hs,ha,_,_⟩ := hlabels e he
    exact ⟨a,hs,ha⟩
  · intro e he
    exact List.mem_map.mpr ⟨e,he,rfl⟩

end Gallai.TwoException
