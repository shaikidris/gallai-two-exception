/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
module

public import Gallai.TwoException.EarlyOrientedMixedFamily
public import Gallai.TwoException.EarlyMixedParity
public import Gallai.TwoException.WindmillContactSets

@[expose] public section

/-! # Simultaneous special selection and oriented early packets -/
namespace Gallai.TwoException
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable local instance selectedMixedComponents :
    DecidableEq (evenSubgraph G).ConnectedComponent := Classical.decEq _

/-- Choose the optional special packet and all regular orientations together.
The resulting literal deletion star is even whenever the baseline is even
or a two-contact ordinary triangle is available. The same witnesses provide
recipient coverage and all local mate data for native early restoration. -/
theorem bare_early_selected_even_mixed_family
    (h u : V) (x : evenVertices G) (H : BareMinimalCounterexample G h (x : V))
    (A : Finset {a : evenVertices G // (evenSubgraph G).Adj x a})
    (S : Finset (evenVertices G)) (F : Finset (evenSubgraph G).ConnectedComponent)
    (hF : F ⊆ S.image (evenSubgraph G).connectedComponentMk)
    (hx : ∀ Z ∈ F, x ∉ Z.supp)
    (hclass : ∀ t, G.Adj u t → ∀ ht : Even (G.degree t),
      t = (x : V) ∨ t = h ∨ (⟨t,ht⟩ : evenVertices G) ∈ S)
    (havailable : Even (#A + #F + 2 * #(F.filter
      (fun Z => #(ordinaryComponentPacket G S Z) = 3))) ∨
      (F.filter (fun Z => #(ordinaryComponentPacket G S Z) = 2)).Nonempty) :
    ∃ special : Finset (evenSubgraph G).ConnectedComponent,
    ∃ Q : (evenSubgraph G).ConnectedComponent → Finset (evenVertices G),
    ∃ mates : (evenSubgraph G).ConnectedComponent → List (evenVertices G × evenVertices G),
      special ⊆ F ∧ #special ≤ 1 ∧
      Even #(windmillPrivateSet x A ∪ (F.biUnion Q).image Subtype.val) ∧
      (∀ Z ∈ F, (Q Z).Nonempty ∧ Q Z ⊆ ordinaryComponentPacket G S Z ∧
        ∀ t ∈ Q Z, t ∈ Z.supp) ∧
      (∀ Z ∈ F, Z ∉ special →
        (∀ t, t ∈ Z.supp → t ∈ Q Z ∨ ∃ e ∈ mates Z, t = e.1 ∨ t = e.2) ∧
        (∀ e ∈ mates Z, G.Adj e.1 e.2 ∧ e.1 ∈ Z.supp ∧ e.2 ∈ Z.supp ∧
          e.1 ∉ Q Z ∧ e.2 ∉ Q Z ∧ e.2 ∉ S ∧
          ∃ a : evenVertices G, Z.supp = {a,e.1,e.2} ∧ a ∈ Q Z ∧
            G.Adj a e.1 ∧ G.Adj e.2 a) ∧ (mates Z).length ≤ 1 ∧
        #(Q Z) = 1 + 2 * (if #(ordinaryComponentPacket G S Z) = 3 then 1 else 0)) ∧
      (∀ Z ∈ special, Q Z = ordinaryComponentPacket G S Z) ∧
      (∀ Z ∈ special, ∃ a b c : evenVertices G,
        Z.supp = {a,b,c} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        ordinaryComponentPacket G S Z = {a,b} ∧ c ∉ S ∧ ¬ G.Adj c u) ∧
      (let O := ((F \ special).toList.flatMap mates).map
        (fun e => ((e.1 : V),(e.2 : V)));
        (∀ Z ∈ F, Z ∉ special →
          (∃ a : evenVertices G, (Q Z).image Subtype.val = {(a : V)} ∧
            ∀ t, G.Adj a t → ¬ Even (G.degree t)) ∨
          (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
            (Q Z).image Subtype.val = {(a : V)} ∧ ∃ e ∈ O, e.1 = (b : V)) ∨
          (∃ a b c : evenVertices G, Z.supp = {a,b,c} ∧
            G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
            (Q Z).image Subtype.val = {(a : V),(b : V),(c : V)})) ∧
        (∀ t ∈ S, (evenSubgraph G).connectedComponentMk t ∈ F →
          (t : V) ∈ (F.biUnion Q).image Subtype.val ∨ ∃ e ∈ O, (t : V) = e.1)) := by
  classical
  let K := windmillPrivateSet x A
  let k := #K + #F + 2 * #(F.filter
    (fun Z => #(ordinaryComponentPacket G S Z) = 3))
  obtain ⟨special,hsub,hsize,hempty,hpar,_,hspecial⟩ :=
    bare_early_special_family h u x H S F hF hx hclass k
  have hsubF : special ⊆ F := fun Z hZ => (Finset.mem_filter.mp (hsub hZ)).1
  obtain ⟨Q,mates,hQ,hregular,hfull,hglobal⟩ :=
    bare_early_oriented_mixed_family h u x H S F special hF hx hsubF hspecial
  have hsupp : ∀ Z ∈ F, ∀ t ∈ Q Z, t ∈ Z.supp :=
    fun Z hZ => (hQ Z hZ).2.2
  have hdis : Disjoint K ((F.biUnion Q).image Subtype.val) := by
    apply Finset.disjoint_left.mpr
    intro t htK htL
    obtain ⟨a,ha,hat⟩ := (mem_windmillPrivateSet x A _).mp htK
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp htL
    obtain ⟨Z,hZ,hbQ⟩ := Finset.mem_biUnion.mp hb
    have hba : b = a.val := Subtype.ext (hbt.trans hat.symm)
    have haZ : a.val ∈ Z.supp := hba ▸ hsupp Z hZ b hbQ
    exact hx Z hZ (Z.mem_supp_of_adj_mem_supp haZ a.property.symm)
  have hspecialCard : ∀ Z ∈ special,
      #(ordinaryComponentPacket G S Z) = 2 ∧ #(Q Z) = 2 := by
    intro Z hZ
    have hp := (Finset.mem_filter.mp (hsub hZ)).2
    exact ⟨hp,by rw [hfull Z hZ]; exact hp⟩
  have heven := early_actual_mixed_star_even S F special Q K hdis hsubF hsupp
    (fun Z hZ hn => (hregular Z hZ hn).2.2.2) hspecialCard hsize hempty hpar
    (by simpa only [K,windmillPrivateSet_card] using havailable)
  refine ⟨special,Q,mates,hsubF,hsize,heven,hQ,hregular,hfull,hspecial,?_⟩
  dsimp only
  refine ⟨hglobal.2,?_⟩
  intro t ht htouch
  exact early_mixed_recipient_coverage_at S F special Q mates hfull
    (fun Z hZ hn => (hregular Z hZ hn).1)
    (fun Z hZ hn e he => (hregular Z hZ hn).2.1 e he |>.2.2.2.2.2.1)
    t ht htouch

end Gallai.TwoException
