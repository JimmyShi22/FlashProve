-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.Promise354
import Johnson.Desc.K12.Door.LaidAt
import Johnson.Top.H0.Tw.K2C.ShapeIsTold
/-
Johnson/Loose/H2K12/ToldAt354.lean:
`MemberTold` (H2K12/Promise354.lean: the listed shape of the tree in which a member sits is what the IOP as written in
Lean tells of it) AT A TREE THAT A CODE SWITCH SENDS, from "told is laid" for that kind's sendings
(`P1K2.shapeIs_told`, ShapeIsTold.lean) AND TWO TIES. General in the chain, the sending and the tree.
  `laidOf_cut`: THE FIRST TIE's GENERAL HALF: the list of places and shapes of a chain's sendings
    (`K12.Door.laidOf`), cut at one sending: behind the shapes of the sendings in front stand the shapes that
    `layTrees` gives that sending.
  `oracleAt_cut`: THE SECOND TIE's GENERAL HALF: where the first chain's flat list is pre ++ B :: post, what
    the IOP as written tells of the tree number (the oracles that pre tells) + i is the i-th oracle that B
    tells.
  `ToldTies`: THE TWO TIES AS THEY ARE OWED AT A MEMBER, a Lean structure: the sendings' cut · the flat
    list's cut · B tells `P1K2.oraclesAt` of that sending · as many trees are listed in front as are told
    in front · the member's tree is number i behind them.
  `memberTold_of_ties`: `ToldTies` ⊢ `MemberTold`.
It stands over two other files: Johnson/Top/H0/Tw/K2C/ShapeIsTold.lean
and, beneath it, ToldTenants.lean.

(Where this and lean/THEOREM.md differ, the page holds.)
AT THE CALL. The list L is meant as `K12.Door.laidAtCodes cs c`'s return, which is by its text
(Johnson/Desc/K12/Door/LaidAt.lean) `laidOf cs` of the chain's sendings' notices in the order of their
entries: so the first clause of `ToldTies` asks that this sorted list is preS ++ sent :: postS.
What it is not. `ToldTies` is a premise: shown at no list of rounds. No example. No soundness is claimed.
Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid laidOf)
open VerifiableInference.Desc.K12.Coin (ShapeIs)

/-- **The listed shapes, cut at one sending.** -/
theorem laidOf_cut (codes : Codes) : ∀ (pre : List (List OracleNotice)) (sent : List OracleNotice)
    (post : List (List OracleNotice)) (L : Laid), laidOf codes (pre ++ sent :: post) = some L →
    ∃ Lp lay, laidOf codes pre = some Lp ∧ layTrees codes sent.toArray = some lay ∧
      ∀ i T, lay.shapes[i]? = some T → L.shapes[Lp.shapes.length + i]? = some T
  | [], sent, post, L, h => by
    simp only [List.nil_append, laidOf] at h
    obtain ⟨lay, hl, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨R, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨{}, lay, rfl, hl, fun i T hT => ?_⟩
    have hi : i < lay.shapes.toList.length := by
      rw [Array.length_toList]
      exact (Array.getElem?_eq_some_iff.1 hT).1
    show (lay.shapes.toList ++ R.shapes)[0 + i]? = some T
    rw [Nat.zero_add, List.getElem?_append_left hi, Array.getElem?_toList]
    exact hT
  | s :: pre, sent, post, L, h => by
    simp only [List.cons_append, laidOf] at h
    obtain ⟨l0, hl0, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨Lp, lay, h1, h2, h3⟩ := laidOf_cut codes pre sent post R hR
    have e : laidOf codes (s :: pre) = some
        { places := ((List.range s.length).map fun i => (l0.tree.getD i 0, l0.part.getD i 0)) ++
            Lp.places.map fun x => (l0.shapes.size + x.1, x.2)
          shapes := l0.shapes.toList ++ Lp.shapes } := by
      simp only [laidOf, hl0, h1, Option.bind_some, Option.map_some]
    refine ⟨_, lay, e, h2, fun i T hT => ?_⟩
    show (l0.shapes.toList ++ R.shapes)[(l0.shapes.toList ++ Lp.shapes).length + i]? = some T
    rw [List.length_append, Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact h3 i T hT

/-- **What is told, cut at one sub-protocol of the first chain.** -/
theorem oracleAt_cut {Xi : Type} (G : FileDescription Xi) (pre post : List (Block G.S₁ G.Cl))
    (B : Block G.S₁ G.Cl) (hc : G.first.blocksInOrder = pre ++ B :: post) (i : ℕ)
    (u : VerifiableInference.Desc.Oracle)
    (hi : i < (B.oracles.flatMap id).length)
    (hu : G.oracleAt ((oraclesOf pre).length + i) = some u) :
    (B.oracles.flatMap id)[i]? = some u := by
  unfold FileDescription.oracleAt at hu
  have e : oraclesOf G.first.blocksInOrder = oraclesOf pre ++ (B.oracles.flatMap id ++ oraclesOf post) := by
    rw [hc]
    simp [oraclesOf, List.flatMap_append, List.flatMap_cons]
  rw [e, List.append_assoc, List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.append_assoc, List.getElem?_append_left hi] at hu
  exact hu

/-- **The two ties, as they are owed at a member x.** sends: the chain's sendings in the order of their
entries. -/
structure ToldTies (cs : Codes) {Xi : Type} (G : FileDescription Xi) (L : Laid) (x : Mem) : Prop where
  ties : ∃ (preS : List (List OracleNotice)) (sent : List OracleNotice)
      (postS : List (List OracleNotice)) (pre post : List (Block G.S₁ G.Cl))
      (B : Block G.S₁ G.Cl) (grp i : ℕ),
    laidOf cs (preS ++ sent :: postS) = some L ∧ G.first.blocksInOrder = pre ++ B :: post ∧
    B.oracles.flatMap id = P1K2.oraclesAt grp cs sent.toArray ∧ 0 < sent.length ∧
    (∀ Lp, laidOf cs preS = some Lp → Lp.shapes.length = (oraclesOf pre).length) ∧
    (x.1.seat x.2).1 = (oraclesOf pre).length + i ∧ i < (B.oracles.flatMap id).length

/-- **`MemberTold` from the two ties.** -/
theorem memberTold_of_ties (cs : Codes) {Xi : Type} (G : FileDescription Xi) (L : Laid) (x : Mem)
    (h : ToldTies cs G L x) : MemberTold G L.shapes x := by
  obtain ⟨preS, sent, postS, pre, post, B, grp, i, hL, hc, hor, h0, hlen, hj, hi⟩ := h.ties
  obtain ⟨Lp, lay, h1, h2, h3⟩ := laidOf_cut cs preS sent postS L hL
  intro u T hu hT
  rw [hj] at hu hT
  have hu' := oracleAt_cut G pre post B hc i u hi hu
  rw [hor] at hu'
  have hi' : i < lay.shapes.size := by
    have e : (P1K2.oraclesAt grp cs sent.toArray).length = lay.shapes.size := by
      unfold P1K2.oraclesAt
      rw [h2]
      simp
    rw [← e, ← hor]
    exact hi
  have hT' := h3 i lay.shapes[i] (Array.getElem?_eq_getElem hi')
  rw [hlen Lp h1, hT] at hT'
  obtain rfl := Option.some.inj hT'
  exact P1K2.shapeIs_told h2 (by simpa using h0) (Array.getElem?_eq_getElem hi') hu'

end H2K12

#print axioms H2K12.laidOf_cut
#print axioms H2K12.oracleAt_cut
#print axioms H2K12.memberTold_of_ties
