-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedX.lean: **ONE X BESIDE "shape k" ON THE SHARED CHAIN: THE FOUR TESTS THAT THE TWO PROXIMITY TESTS AND THE SAMPLES' RIDING WANT OF THE RECORD, AS ONE BOOL, HANDED ON BY EVERY BLOCK.** One
definition with code; statements; each proof is four calls.

Johnson/Desc/K14/Law/LedgerRow.lean has A LETTER X beside shapeK at every border (pmK := besideP pm0 (besX Q X)) and eight premises that hand X on. What X must say: the book's count of
trees at the border 2; at 3 … 5 the count behind o_u's sending and every place.
  sharedX P sentU layU layO k d := bookX (the book is in order; the mask noted) && seatX (the book is empty up to 2; then each sending's places and trees' shapes, with the counts at 3 … 5) && membX (the
                 groups' members and the small record's notes, by number) && fitX (every place names a tree of the book; the book places no message that the statement has not).
  sharedX_first · sharedX_front · sharedX_k14 · sharedX_onGu · sharedX_onGomega · sharedX_end   FROM THE CHAIN's FIRST RECORD TO BEHIND ITS LAST BLOCK.
  sharedX_parts  what it says, in its four parts.
  sharedX_twelve the last chain's start wants o_omega's seat at border 12: bookX and seatX stand up to 12, membX's notes of
                 o_omega and o_sp up to 12: what stands at the chain's last border.
  sharedX_five   A CONTROL: a record at the border 2 whose book has a tree fails.
PREMISES ON THE PLAN: blocks P = some [eight] · withU P.S = some sentU · the two layouts at the plan's codes · a split · the masks ahead · at the two tests: the place's firstTree is K14's.
Limits. At the chain's own record St, in the blocks' own decide-form. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookX
import Johnson.Desc.Sound.MembersCarried
import Johnson.Desc.K12.Coin.HeldFitCarried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (fitX fitX_first fitX_front fitX_k14 fitX_onGu fitX_onGomega)

/-- **THE ONE X.** -/
def sharedX (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d : St) : Bool :=
  bookX P.par.toGPar.firstTree k d && seatX P sentU layU layO k d && membX sentU.size k d && fitX d

theorem sharedX_parts (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ) (d : St) :
    sharedX P sentU layU layO k d = true ↔
      bookX P.par.toGPar.firstTree k d = true ∧ seatX P sentU layU layO k d = true ∧
        membX sentU.size k d = true ∧ fitX d = true := by
  unfold sharedX
  simp only [Bool.and_eq_true, and_assoc]

theorem sharedX_first (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (codes : Codes)
    (key : TableKey) : sharedX P sentU layU layO 0 (first codes key) = true :=
  (sharedX_parts P sentU layU layO 0 _).2 ⟨bookX_first _ codes key,
    seatX_first P sentU layU layO codes key, membX_first _ codes key, fitX_first codes key⟩

theorem sharedX_front (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (frontBlock c).decide d rs gs = .ok d') (hX : sharedX P sentU layU layO 0 d = true) :
    sharedX P sentU layU layO 1 d' = true := by
  obtain ⟨a, b, e, f⟩ := (sharedX_parts P sentU layU layO 0 d).1 hX
  exact (sharedX_parts P sentU layU layO 1 d').2 ⟨bookX_front _ c d d' rs gs h a,
    seatX_front P sentU layU layO c d d' rs gs h b, membX_front _ c d d' rs gs h e,
    fitX_front c d d' rs gs h f⟩

/-- **K14's eight blocks.** i: the block's place in blocks P, from 0: the chain's block i + 1. -/
theorem sharedX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (layU layO : TreeLay)
    (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.par.S.sharedSplitNeeded = true) (hm : P.par.S.masksAhead = true)
    (i : ℕ) (b : Block St Unit) (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hX : sharedX P sentU layU layO (i + 1) d = true) :
    sharedX P sentU layU layO (i + 2) d' = true := by
  obtain ⟨a, b', e, f⟩ := (sharedX_parts P sentU layU layO (i + 1) d).1 hX
  exact (sharedX_parts P sentU layU layO (i + 2) d').2
    ⟨bookX_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl hm i b hb d d' rs gs h a,
      seatX_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU layU layO hlU hlO i b hb d d' rs gs h b',
      membX_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU hS hm i b hb d d' rs gs h e,
      fitX_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) d d' rs gs h f⟩

/-- **The test on G_u.** -/
theorem sharedX_onGu (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (p : P12)
    (hft : p.nums.firstTree = P.par.toGPar.firstTree) (he : p.early = true) (ha : p.answers = 1)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hX : sharedX P sentU layU layO 9 d = true) :
    sharedX P sentU layU layO 10 d' = true := by
  obtain ⟨a, b, e, f⟩ := (sharedX_parts P sentU layU layO 9 d).1 hX
  rw [← hft] at a
  refine (sharedX_parts P sentU layU layO 10 d').2 ⟨?_,
    seatX_onGu P sentU layU layO p he ha d d' rs gs h b, membX_onGu _ p he ha d d' rs gs h e,
    fitX_onGu p he ha d d' rs gs h f⟩
  rw [← hft]
  exact bookX_onGu p he ha d d' rs gs h a

/-- **The test on G_omega.** -/
theorem sharedX_onGomega (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (p : P12)
    (hft : p.nums.firstTree = P.par.toGPar.firstTree) (he : p.early = true) (ha : p.answers = 1)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') (hX : sharedX P sentU layU layO 10 d = true) :
    sharedX P sentU layU layO 11 d' = true := by
  obtain ⟨a, b, e, f⟩ := (sharedX_parts P sentU layU layO 10 d).1 hX
  rw [← hft] at a
  refine (sharedX_parts P sentU layU layO 11 d').2 ⟨?_,
    seatX_onGomega P sentU layU layO p he ha d d' rs gs h b, membX_onGomega _ p he ha d d' rs gs h e,
    fitX_onGomega p he ha d d' rs gs h f⟩
  rw [← hft]
  exact bookX_onGomega p he ha d d' rs gs h a

/-- Past the chain's end, at one record. -/
theorem sharedX_end (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hX : sharedX P sentU layU layO 11 d = true) : sharedX P sentU layU layO 12 d = true := by
  obtain ⟨a, b, e, f⟩ := (sharedX_parts P sentU layU layO 11 d).1 hX
  exact (sharedX_parts P sentU layU layO 12 d).2 ⟨bookX_end _ d a, seatX_end P sentU layU layO d b,
    membX_end _ d e, f⟩

/-- **What stands at the chain's last border** (what is handed to the last chain): the book is in order; o_omega bears the number sentU.size, as the small record notes it; the book places it where its sending laid it,
in a tree of that shape. -/
theorem sharedX_twelve (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 0 < (withOmega P.S).size) (hX : sharedX P sentU layU layO 12 d = true) :
    VerifiableInference.Desc.Sound.BookStep P.par.toGPar.firstTree d.book d.roots ∧
      d.loc.oOmega = sentU.size ∧
      d.book.place[sentU.size]? =
        some (layU.shapes.size + layO.tree.getD 0 0, layO.part.getD 0 0) ∧
      (d.book.trees[layU.shapes.size + layO.tree.getD 0 0]?).map (·.shape) =
        some (layO.shapes.getD (layO.tree.getD 0 0) default) := by
  obtain ⟨a, b, e, _⟩ := (sharedX_parts P sentU layU layO 12 d).1 hX
  obtain ⟨p1, p2⟩ := (seatX_place P sentU layU layO 12 d ⟨by omega, by omega⟩ b).2 0 hO
  exact ⟨(bookX_twelve _ d a).1, (membX_twelve _ d e).1, p1, p2⟩

/-- LedgerRow.lean's control: at border 2 a record whose book has trees fails. -/
theorem sharedX_five (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (h : 0 < d.book.trees.size) : sharedX P sentU layU layO 2 d = false := by
  cases hX : sharedX P sentU layU layO 2 d with
  | false => rfl
  | true =>
    have h2 := ((sharedX_parts P sentU layU layO 2 d).1 hX).2.1
    unfold seatX at h2
    rw [if_pos (by omega)] at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    omega

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.sharedX_first
#print axioms Desc.K14.Law.Fence.sharedX_front
#print axioms Desc.K14.Law.Fence.sharedX_k14
#print axioms Desc.K14.Law.Fence.sharedX_onGu
#print axioms Desc.K14.Law.Fence.sharedX_onGomega
#print axioms Desc.K14.Law.Fence.sharedX_end
#print axioms Desc.K14.Law.Fence.sharedX_twelve
#print axioms Desc.K14.Law.Fence.sharedX_five
