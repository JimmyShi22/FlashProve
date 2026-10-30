-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LaidInsideSeats.lean: the seats that the plan's item "layout" gives lie inside
their messages' ranges and off their pads. Theorems, proved; one condition on public letters,
stated and proved nowhere.

Why. Johnson/Goal/Meaning/HidSeatsOf.lean makes the seats of the 25 sub-proofs off the layout:
seatBy (fLay layout num) X s. A witness's table is total; a pin fixes a message inside the member's
ranges alone (InMsg, Johnson/Desc/Sound/World.lean), and at a pad's place (padB,
Johnson/Desc/SeatAt.lean) each copy of a message has an entry of its own. So a statement on what is
read at the seats says something of the committed tables only where every seat lies inside the
ranges and off the pad. Johnson/Goal/Meaning/LaidInside.lean has that of the seats of one array,
from the programs' three tests. Here it is carried to the seats of the sub-proofs.

Main names:
  array_inside   at the array of a name: InMsg and padB = false at the shape of the message that the
    array names.
  seat_inside   at seatBy (fLay layout num) X s, under the three tests and laidThere, for k < 25,
    within the sizes: the seat's number is num l A.message, l the owner's link and A the array that
    the entry's label names; message A.message of link l is there in the request's shape; the seat's
    row and place lie inside its ranges and off its pad.
  ShapesTied codes shape layout num arr ms grp   THE TIE OF LETTERS, A PREMISE:
    wherever an array of link l lies in message j of that link, every member of ms that sits in a
    group grp k, k < 25, and bears the number num l j has that message's padKey
    (Johnson/Desc/PlanMem.lean): main and mask rows, degree, and the two codes' lengths.
  seat_inside_members   under the tie: the same of every such member's own shape, by padB_of_key and
    inMsg_of_key (Johnson/Desc/Sound/PlanMemProofs.lean).

Object, user, letters.
  seat_inside   object: reqLayoutOk, reqShapeOk, Codes.lengthsOk, laidThere, seatBy, fLay, InMsg,
    padB. User: seat_inside_members. Letters: codes, shape, layout, X, s, num free.
  seat_inside_members   object: these and Mem, seatOf, numOf (Johnson/Desc/Sound/World.lean). User:
    none in the library yet. It is shaped for whoever asks, of every member in a segment's group
    with a seat's number, InMsg or padB = false at the seat. Letters: also arr, ms, grp free; grp
    is meant to be the list of a segment's group's tenants.

Who can pay ShapesTied. Whoever makes ms, grp, arr and num off one plan. The programs' text makes a
kept message's later copy with the first sending's shape (reqGroupAt, OnBytes/Iop/Req.lean), so the
equation is not asked against the text; no theorem says it. It is asked at no message in which no
array lies, so a number that num gives by default binds nobody. All its letters are lists and
numbers and k is bounded: a test with code can stand beside it; none is typed.

What is not claimed. ShapesTied at any letters. laidThere, or any of the three tests, at any plan:
none has run here. What HidSeatsOf.lean does not claim either: that sub-proof k is link k of the
layout, that entry a's array bears the name "M" and a, that the programs read a borrowed array at
its owner's seat. Nothing beyond k = 24. Nothing on soundness, nothing on hiding. The program does
not import this file.
-/
import Johnson.Goal.Meaning.LaidInside
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.Sound.World
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes
open OnBytes.Params (ReqArray ReqLayout ReqShape ReqMessage)
open VerifiableInference.Desc (seatIn arrayOf laidAt padB padKey)
open VerifiableInference.Desc.Sound (InMsg Mem seatOf numOf padB_of_key inMsg_of_key)
open Cb.Pv.Tail (Size)

/-- The array of a name among link l's is one of link l's arrays. -/
theorem arrayOf_mem {layout : ReqLayout} {l : ℕ} {name : String} {A : ReqArray}
    (h : arrayOf layout l name = some A) : ∃ as, layout.link[l]? = some as ∧ A ∈ as := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨as, hl, List.mem_of_find?_eq_some hf⟩

section
variable {codes : Codes} {shape : ReqShape} {layout : ReqLayout}

/-- **The geometry at a named array**: inside the message's ranges and off its pad. -/
theorem array_inside (hC : codes.lengthsOk = true) (hS : reqShapeOk shape = true)
    (h : reqLayoutOk codes shape layout = true) {l : ℕ} {name : String} {A : ReqArray}
    (hA : arrayOf layout l name = some A) {i c : ℕ} {x : ℕ × ℕ} (hat : laidAt A i c = some x) :
    ∃ m, messageAt shape l A.message = some m ∧ InMsg codes m.shape false x.1 x.2 ∧
      padB codes m.shape false x.1 x.2 = false := by
  obtain ⟨as, hl, hm⟩ := arrayOf_mem hA
  obtain ⟨m, e, hr, hp, hB⟩ := laidAt_inside hC hS h hl hm (r := x.1) (p := x.2) hat
  refine ⟨m, e, ?_, hB⟩
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨hr, hp⟩

/-- **The geometry at the seats off the layout.** Under the programs' three tests and the test
laidThere, every seat that sub-proof k < 25 names within its sizes bears the number of a message of
the request's shape (message A.message of the owner's link, A the array that the entry's label
names), and lies inside that message's ranges and off its pad. -/
theorem seat_inside (hC : codes.lengthsOk = true) (hS : reqShapeOk shape = true)
    (h : reqLayoutOk codes shape layout = true) {X : Model.Verify.Public} {s : ℕ → Size}
    (T : laidThere X s layout = true) (num : ℕ → ℕ → ℕ) {k : ℕ} (hk : k < 25) (μ : Fin (s k).NM)
    {i c : ℕ} (hi : i < Alg.symRows ((s k).m μ)) (hc : c < (s k).k μ) :
    ∃ A m, arrayOf layout (ownerK (labAt X k μ.val)) (nameOf (ownerA (labAt X k μ.val))) = some A ∧
      messageAt shape (ownerK (labAt X k μ.val)) A.message = some m ∧
      (seatBy (fLay layout num) X s k μ i c).1 = num (ownerK (labAt X k μ.val)) A.message ∧
      InMsg codes m.shape false (seatBy (fLay layout num) X s k μ i c).2.1
        (seatBy (fLay layout num) X s k μ i c).2.2 ∧
      padB codes m.shape false (seatBy (fLay layout num) X s k μ i c).2.1
        (seatBy (fLay layout num) X s k μ i c).2.2 = false := by
  obtain ⟨A, x, hA, -, -, hx, e⟩ := seat_of_laidThere T num hk μ hi hc
  obtain ⟨m, hm, hin, hB⟩ := array_inside hC hS h hA hx
  rw [e]
  exact ⟨A, m, hA, hm, rfl, hin, hB⟩

/-! ## The tie of letters: a premise, and what follows from it -/

/-- **THE TIE OF LETTERS: A CONDITION ON PUBLIC LETTERS, PROVED NOWHERE.** grp k: the tenants of
segment k's group. Wherever an array A of link l lies in message A.message of that link:
every member of ms that sits in the group of one of the 25 segments and bears the number
num l A.message has that message's padKey: the five numbers that padB and InMsg read of a shape. -/
def ShapesTied (codes : Codes) (shape : ReqShape) (layout : ReqLayout) (num arr : ℕ → ℕ → ℕ)
    (ms : List Mem) (grp : ℕ → List (ℕ × ℕ)) : Prop :=
  ∀ l as A m, layout.link[l]? = some as → A ∈ as → messageAt shape l A.message = some m →
    ∀ k < 25, ∀ y ∈ ms, seatOf y ∈ grp k → numOf arr y = num l A.message →
      padKey codes (y.1.l.get y.2).1 = padKey codes m.shape

/-- **The geometry at the members.** Under the three tests, laidThere and the tie of letters: every
member of ms that sits in the group of ANY of the 25 segments with the number that a seat of
sub-proof k < 25 names has the seat's row and place inside its ranges and off its pad. -/
theorem seat_inside_members (hC : codes.lengthsOk = true) (hS : reqShapeOk shape = true)
    (h : reqLayoutOk codes shape layout = true) {X : Model.Verify.Public} {s : ℕ → Size}
    (T : laidThere X s layout = true) {num arr : ℕ → ℕ → ℕ} {ms : List Mem}
    {grp : ℕ → List (ℕ × ℕ)} (tie : ShapesTied codes shape layout num arr ms grp) {k : ℕ}
    (hk : k < 25) (μ : Fin (s k).NM) {i c : ℕ} (hi : i < Alg.symRows ((s k).m μ))
    (hc : c < (s k).k μ) {k' : ℕ} (hk' : k' < 25) (y : Mem) (hy : y ∈ ms) (hg : seatOf y ∈ grp k')
    (hn : numOf arr y = (seatBy (fLay layout num) X s k μ i c).1) :
    InMsg codes (y.1.l.get y.2).1 false (seatBy (fLay layout num) X s k μ i c).2.1
        (seatBy (fLay layout num) X s k μ i c).2.2 ∧
      padB codes (y.1.l.get y.2).1 false (seatBy (fLay layout num) X s k μ i c).2.1
        (seatBy (fLay layout num) X s k μ i c).2.2 = false := by
  obtain ⟨A, m, hA, hm, e, hin, hB⟩ := seat_inside hC hS h T num hk μ hi hc
  obtain ⟨as, hl, hmem⟩ := arrayOf_mem hA
  have key := tie _ as A m hl hmem hm k' hk' y hy hg (hn.trans e)
  rw [inMsg_of_key codes _ _ key, padB_of_key codes _ _ key]
  exact ⟨hin, hB⟩

end

end Meaning

#print axioms Meaning.arrayOf_mem
#print axioms Meaning.array_inside
#print axioms Meaning.seat_inside
#print axioms Meaning.seat_inside_members
