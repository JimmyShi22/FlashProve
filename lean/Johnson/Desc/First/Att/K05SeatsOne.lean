-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05SeatsOne.lean: TWO WRITINGS OF ONE PLAN, FIRST PART: WHICH ORACLE MESSAGE
HOLDS AN ADDRESS. The closed caller of the lookup on an attention link's calls finds the message of
a cell or of a mask entry by seatCalls (Johnson/Desc/First/Look/K3CallerAtt.lean): a number in the
list of the messages that stand sent (the kept ones, then the link's own). The programs' live
request finds it by ReqFrame.whereIs (OnBytes/Iop/Req.lean): a number in the statement; the batching
kind's dataOf and maskOracle (Johnson/Desc/First/Batch/Law/AsRow.lean) call that. K3CallerAtt.lean
says of itself that seatCalls is "a second writing of the programs' maps …; no theorem ties them".
Here is the tie for the message.

IS IT EMPTY HERE? NO MEMBER IS SHOWN: FrameIs is shown of no record.

Main names:
  (`oracleOfMsg f kept k`, Johnson/Desc/First/Att/K05DoorB.lean: message number k of the caller's list, as
    a number in the statement: below kept the live request's kept message number k, from kept on its
    own message number k - kept.)
  `FrameIs D i f`: four facts on the live request f, each of which a Bool with code can say: its
    shape is the description's; at its link its group's list "born" is that shape's; its link is i;
    a link is under way. `born_of_groups`: the second holds where its groups are its shape's.
  `whereIs_cell`: **where seatCalls D i gives a cell a seat z, the array's message, as whereIs finds
    it, is oracleOfMsg at z.msg.**
  `maskOracle_mask`: **the like for the mask row**: where seatCalls gives a mask entry a seat z,
    maskOracle f is oracleOfMsg at z.msg.
Premise beside FrameIs: hk: there are as many kept messages as entries in the group's list "born" (a
test on public data).
Both theorems equate two Options: the two writings AGREE; where the live request's arrays are too
short both sides are nothing: that the message is FOUND is not said.
Limits. WHICH PLACE of the message's table, and AT WHICH SEAT of the book the message sits, are not
spoken of. General in the sort of link, though the file stands among the files of kind K5.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Desc.First.Batch.Law.AsRow
import Johnson.Desc.First.Att.K05DoorB

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls keptAt bornAt messagesAt laidPlace)

/-- Four facts on the live request. -/
structure FrameIs (D : Sent) (i : ℕ) (f : ReqFrame) : Prop where
  shape : f.shape = D.shape
  born : (f.groups.getD f.link {}).born = bornAt D i
  link : f.link = i
  next : f.next = .laterOrClose

/-- The third fact holds where the live request's groups are its shape's: as the programs make them
(ReqFrame's start, OnBytes/Iop/Req.lean). -/
theorem born_of_groups {D : Sent} {i : ℕ} {f : ReqFrame} (hg : f.groups = reqGroups D.shape)
    (hl : f.link = i) : (f.groups.getD f.link {}).born = bornAt D i := by
  unfold bornAt
  rw [hg, hl, Array.getD_eq_getD_getElem?]
  cases (reqGroups D.shape)[i]? <;> rfl

/-- **Which message holds a cell: the two writings are one.** -/
theorem whereIs_cell {D : Sent} {i : ℕ} {f : ReqFrame} (H : FrameIs D i f)
    (hk : (keptAt D i).length = (bornAt D i).size) {t r c : ℕ} {z : Seat}
    (hz : seatCalls D i (.cell t r c) = some z) :
    ∃ bn a, (D.arrayOf.getD i #[])[t]? = some bn ∧ reqArray D.layout bn.1 bn.2 = some a ∧
      laidPlace a.blocks r c = some (z.row, z.place) ∧ z.mask = false ∧
      f.whereIs bn.1 a.message = oracleOfMsg f (keptAt D i).length z.msg := by
  unfold seatCalls at hz
  obtain ⟨bn, hbn, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨rp, hrp, hz⟩ := Option.bind_eq_some_iff.1 hz
  refine ⟨bn, a, hbn, ha, ?_⟩
  unfold ReqFrame.whereIs oracleOfMsg
  rw [H.next, H.born, H.link]
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hz
    obtain rfl := Option.some.inj hz
    refine ⟨hrp, rfl, ?_⟩
    simp [hb]
  · rw [if_neg hb] at hz
    obtain ⟨k, hkk, rfl⟩ := Option.map_eq_some_iff.1 hz
    refine ⟨hrp, rfl, ?_⟩
    have hlt : k < (bornAt D i).size := by
      unfold Array.idxOf? at hkk
      obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.1 hkk
      exact q.2
    simp [hb, hkk, hk, hlt]

/-- **Which message holds the mask row: the two writings are one.** -/
theorem maskOracle_mask {D : Sent} {i : ℕ} {f : ReqFrame} (H : FrameIs D i f) {j : ℕ} {z : Seat}
    (hz : seatCalls D i (.mask j) = some z) :
    z.mask = true ∧ z.row = 0 ∧ z.place = j ∧
      maskOracle f = oracleOfMsg f (keptAt D i).length z.msg := by
  unfold seatCalls at hz
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hz
  refine ⟨rfl, rfl, rfl, ?_⟩
  unfold maskOracle oracleOfMsg ReqFrame.whereIs
  unfold messagesAt at hm
  rw [H.shape, H.link, hm, H.next]
  simp

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.born_of_groups
#print axioms VerifiableInference.Desc.First.Att.P.whereIs_cell
#print axioms VerifiableInference.Desc.First.Att.P.maskOracle_mask
