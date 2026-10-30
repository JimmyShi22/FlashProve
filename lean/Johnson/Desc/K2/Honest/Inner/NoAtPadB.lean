-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/NoAtPadB.lean: FROM THE LIST OF A PAD's PLACES TO THE TEST BY ROW AND
PLACE: at a message without a mask row, an index inside its table that is no place of `padPlaces`
(OnBytes/Iop/Cs.lean) is one at whose row and place `padB` (Johnson/Desc/SeatAt.lean) says no. Three
statements with their proofs; no definition. Shapes, codes and indices alone: no value, no coin, no
round, no frame.

  `pad_at_copy` `Send.pad` returns at a kept member's copy's shape, since it does at the member's
                    own (`KeptFits.pad`)
  `padB_no_off_places` at a shape at which `Send.pad` returns, with an answer or more: an index
                    whose place lies below the row's length and which is no main place of the list:
                    `padB` says no
  `padB_no_in_table` the same at a statement's message without a mask row, for both parts, at an
                    index below the table's size: the mask part has no such index

WHY. A witness's accessor (`Wit.tab`, Johnson/Desc/Sound/MsgSig.lean) parts pad and message by
`padB`; the rows that a switch makes are known to spare the places of `padPlaces` (`padsUnread`,
Inner/PadsProof.lean). Whoever knows a witness's table only where `padB` says no needs this step to
speak of such rows.

How. `padB_no_off_places`: the library's `pad_of_padB` (Johnson/Goal/Meaning/LaidInside.lean),
turned round. `padB_no_in_table`: the library's `place_lt_ell` (Johnson/Desc/Means/ItemsLen.lean)
gives the place's bound under `Codes.lengthsOk`. `pad_at_copy`: `padFits_eq`, `padFits_iff`
(Johnson/Top/H0/Tw/K2/TargetAgree.lean) and `KeptFits`' fields. Kin, not called: the library's
`padRaw_iff_mem` (Johnson/Top/H/SwitchFront.lean): at a shape without mask rows and with JUST ONE
ANSWER, for a row and place inside the table, `padRaw` (the main arm of `padB`, as a sentence) holds
just where the index is one of `padPlaces`': BOTH WAYS THERE; here one way, at an answer or more
(the carrying message may have more); `pads_same` (Inner/PadsProof.lean): one list for a member and
its copy; `padB_of_pad` (LaidInside.lean): the way back, at one answer alone; another house's
`padB_of_room` (Johnson/Desc/ProofFile/Honest/Law/LaysRoom.lean): the like step from another list,
`padInMain`, which goes by row and place; and its `padInMain_pad` (the same file; `pad_has`,
Honest/Law/LaidLaw.lean, says the same): each place of that list is a main place of `Send.pad`, by
its index: THE TWO TOGETHER GIVE `padB_no_off_places` BY ANOTHER ROAD, not taken here: this file
stands over the library's files alone; our second author's `padInMain_iff_padB`
(Honest/K2/Law/PadPlaces.lean): that list and `padB` are one, at one answer.

Limits. One way alone: with more answers than one the list has places at which `padB` says no. A
message with a mask row: nothing is said. Beyond a table's size: nothing is said: there `padB` may
say yes. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Inner.PadsProof
import Johnson.Desc.Means.ItemsLen
import Johnson.Goal.Meaning.LaidInside
import Johnson.Top.H0.Tw.K2.TargetAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Means (tableSize place_lt_ell ellOf)
open VerifiableInference.Desc (padB)

/-- `Send.pad` returns at a copy's shape. -/
theorem pad_at_copy (codes : Codes) (o n : OracleShape) (K : _root_.Tw.K2.KeptFits codes o n) :
    (Send.pad codes n).isSome = true := by
  have h := (_root_.Tw.K2.padFits_iff codes o).1 K.pad
  rw [← _root_.Tw.K2.padFits_eq, _root_.Tw.K2.padFits_iff, K.newBare, K.degree, K.answers, K.length]
  rw [K.oldBare] at h
  simp only [Nat.lt_irrefl, false_or, if_false] at h ⊢
  exact h

/-- **Off the list, inside the row, `padB` says no.** -/
theorem padB_no_off_places (codes : Codes) (s : OracleShape)
    (hp : (Send.pad codes s).isSome = true) (ha : 1 ≤ s.answers) (i : Nat)
    (hlt : i / 2 ^ ceilLog2 s.mainRows < (codes.base.getD s.code default).ell)
    (hno : ∀ q ∈ padPlaces codes s, q.part = .main → q.index ≠ i) :
    padB codes s false (i % 2 ^ ceilLog2 s.mainRows) (i / 2 ^ ceilLog2 s.mainRows) = false := by
  obtain ⟨pad, hpad⟩ := Option.isSome_iff_exists.1 hp
  by_contra h
  obtain ⟨q, hq, h1, h2⟩ := Meaning.pad_of_padB hpad ha (Bool.eq_true_of_not_eq_false h) hlt
  refine hno q ?_ h1 ?_
  · unfold padPlaces
    rw [hpad]
    exact hq
  · rw [h2]
    exact Nat.mod_add_div' i _

/-- **At a statement's message without a mask row**: inside the table, off the list. -/
theorem padB_no_in_table (St : Statement) (o : Nat) (x : OnBytes.Oracle)
    (hx : St.oracles[o]? = some x)
    (hl : St.codes.lengthsOk = true) (hc : x.shape.code < St.codes.base.size)
    (hm : x.shape.maskRows = 0) (hp : (Send.pad St.codes x.shape).isSome = true)
    (ha : 1 ≤ x.shape.answers) (part : Part) (i : Nat) (hi : i < tableSize St o part)
    (hno : ∀ q ∈ padPlaces St.codes x.shape, q.part = part → q.index ≠ i) :
    padB St.codes x.shape (part == .mask) (i % 2 ^ ceilLog2 (x.shape.rows part))
      (i / 2 ^ ceilLog2 (x.shape.rows part)) = false := by
  cases part with
  | mask =>
    exfalso
    unfold tableSize Statement.has at hi
    rw [hx] at hi
    simp [OracleShape.rows, hm] at hi
  | main =>
    have h1 := place_lt_ell hl (o := o) (part := .main)
      (fun y hy => by
        obtain rfl := Option.some.inj (hx.symm.trans hy)
        exact hc) hi
    unfold Statement.rowBits ellOf at h1
    rw [hx] at h1
    exact padB_no_off_places St.codes x.shape hp ha i h1 hno

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.pad_at_copy
#print axioms VerifiableInference.Desc.K2.Honest.padB_no_off_places
#print axioms VerifiableInference.Desc.K2.Honest.padB_no_in_table
