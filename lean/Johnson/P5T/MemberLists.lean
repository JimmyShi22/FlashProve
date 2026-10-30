-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/MemberLists.lean: THE MEMBERS OF THE LAW ON COMMITTED WORDS, AT A PLAN, WITH CODE: as
plain lists (one entry a sending of the proof file's first chain: its sampled messages' shapes WITH
THE RADII: Johnson/G/LinkSig.lean: SendRow.sampled; and their seats off
Johnson/P5T/PlanSeats.lean); and the letter ms of the table of joints' composed filling as a term.

  `firstRows`, `memberLists`, `membersFault`: THE VERY TEXT OF
    Johnson/P5T/PlanNumbers.lean (not in this library), MOVED BY PROGRAM, no
    word turned (two of its lines are longer than 100 signs: left).
  `rowsAt? pol lay KL`: the sendings' rows of all seven chains (`Johnson.G.sendRowsOf`), or nothing
    where that maker refuses.
  `msAt Z lay`: **ms**: `msOf` (Johnson/Desc/Sound/PlanMemProofs.lean) of the members' lists at the
    rows of Z's own policy.txt and KL.bin and of layout.txt, and at the first chain's seats.
    layout.txt IS A LETTER BESIDE Z: the public part holds the two other files, not that one; the
    radii are priced off the planner's calls, whose maker reads it.
  `msAt_of_rows`: where the maker returns rows, ms is `msOf (memberLists rows (planSeats Z Z.D.1))`.

Limits. WHERE `sendRowsOf` REFUSES, `msAt` IS THE EMPTY LIST: EVERY SENTENCE "for all members"
THEN HOLDS OF NOTHING. WHOEVER FILLS ms WITH `msAt` OWES "(rowsAt? Z.pol lay Z.KL).isSome": a test
with code on the three public files. That the lists' shapes and labels are the planner's own is
`membersFault`'s to test. This file stands over Johnson/G/LinkSig.lean and so over the library's
files on codes. Nothing on soundness.

-/
import Johnson.P5T.NumbersOf
import Johnson.G.LinkSig
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VerifiableInference.Desc VerifiableInference.Desc.First

namespace P5T

def firstRows (rows : List Johnson.G.SendRow) : List Johnson.G.SendRow :=
  rows.filter fun r => r.file == "proof" && r.chain == 0

def memberLists (rows : List Johnson.G.SendRow) (ps : List PSeat) : MemberLists :=
  (firstRows rows).zipIdx.map fun r => (r.1.sampled, (ps.filter fun p => p.send == r.2 && p.smpd).map (·.seat))

/-- What is amiss between the rows (`sendRowsOf`) and the planner's sendings. -/
def membersFault (rows : List Johnson.G.SendRow) (ps : List PSeat) : List String :=
  (firstRows rows).zipIdx.filterMap fun r =>
    let mine := ps.filter fun p => p.send == r.2 && p.smpd
    if mine.map (·.shape) != r.1.sampled.map (·.1) then some s!"{r.1.label}: other shapes, or another order"
    else if mine.any fun p => p.label != r.1.label then some s!"{r.1.label}: another label"
    else none

/-- The sendings' rows of all seven chains (`Johnson.G.sendRowsOf`), where their maker returns. -/
def rowsAt? (pol lay KL : ByteArray) : Option (List Johnson.G.SendRow) :=
  (Johnson.G.sendRowsOf pol lay KL).toOption

/-- **ms.** -/
def msAt (Z : ProofFile.Pub) (lay : ByteArray) : List VerifiableInference.Desc.Sound.Mem :=
  VerifiableInference.Desc.Sound.msOf
    (memberLists ((rowsAt? Z.pol lay Z.KL).getD []) (planSeats Z Z.D.1))

/-- Where the maker returns rows. -/
theorem msAt_of_rows (Z : ProofFile.Pub) (lay : ByteArray) (rows : List Johnson.G.SendRow)
    (h : Johnson.G.sendRowsOf Z.pol lay Z.KL = .ok rows) :
    msAt Z lay = VerifiableInference.Desc.Sound.msOf (memberLists rows (planSeats Z Z.D.1)) := by
  unfold msAt rowsAt?
  rw [h]
  rfl

end P5T

#print axioms P5T.msAt_of_rows
