-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyAccount.lean: tests of OnBytes/Model/VerifyAccount.lean, run when this file
compiles.

The program does not import this file.

Plans are made up by hand from rounds with given errors. The rounds draw no element of the field, so
that a round's whole error is the given one. What is tested: the logarithm in hundredths; when an
accounting is formed, holds and needs work; the numbers of a record; the three grounds on which
acctOfH refuses; a round with the mark wordFault; the note on work; the condition on the committer's
files; the joining of plans under one setting; when the stage request has a record to hand on; the
question whether the plans need work, compared with the note.
-/
import OnBytes.Model.VerifyAccount

namespace OnBytes.Model.TestVerifyAccount

open Verify
open Params (Planned PlanRound Binary Setting)

#guard centibits (Binary.twoTo (-128)) == 12800
#guard centibits ⟨3, -130⟩ == 12841
#guard centibits ⟨5, -130⟩ == 12767
#guard centibits ⟨1, 0⟩ == 0
#guard centibits ⟨4, 0⟩ == 0
#guard centibits ⟨0, 0⟩ == 0

/-- The setting: a target of 128 bits. -/
def set : Setting := {}

/-- A round with the error m 2^e, the given bits of work, and a kind and source of its error. -/
def round (name : String) (m : Nat) (e : Int) (work : Nat := 0)
    (why : Params.ErrorKind := .query) (rests : Params.CountSource := .johnson) : PlanRound :=
  { entry := { name := name, work := work, poss := 1 }, error := ⟨m, e⟩, why := why,
    rests := rests }

/-- A result in short: the refusal's name, or the record and the note. -/
abbrev Short : Type := String ⊕ (Stages.Acct × Option Stages.WorkNote)

/-- The result of acctOfH in short. -/
def short (rounds : List PlanRound) (asked : Nat := 128) : Short :=
  match acctOfH set (some [⟨set, rounds⟩]) asked "key" with
  | .error e => .inl e
  | .ok x => .inr (x.acct, x.work)

-- all rounds hold without work
#guard short [round "LOC" 1 (-128), round "CS" 3 (-131), round "SEAL" 0 0]
  == .inr (⟨128, false, 12800, 0, 0, 0, 12800, 0⟩, none)
-- a round above the target
#guard short [round "LOC" 1 (-128), round "CS" 3 (-129)] == .inl "security-bits"
-- it holds with its work, and the note names it
#guard short [round "LOC" 1 (-128), round "CS" 3 (-129) 1]
  == .inr (⟨128, true, 12741, 1, 1, 0, 12800, 0⟩, some ⟨12741, 1, "key: CS"⟩)
-- a later round with a smaller error, which needs no work and has none, changes nothing
#guard short [round "CS" 3 (-129) 1, round "LOC" 1 (-128)]
  == .inr (⟨128, true, 12741, 1, 1, 0, 12800, 0⟩, some ⟨12741, 1, "key: CS"⟩)
-- of two rounds with the same error the one with less work is named
#guard short [round "CS" 3 (-129) 2, round "LOC" 3 (-129) 1, round "BASE" 3 (-129) 1]
  == .inr (⟨128, true, 12741, 1, 3, 0, 12841, 0⟩, some ⟨12741, 1, "key: LOC"⟩)
-- work that is not enough
#guard short [round "CS" 5 (-129) 1] == .inl "security-bits"
#guard (short [round "CS" 5 (-129) 2]).isRight
-- the mark wordFault, at a round with an error and at one without
#guard short [{ round "LOC" 1 (-140) with wordFault := true }] == .inl "security-bits"
#guard short [round "LOC" 1 (-140), { round "SEAL" 0 0 with wordFault := true }]
  == .inl "security-bits"
-- no round with an error; no plan
#guard short [round "SEAL" 0 0] == .inl "security-bits"
#guard (acctOfH set none 128 "key").toOption.isNone
-- the call asks for more than the target, or for less
#guard short [round "LOC" 1 (-140)] 129 == .inl "security-bits"
#guard (short [round "LOC" 1 (-140)] 100).isRight
-- plans end to end; a chain under another setting
#guard acctWhole set (some [⟨set, [round "LOC" 1 (-128)]⟩, ⟨set, [round "CS" 3 (-129) 1]⟩])
  == some ⟨128, true, 12741, 1, 1, 0, 12800, 0⟩
-- of equal errors in two files the one with less work
#guard acctWhole set (some [⟨set, [round "CS" 3 (-129) 20]⟩, ⟨set, [round "CS" 3 (-129) 10]⟩])
  == some ⟨128, true, 12741, 10, 2, 0, 13741, 0⟩
-- the rounds whose closeness term rests on a source other than the lemma within a third of the
-- distance: of the four rounds, those of the kind closeness with the source johnson
#guard (acctWhole set (some [⟨set, [round "FOLD round" 1 (-140) 0 .closeness .third,
    round "LOC" 1 (-140) 0 .query .johnson,
    round "FOLD round" 1 (-140) 0 .closeness .johnson,
    round "FOLD round" 1 (-141) 0 .closeness .johnson]⟩])).map (·.closeOther) == some 2
-- the most bits of work that the setting has
#guard mostWork set == 0
#guard mostWork { set with workQuery := ⟨20, 28, 32⟩, workSmall := ⟨0, 40, 0⟩ } == 40
-- no record: a round of one file does not hold; the mark wordFault; no round with an error; no plan
#guard acctWhole set (some [⟨set, [round "CS" 3 (-129)]⟩, ⟨set, [round "LOC" 1 (-128)]⟩]) == none
#guard acctWhole set
  (some [⟨set, [{ round "SEAL" 0 0 with wordFault := true }]⟩, ⟨set, [round "LOC" 1 (-128)]⟩])
  == none
#guard acctWhole set (some [⟨set, [round "SEAL" 0 0]⟩]) == none
#guard acctWhole set none == none
#guard (merged set [⟨set, []⟩, ⟨{ set with target := 100 }, []⟩]).isNone
#guard (acctOfH set (some [⟨{ set with target := 100 }, [round "LOC" 1 (-128)]⟩]) 100 "key").toOption.isNone
-- whether the plans need work, and the note
#guard (workHeldH false none).isOk
#guard (workHeldH true (some ⟨12741, 1, "key: CS"⟩)).isOk
#guard (workHeldH true none).toOption.isNone
#guard (workHeldH false (some ⟨12741, 1, "key: CS"⟩)).toOption.isNone
#guard (match workHeldH true none with | .error e => e | .ok _ => "") == "internal-work-two-ways"
#guard Stages.internalName "internal-work-two-ways"

end OnBytes.Model.TestVerifyAccount
