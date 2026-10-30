-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyAccount.lean: the accounting of the rounds of a file's plan, compared with the
bits that a call asks for.

The accounting judges each round by itself. The plan of every chain of a key, an entry and a proof
follows from the public files, and it bounds the error of each round (OnBytes/Params/Planner.lean).
A round holds if its error, times 2^-work for the bits of proof of work before the verifier's
message, is at most 2^-target. The target is the parameter file's. Every comparison here is exact,
on upper bounds in binary numbers.

It follows, in part, account() of blocks/numbers/accounting.h and merged() of blocks/frame/files.h,
the first line of acctLinesH of verifier/src/vf_accounting_record.h, and the local routines acctOfH
and workHeldH of runStage in verifier/src/cp_verify.cpp. The local routine acctFormH there
is account after merged.

Main definitions: Accounting, merged, account, centibits, FileAcct, acctOfH, acctWhole, workHeldH,
Account.places.

What this file does not do: it prints no accounting, and it leaves out what the C++ type holds for
prints alone (sums of errors, numbers of hash calls, rounds near the target). It makes no plan. It
cannot tell whether the plans that it is handed are those under which the files' chains are read:
the caller must see to that. It does not ask whether a bound on a round's error is a true bound. No
theorem is stated here.

What differs from the C++.
 1. The error in hundredths of a bit is exact here, where the C++ rounds a floating-point logarithm
    down. The two numbers can differ by 1, in either direction, where the logarithm is closer to a
    whole hundredth than the rounding error of a double. Both numbers of a record
    (Stages.Acct.centibits, leastRound) can differ from the C++ program's in a wider band. A stage
    of the C++ program hands its record on as text, with the bits cut to six decimals. The call
    reads them back, adds the round's work (for leastRound alone), multiplies by 100 and rounds
    down, all in floating point. Where the logarithm is less than a millionth of a bit above a
    whole hundredth, the text is that hundredth, and at some hundredths the product falls below the
    whole number: the C++ number is then lower by 1, never higher. A round with 32 bits of work
    whose text is 96.020000 gives 12801 there and 12802 here. At a whole number of bits the product
    is exact. What this item says of the C++ is by our reading of the C++ source (not run here).
 2. To find the largest error, errors are compared exactly here, where the C++ compares their
    floating-point logarithms: two errors whose logarithms are the same double count as equal there
    and not here.
    What depends on 1 and 2 (call, stage, note and record are defined in
    OnBytes/Model/Stages.lean). The numbers on work in a call's closing lines can differ: the bits
    by a hundredth (1), and the bits of work where another round counts as the largest (2). The
    wider band of 1 changes printed numbers only, among them two fields of the line for programs
    (least-round, least-round-without-work): the C++ compares the record's bits with a stage's note
    as it has read them, before that product, and allows a difference of a hundredth (by our
    reading). By a double's rounding error (1) or by 2, one decision can differ too. Of its stages'
    notes a call takes the one with the fewest bits and compares its work with the work in the
    call's record (Stages.workFits). If the largest errors of two files print the same hundredth and
    have different work, one program can pass the call where the other ends it as not checked, in
    either direction. Both programs compare the error of every round, work counted, with the target
    before that step; an error of 0 needs no comparison (here in account: if a round does not hold,
    acctOfH refuses the file; in the C++ in blk::account, blocks/numbers/accounting.h: if a round
    does not hold, the local routine acctOfH of runStage in verifier/src/cp_verify.cpp rejects the
    file, in the stage that checks that file; by our reading). What a proof of a false statement
    could gain from this difference is not claimed or proved here.
 3. Among rounds with the same largest error and the same work the first of the plan is named here,
    the first by name in the C++.
 4. The note on work names a round by its name alone. The C++ adds the place of the round's block
    and writes '#' for every run of digits.
 5. A round counts as 1 in byWork and in the three counts of closeness terms. The C++ adds the
    number of rounds that an entry of its plan stands for; a plan here has an entry for each round.
-/
import OnBytes.Params.Planner
import OnBytes.Model.Stages

namespace OnBytes.Model.Verify

open Params (Planned PlanRound Binary Setting)

/-- The round with the largest error when work is left out. Among rounds with the same error it is
one with the fewest bits of work, and among these the first of the plan. -/
structure Largest where
  /-- the error -/
  error : Binary
  /-- the round's bits of work -/
  work : Nat
  /-- the round's name -/
  name : String
  deriving Inhabited

/-- The accounting of a plan, as far as a decision or a closing line of a call depends on it.
C++: blk::Accounting, in part. -/
structure Accounting where
  /-- the plan was admitted and some round has an error above 0 -/
  formed : Bool := false
  /-- every round holds at the target, work counted, and no round has the mark wordFault: what the
  planner says of how the round's error was computed (Params.Priced) contradicts the round
  (Params.wordFaultOf). Unlike Params.Planned.holds this does not ask oneDistance: a merged plan
  spans several chains, where two stages may share both codes. That is asked of each chain's own
  plan (Params.finishHeld). -/
  holds : Bool := false
  /-- some round holds only with its work -/
  needsWork : Bool := false
  /-- the target in bits of the setting under which the plan was made -/
  target : Nat := 0
  /-- the number of rounds with a closeness term (explained at Stages.Acct.closeOther) that rests on
  a lemma within a third of the code's distance (Params.CountSource.third). Read by tests only. -/
  closeThird : Nat := 0
  /-- the number of those that rest on an assumed theorem up to the Johnson radius (.johnson) -/
  closeJohnson : Nat := 0
  /-- the round with the largest error when work is left out; there is one if formed is true -/
  lists : Option Largest := none
  /-- the number of rounds whose error without work is above the target; where the accounting holds,
  these are the rounds that hold only with their work -/
  byWork : Nat := 0
  /-- the most bits of work that the setting has for any kind of error and any scope -/
  mostWork : Nat := 0
  /-- the largest of the rounds' errors when each is multiplied by 2^-work for its own bits of work;
  there is one if formed is true -/
  withWork : Option Binary := none
  deriving Inhabited

/-- Joins the plans of some chains, in their order, into one plan under the setting s. Returns none
if a chain's plan was made under another setting. C++: blk::merged, which also adds items of the
file between the chains; these have no round. -/
def merged (s : Setting) (chains : List Planned) : Option Planned :=
  if chains.all (·.set == s) then some ⟨s, chains.flatMap (·.rounds)⟩ else none

/-- Takes one round into the accounting. Of a round with the error 0 only the mark wordFault is
read. -/
def Accounting.take (s : Setting) (unit : Binary) (a : Accounting) (r : PlanRound) : Accounting :=
  let a := { a with holds := a.holds && !r.wordFault }
  let error := Params.wholeError s unit r
  if error.isZero then a
  else
    let close := fun (c : Params.CountSource) =>
      if r.why == .closeness && r.rests == c then 1 else 0
    let needs := !error.le (Binary.twoTo (-(s.target : Int)))
    let counted : Binary := ⟨error.m, error.e - (r.entry.work : Int)⟩
    { a with
      formed := true
      holds := a.holds && Params.roundHolds s unit r
      needsWork := a.needsWork || needs
      byWork := a.byWork + (if needs then 1 else 0)
      withWork :=
        match a.withWork with
        | some w => if w.lt counted then some counted else some w
        | none => some counted
      closeThird := a.closeThird + close .third
      closeJohnson := a.closeJohnson + close .johnson
      lists :=
        match a.lists with
        | some l =>
          if l.error.lt error || (l.error.le error && r.entry.work < l.work) then
            some ⟨error, r.entry.work, r.entry.name⟩
          else some l
        | none => some ⟨error, r.entry.work, r.entry.name⟩ }

/-- The most bits of work that a setting has for any kind of error and any scope. -/
def mostWork (s : Setting) : Nat :=
  [s.workField, s.workSample, s.workCloseness, s.workQuery, s.workSmall].foldl
    (fun n w => max n (max w.request (max w.shared w.once))) 0

/-- The accounting of a plan. Without a plan (the parameters were not admitted, the chains' plans
could not be made, or merged met a second setting) it is the empty accounting, which is not formed
and does not hold. C++: blk::account. -/
def account (p : Option Planned) : Accounting :=
  match p with
  | none => {}
  | some p =>
    p.rounds.foldl (Accounting.take p.set (Params.capped p.set))
      { holds := true, target := p.set.target, mostWork := mostWork p.set }

/-- Minus the binary logarithm of x in hundredths, rounded down: the largest c with
x ≤ 2^(-c / 100), and 0 if that is below 0 or x is 0. By whole numbers alone: x^100 is compared with
a power of two. -/
def centibits (x : Binary) : Nat :=
  if x.isZero then 0 else (-(100 * x.e) - (ceilLog2 (x.m ^ 100) : Int)).toNat

/-- The accounting as a stage hands it on. -/
def Accounting.record (a : Accounting) : Stages.Acct where
  target := a.target
  needsWork := a.needsWork
  centibits := (a.lists.map fun l => centibits l.error).getD 0
  work := (a.lists.map (·.work)).getD 0
  byWork := a.byWork
  mostWork := a.mostWork
  leastRound := (a.withWork.map centibits).getD 0
  closeOther := a.closeJohnson

/-- The record that reaches the call. There is one only if the accounting is formed and holds.
C++: acctLinesH of verifier/src/vf_accounting_record.h, which writes nothing otherwise. -/
def Accounting.handedOn (a : Accounting) : Option Stages.Acct :=
  if a.formed && a.holds then some a.record else none

/-- What the accounting of one file's plan gives a stage. -/
structure FileAcct where
  /-- the record of this file's accounting -/
  acct : Stages.Acct
  /-- a note, if some round holds only with its work -/
  work : Option Stages.WorkNote

/-- The accounting of one file's plan, compared with the bits asked for. s: the setting under which
the plans were made. chains: the plans of the file's chains, or
nothing if they could not be made. asked: the bits that the call asks for. object: the stage's name,
for the note. Refused as "security-bits": no
accounting was formed, some round does not hold, or the call asks for more than the target. In this
program every plan has passed Params.finishHeld, which rules out the second ground for plans made
under s. The first is left for a file whose rounds all have the error 0. No theorem states this.
C++: acctOfH. -/
def acctOfH (s : Setting) (chains : Option (List Planned)) (asked : Nat)
    (object : String) : Except String FileAcct :=
  let a := account (chains.bind (merged s))
  if !a.formed || !a.holds || a.target < asked then throw "security-bits"
  else
    pure
      { acct := a.record
        work :=
          if a.needsWork then
            a.lists.map fun l => ⟨centibits l.error, l.work, object ++ ": " ++ l.name⟩
          else none }

/-- The record that the stage request hands on: the accounting of all three files' plans laid end to
end. There is none if that accounting is not formed or does not hold; the call then ends as not
checked, unless a stage has said no. The bits asked for are not compared here. C++: the assignment
to acctNote after the stage's own acctOfH, and acctLinesH. -/
def acctWhole (s : Setting) (chains : Option (List Planned)) : Option Stages.Acct :=
  (account (chains.bind (merged s))).handedOn

/-- Compares two answers to the question whether a file's yes needs work: withWork, which the caller
takes from the file's plans (Params.needsWork), and the stage's note, which acctOfH makes from the
accounting. Both come from the same plans by the same comparison, so no file can make this test
fail: it guards this program's own text. No theorem states this. C++: workHeldH, which takes the
first from the verdict of the file's checker. -/
def workHeldH (withWork : Bool) (note : Option Stages.WorkNote) : Except String Unit :=
  if withWork != note.isSome then throw "internal-work-two-ways" else pure ()

/-- The names under which the functions of this file refuse. -/
def Account.names : List String := ["security-bits", "internal-work-two-ways"]

/-- The names that a round of a plan can have. C++: blocks/numbers/round_names.h. -/
def Account.roundNames : List String :=
  ["SEND seed", "SEND answer", "BAT", "BAT-sigma", "SPLIT", "PSC epsilon", "PSC round", "PSC Y",
   "PSC values", "ZERO", "LINE", "LKP shift", "JOIN", "LKP", "RNG", "FOLD epsilon", "FOLD round",
   "LOC", "CS", "BASE lambda", "BASE", "SEAL", "LAST", "REPLY", "RECORD", "LIN point", "LIN zeta",
   "LINK point", "LINK", "LINK phi"]

/-- Every text that the field place of a note on work can hold, if acctOfH is handed a stage's name
as object and plans whose rounds have names of roundNames: the stage's name, a colon, a blank and
the round's name. -/
def Account.places : List String :=
  ["key", "leaf", "request"].flatMap fun object =>
    Account.roundNames.map fun name => object ++ ": " ++ name

end OnBytes.Model.Verify
