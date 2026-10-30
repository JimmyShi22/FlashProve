-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/ToyWork.lean: for calls on test files, whether a yes rests on proof of work, and by
how much.

Proof of work counts toward the target: a round holds if its error times 2^-work is at most
2^-target. A result must therefore say both numbers wherever a round misses the target unless its
work counts. The whole call on a model's files does so, by the accounting of its plans
(OnBytes/Model/VerifyAccount.lean). This file hands the same accounting's pair out for the plans of
the small runs and of the toys' files.

The pair. Of the round with the largest error when work is left out: minus the binary logarithm of
that error, in bits with two decimals, rounded down; and that round's bits of work. It is spelled
as in "96.03 + 32".

The numbers of the line on work. The work that is counted: the most bits of work that the setting
declares for any kind of round, and the number of rounds that hold only with their work; nothing if
no round needs its work. And the first number of the pair, in hundredths of a bit. The calls on test
files print these, as the whole call does, in a line of its own before the passing line.

Main definitions: workPair, ToyRun.workPair, keyWorkPair, entryWorkPair, wholeWorkPair; workCount,
ToyRun.workCount, keyWorkCount, entryWorkCount, wholeWorkCount.

Not claimed here: no theorem is stated.
-/
import OnBytes.Plan.ToyShapes
import OnBytes.Model.VerifyAccount

namespace OnBytes.Plan

open OnBytes.Params

/-- The accounting of some chains' plans, laid end to end, all made under the setting s. bits: what
the caller asks of every round. Returns the pair if some round holds only with its work, and nothing
if none does. Refused under the name "security-bits" if no round has an error, if some round does
not hold, if a plan was made under another setting, or if the target is below bits. -/
def workPair (s : Setting) (plans : List Planned) (bits : Nat := 128) :
    Except String (Option String) :=
  (Model.Verify.acctOfH s (some plans) bits "").map fun a =>
    a.work.map fun w => Model.Stages.hundredths w.centibits ++ " + " ++ toString w.work

/-- The pair of a small run. -/
def ToyRun.workPair (r : ToyRun) (bits : Nat := 128) : Except String (Option String) :=
  Plan.workPair r.plan.set [r.plan] bits

/-- The pair of a key's three chains. -/
def keyWorkPair (c : Configured) (bits : Nat := 128) : Except String (Option String) :=
  workPair c.sized.set c.key bits

/-- The pair of an entry's chain. -/
def entryWorkPair (c : Configured) (bits : Nat := 128) : Except String (Option String) :=
  workPair c.sized.set [c.entry] bits

/-- The pair of all seven chains: key, entry and proof, as the whole call on a model's files
reckons it. -/
def wholeWorkPair (c : Configured) (bits : Nat := 128) : Except String (Option String) :=
  workPair c.sized.set (c.key ++ [c.entry] ++ c.proof) bits

/-- The same accounting, as the numbers of the line on work. Returns the work that is counted, if
some round holds only with its work, and the weakest round's bits without work, in hundredths.
Refused as `workPair` is. -/
def workCount (s : Setting) (plans : List Planned) (bits : Nat := 128) :
    Except String (Option Model.Stages.WorkCount × Nat) :=
  (Model.Verify.acctOfH s (some plans) bits "").map fun a =>
    (if a.acct.needsWork then some ⟨a.acct.mostWork, a.acct.byWork, a.acct.leastRound⟩ else none,
      a.acct.centibits)

/-- The numbers of a small run. -/
def ToyRun.workCount (r : ToyRun) (bits : Nat := 128) :
    Except String (Option Model.Stages.WorkCount × Nat) :=
  Plan.workCount r.plan.set [r.plan] bits

/-- The numbers of a key's three chains. -/
def keyWorkCount (c : Configured) (bits : Nat := 128) :
    Except String (Option Model.Stages.WorkCount × Nat) :=
  workCount c.sized.set c.key bits

/-- The numbers of an entry's chain. -/
def entryWorkCount (c : Configured) (bits : Nat := 128) :
    Except String (Option Model.Stages.WorkCount × Nat) :=
  workCount c.sized.set [c.entry] bits

/-- The numbers of all seven chains: key, entry and proof, as the whole call on a model's files
reckons them. -/
def wholeWorkCount (c : Configured) (bits : Nat := 128) :
    Except String (Option Model.Stages.WorkCount × Nat) :=
  workCount c.sized.set (c.key ++ [c.entry] ++ c.proof) bits

end OnBytes.Plan
