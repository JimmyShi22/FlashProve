-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Test/Cs.lean: the code switch inside a proximity test, as a plain function on data.

Why. The program 'verify-on-bytes' makes the switch from one stage of a proximity test to the next
by `csVerify` (OnBytes/Iop/Cs.lean), which runs in a context. A step of the description is a
function on data, with no context across its border. `csTest` is that routine, line for line, over
any type σ of states. What it calls that is another routine in a context comes in as a record of
plain functions on σ (`CsParts`), so that each can be written, tried and replaced by itself:
 - the switch itself, with one element drawn behind the positions (`switchVerify` at
   withTheta = true);
 - the beginning of the test on the new group (`Blk.beginRun`);
 - the question whether the round closed last batches this number of rows (`Blk.requireRows`);
 - the reading of the statement (`Blk.statement`).
The type of `csTest P` is that of the field `cs` of `TestParts` (Johnson/Desc/Test/Frame.lean).

What is called by name, because it is a plain function already: the batching in the description's
own text, `Own.batch` (Johnson/Desc/Own/Batch.lean). It returns what the program's `Bat.combine`
(OnBytes/Iop/Bat.lean) returns, at all arguments (`batch_agrees`, Johnson/Desc/Own/BatchAgree.lean).



The order is the program's, and three things hang on it.
 - The rows are counted behind the beginning of the test: the number that is asked is that of the
   rows which the test takes in (the plain rows, the members' sample rows, the generator rows).
 - The batching is handed the statement as the beginning of the test has left it. Of the statement
   it reads the oracle messages' shapes alone, which the beginning of the test does not turn; the
   moment is kept because it is the program's.
 - The layout that is returned is the one that the beginning of the test returns, not a layout read
   again behind it.

The round's count of rows. The entry of the round in which the positions and the element are drawn
counts rows. The switch closes that round, and this function asks the count before it returns. So
no count is owed behind the function, if `askRows` asks what the program asks. A count that is owed
in front of it makes the switch's first closing refuse. The switch's first round ("SEND seed")
counts no rows in the planner's plans.

For whoever fills the parts. `statement` must read the statement of the very state that `beginRun`
and `askRows` return. A filling that reads another statement gets another row, and no refusal.

Kin. OnBytes/Slice/BlkCsRun.lean (`csVerify_inv`) says what a run of the program's routine on a view
has done, as a relation between two contexts, for one answer to a sample, no kept member, and
further oracle messages that are not sampled. It is a law on the program, no function that computes,
and it is not called here.

Main definitions: `CsParts`, `csTest`.

Where the text parts from the program's. A refusal has no name here. The dry run's branch of the
last call (the row { group := to }, with nothing computed) is not here: the batching is always
called.

Not claimed. No theorem is stated here. That this function returns what the program's routine
returns is not stated. Of the guards of a whole switch this function has one of its own: that the
rows can be batched (`Own.batch` gives a row). All others lie in the parts. No equation of the
protocol is tested here: every claim goes into the one row that is returned. Nothing on the dry
run. Nothing on soundness.


-/
import OnBytes.Iop.Cs
import Johnson.Desc.Own.Batch

set_option autoImplicit false

namespace VerifiableInference.Desc.Test
open OnBytes

/-- **What the code switch inside a proximity test calls**, as plain functions on a state. One
reading of the state, and three steps; a step returns its value and the new state, or nothing where
it refuses. -/
structure CsParts (σ : Type) where
  /-- the statement -/
  statement : σ → Statement
  /-- the switch from single rows to a target; the new oracle message joins the group of the given
  number; then further oracle messages of the same prover's message; true: one element is drawn
  behind the positions, and it is returned (`switchVerify`) -/
  switch : SingleRows → SwitchTarget → Nat → Array OracleNotice → Bool → σ →
    Option ((Switched × E) × σ)
  /-- the proximity test on the group of this number begins: its layout and its rows in the fixed
  order (`Blk.beginRun`) -/
  beginRun : Nat → σ → Option (RunInput × σ)
  /-- the round that was closed last batches this number of rows (`Blk.requireRows`) -/
  askRows : Nat → σ → Option σ

variable {σ : Type}

/-- **The code switch, then the batching of the new group's rows** with the powers of the element
that was drawn behind the positions. old: the single rows. T: the target. to: the number of the new
group. others: further oracle messages of the new oracle message's prover's message. Returns what
the switch returns, the one row, and the group's layout. The guard of its own: the rows can be
batched. -/
def csTest (P : CsParts σ) (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) (s : σ) : Option ((Switched × GroupRow × GroupLayout) × σ) :=
  match P.switch old T to others true s with
  | none => none
  | some ((out, theta), s1) =>
    match P.beginRun to s1 with
    | none => none
    | some (run, s2) =>
      match P.askRows run.rows.size s2 with
      | none => none
      | some s3 =>
        match Own.batch (P.statement s3) to run theta with
        | none => none
        | some row => some ((out, row, run.layout), s3)

end VerifiableInference.Desc.Test
