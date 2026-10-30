-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionOwn.lean: the messages of the own part of the attention sub-proof,
compared with the plan of its rounds.

The tests run when this file is compiled. The program does not import this file.

The own part is what comes between the lookup of the sub-proof's calls and its smallness test. Two
definitions say which rounds it has: the check itself (scores, divide, attain), whose dry run
(OnBytes/Iop/Ground.lean) notes each round's kind and items, and Params.planAttentionOwn
(OnBytes/Params/SubRounds.lean), which follows prover/attn/plan_rounds.h. Here the check is run dry
under the plan's entries, at smallCfg of OnBytes/Model/TestAttentionPlan.lean. The dry run goes
through only if each round is closed under its entry's name and with its entry's numbers of draws.
The guards also ask that each message has the bytes that its entry states, and that there are 110
rounds and 502 slots. The guard that ties the sizes from which the plan's rounds are made
(Plan.own) to the second computation of them (ownOf in OnBytes/Model/TestAttentionShape.lean) stands
in OnBytes/Model/TestAttention.lean, so that this file need not import TestAttentionShape.lean. No
file of the repository is read; the examples under prover/examples may have other numbers.

The own part can be run by itself. Its first scalars are in the message of a round that it closes
itself, and its last message is closed by its last sumcheck.

Where the expected numbers come from. 110 rounds: the record in
OnBytes/Model/TestAttentionHonestData.lean, which comes from a run of the C++ verifier, has 891
rounds, and the message with the first scalar of the own part follows the 781st. 502 slots are the
count of the own part in the head of OnBytes/Model/TestAttentionPlan.lean.

What is not tested: any value, since in a dry run all values are 0; and the numbers of batched rows,
which a dry run does not compare (Blk.requireRows in OnBytes/Iop/Ground.lean).
-/
import OnBytes.Model.AttentionScores
import OnBytes.Model.AttentionDivide
import OnBytes.Model.TestAttentionPlan

namespace OnBytes.Attention.TestOwn

/-- The own part of the check. Returns the slot after its last scalar. -/
def own (S : Shape) (zk : Array (Array E)) : Model.SubM Nat := do
  let _ ← scores S zk
  let _ ← divide S zk
  let _ ← attain S
  Model.SubM.slot

/-- A key point of zeros for each call, of the call's length. -/
def zeroPoints (S : Shape) : Array (Array E) :=
  S.calls.map fun c => Array.replicate c.call.n zeroE

/-- The dry run of the own part under the entries of its plan: the rounds that it notes and the
slot that it ends at. Returns none if the plan or the dry run fails. -/
def dryOwn (slots : Nat) : Option (List Fmt.Round × Nat) := do
  let P ← smallPlan.toOption
  let planned ← (Params.finish {} .request (Params.planAttentionOwn P.own)).toOption
  let block : Blk Nat := (own P.S (zeroPoints P.S)).run' (({} : Model.Fork).slots slots)
  let x ← Blk.dryRun block { entries := planned.rounds.map (·.entry), st := {} }
  pure (x.1.map (·.1), x.2)

/-- True if the round's message has the bytes that its entry states, its kind is that of its name,
and it opens nothing. -/
def fitsEntry (r : Fmt.Round) : Bool :=
  (r.items.map Fmt.Item.bytes).sum == r.entry.msg && Params.kindOf r.entry.name == some r.kind &&
  r.opens.isEmpty

-- the dry run goes through, and every round fits its entry
#guard ((dryOwn 502).map fun x => x.1.all fitsEntry) == some true
-- 110 rounds, 502 slots
#guard ((dryOwn 502).map fun x => (x.1.length, x.2)) == some (110, 502)
-- with one slot fewer the dry run fails; the guard does not see at which test
#guard (dryOwn 501).isNone

end OnBytes.Attention.TestOwn
