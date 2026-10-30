-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/CountsFirst.lean: how many calls of the hash the reading of the first chain of a key
file and of a proof file makes at most, as a function of the chain's block alone.

OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean bounds the strings that the program's readers of a key file and
of a proof file ask of an oracle, under three premises each. The first says that a number N1 bounds
the number (fileNX, OnBytes/Tie/CostX.lean) of every description of the first chain that the reading
can make (OneTimeBelow, FirstBelow). The description is made of the rounds that the dry run of the
chain's block states, and its number reads these rounds alone. The dry run is a function of the
block and of what it starts from. So N1 is a function of these: no table and no file; the request
only as far as a caller makes the block of it, as the program does at a proof file.

Main definition: dryN (3 and the number of the rounds that a block's dry run states; 0 if it states
none).
Main theorems: oneTimeBelow, firstBelow: no premise.

Limits. At a proof file the block is a letter: that dryN is one number, or bounded, over the blocks
that the program makes of all requests is not shown here. Where a dry run states no rounds dryN is 0
and the two theorems say nothing. The shared and the second chain's numbers are not looked at here.
No number is evaluated.


-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.Counts

open OnBytes.Tie.CostX OnBytes.TwoPort.M.Asks
open OnBytes.Params (TableName KeyChains ProofChains)

/-- 3 and the number of the rounds that the dry run of the block b from the start s states; 0 if the
dry run states none. -/
def dryN {α : Type} (b : Blk α) (s : Start) : Nat :=
  match b.dryRun s with
  | some x => 3 + roundsNX x.1
  | none => 0

/-- The number of a description that is made of a dry run's rounds. -/
theorem fileNX_dry {α : Type} {b : Blk α} {s : Start} {x : Params.Rounds × α}
    (hx : b.dryRun s = some x) {g : Params.Given} {label : Nat} {statement : ByteArray}
    {rand : Fmt.Rand} {firstTree : Nat} {S : Fmt.SpecX}
    (e : Params.describeWith g label statement rand x.1 firstTree = some S) :
    fileNX S = dryN b s := by
  rw [fileNX_describeWith e]
  unfold dryN
  rw [hx]

/-- **The one-time chain of a key file**, at every parameter bytes and every table. -/
theorem oneTimeBelow (ks : KeyChains) (table : TableName) :
    OneTimeBelow ks table
      (dryN (OnBytes.Key.oneTime ks.oneTime) (OnBytes.Key.startOf ks.oneTime)) :=
  fun _ _ hx e => le_of_eq (fileNX_dry hx e)

/-- **The first chain of a proof file**, at every parameter bytes, table, number of a stored copy,
request item, request file's bytes and block. -/
theorem firstBelow (cs : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk OnBytes.Proof.FirstEnd) :
    FirstBelow cs table copy request words block (dryN block (OnBytes.Proof.firstStart cs.first)) :=
  fun _ _ hx e => le_of_eq (fileNX_dry hx e)

end OnBytes.TieK.Counts
