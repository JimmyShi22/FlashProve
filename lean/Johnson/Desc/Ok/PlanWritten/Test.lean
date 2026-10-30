-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/Test.lean: tests, with code, that hold a plan against the library's
written lists of rounds at the full size.

The library holds the rounds of the key file's and the proof file's chains at the full size as
written values (`dryKeyFull`, `dryProofFull`, Johnson/G/DryKeyLit.lean, Johnson/G/DryProofLit.lean).
Much that is proved speaks of these lists alone, and of the data made of them at the depth 32. That
they are what is computed from the public files is proved nowhere. A description of the protocol
that asks one of the tests of this file says no wherever its plan, at the full size's sizes, is
another one. So behind its yes what is proved at the written lists applies.

Each test has two arms. At the full size's key it asks that the lists of rounds and the stored
table's depth are the written ones. At every other key it says yes.

This file has definitions alone. Nothing is proved in it, and it imports no law on these tests. The
laws are in Johnson/Desc/Ok/PlanWritten/Rounds.lean, Pinned.lean, AtDesc.lean and Seat.lean, and, in
the goals' scope, in Johnson/Goal/Numbers/PlanWrittenScope.lean and PlanWrittenDescScope.lean.

What is here.
  `keyOfScan P`, `keyOf m`, `fullKey`: the key: three sizes of the model (layers, width, vocabulary)
    as the strict scan of the public parameter file has them; the key of an m, off the scan that m
    holds; the full size's key, (48, 5120, 202048).
  `declIs`, `declPinned file R k D d`: the test on declared rounds D, a depth d and a key k.
  `descPinned file R k F`, `descPinnedProof k F`, `descPinnedKey k F`: the test on a file's
    description (`FileDescription`, Johnson/Desc/Block.lean): `declPinned` at `F.roundsDeclaredByBlocks` and `F.tableDepth`.
    The key is a letter k here. Do not call these with a k of your own: call one of the next four.
  `seatPinnedProof pol F`, `seatPinnedKey pol F`: the test from the public parameter file: its
    strict scan (`polScan`, OnBytes/Model/Config.lean), then the test at the scan's key. Where the
    scan refuses, the test says no.
  `pinnedProofAt m F`, `pinnedKeyAt m F`: the test at the key of m, for a maker that holds the m
    made of the public files.
  `Six`, `sameR`, `sameSix`, `planIs L a m`, `planPinnedFull m`: the test on what the planner and
    the sendings have made (`Made`, Johnson/G/RoundsOfPlan.lean): all six lists and the depth.

Of OnBytes/Model/ this file names `polScan`, the type `PolScan` of what it returns, and the field
`X.P` of `Verify.Planned`, which `Made` holds: the scan of the public parameter file.

The planner and the hash functions. No definition of this file calls the planner or a hash function.
The imports hold both: `writtenOf`, `Decl3` and `Made` lie in Johnson/G/RoundsOfPlan.lean, which
also defines `madeOf`, and `madeOf` calls the planner, the format's hash function and its second
hash function by name. That `polScan` and `writtenOf` call no hash function is said from a reading
of their text; no theorem says it.

Limits. The tests pin nothing outside the full size's key: there they say yes of everything. A
`FileDescription` has no field for the model's sizes, so the test on a description is only as good as the
key that it is handed: a k that is not the key of the public parameter file's scan may open the arm
that says yes. `seatPinnedProof pol F` is only as good as its pol: it is to be asked at the same
string of bytes of which the scope is asked. What is compared: of every round of the lists its
entry, kind, items, what it opens and what it has stored, in order; and one depth. What is not
compared: each plan's six settings; the entry record; the entry file's rounds; the planner's records
with their bounds on the errors; sizes and codes but for the depth; the planner's public part but
for the three sizes; the links; the parameter bytes; of a description every field but `tableDepth`
and the rounds of the chains' blocks (`F.plans` is not compared). The written lists were printed
from this library's own planner, so a yes is no second witness for them. This file lays the tests
nowhere. It says nothing on soundness.


-/
import Johnson.G.RoundsOfPlan
import Johnson.G.DryProofLit
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Desc
open OnBytes.Params (Rounds)

variable {Xi : Type}

/-! ## The key -/

/-- The key, off a strict scan of a parameter file: three of the model's sizes: the number of
layers, the width, the size of the vocabulary. -/
def keyOfScan (P : OnBytes.Model.PolScan) : ℕ × ℕ × ℕ := (P.h.L, P.h.d, P.h.V)

/-- The key of what was made: off the strict scan of the parameter file that it holds. -/
def keyOf (m : Made) : ℕ × ℕ × ℕ := keyOfScan m.p.X.P

/-- The full size's key: the lines L, d, V of the stored full-size parameter file
(`VerifierAndGoals.behindA1`, Ladder/Stored.lean). -/
def fullKey : ℕ × ℕ × ℕ := (48, 5120, 202048)

/-! ## The test on declared rounds and a depth -/

/-- Of declared rounds and a depth: written out, the rounds are R, and the depth is a. Where
`writtenOf` refuses, the test says no. -/
def declIs (file : String) (R : Rounds × Rounds × Rounds) (a : ℕ) (D : Decl3) (d : ℕ) : Bool :=
  (match writtenOf file D with
    | .ok x => decide (x = R)
    | .error _ => false) && decide (d = a)

/-- **At the full size's key**: written out, the rounds are R, and the depth is 32. At every other
key: yes. k has to be the key of the strict scan of the public parameter file: any other k may open
the arm that says yes, and where the scan refuses the caller has to say no. Do not call this with a
k of your own: call `seatPinnedProof`, `seatPinnedKey`, `pinnedProofAt` or `pinnedKeyAt`. -/
def declPinned (file : String) (R : Rounds × Rounds × Rounds) (k : ℕ × ℕ × ℕ) (D : Decl3)
    (d : ℕ) : Bool :=
  if k = fullKey then declIs file R 32 D d else true

/-! ## The test on a file's description -/

/-- **The test on a description's declared rounds and depth.** k has to be the key of the strict
scan of the public parameter file: any other k may open the arm that says yes, and where the scan
refuses the caller has to say no. Do not call this with a k of your own: call `seatPinnedProof`,
`seatPinnedKey`, `pinnedProofAt` or `pinnedKeyAt`. -/
def descPinned (file : String) (R : Rounds × Rounds × Rounds) (k : ℕ × ℕ × ℕ)
    (F : FileDescription Xi) : Bool :=
  declPinned file R k F.roundsDeclaredByBlocks F.tableDepth

/-- The test at a proof file's description and the full size's written lists. k has to be the key of
the strict scan of the public parameter file: any other k may open the arm that says yes, and where
the scan refuses the caller has to say no. Do not call this with a k of your own: call
`seatPinnedProof` or `pinnedProofAt`. -/
def descPinnedProof (k : ℕ × ℕ × ℕ) (F : FileDescription Xi) : Bool :=
  descPinned "proof file" dryProofFull k F

/-- The test at a key file's description and the full size's written lists. k has to be the key of
the strict scan of the public parameter file: any other k may open the arm that says yes, and where
the scan refuses the caller has to say no. Do not call this with a k of your own: call
`seatPinnedKey` or `pinnedKeyAt`. -/
def descPinnedKey (k : ℕ × ℕ × ℕ) (F : FileDescription Xi) : Bool :=
  descPinned "key file" dryKeyFull k F

/-! ## The forms to call -/

/-- **The test on a proof file's description, from the public parameter file.** The key is read off
the file's strict scan. Where the scan refuses, the test says no. It calls no planner and no hash
function. It is to be asked at the same string of bytes of which the scope is asked. -/
def seatPinnedProof (pol : ByteArray) (F : FileDescription Xi) : Bool :=
  match OnBytes.Model.polScan pol with
  | .ok P => descPinnedProof (keyOfScan P) F
  | .error _ => false

/-- The like for a key file's description. -/
def seatPinnedKey (pol : ByteArray) (F : FileDescription Xi) : Bool :=
  match OnBytes.Model.polScan pol with
  | .ok P => descPinnedKey (keyOfScan P) F
  | .error _ => false

/-- **The test on a proof file's description, for a maker that holds its own m.** The key is m's. m:
what the planner returned at the public files of which the description is made. -/
def pinnedProofAt (m : Made) (F : FileDescription Xi) : Bool := descPinnedProof (keyOf m) F

/-- The like for a key file's description. -/
def pinnedKeyAt (m : Made) (F : FileDescription Xi) : Bool := descPinnedKey (keyOf m) F

/-! ## The test on what was made -/

/-- The written rounds of the key file's and of the proof file's three chains. -/
abbrev Six : Type := (Rounds × Rounds × Rounds) × (Rounds × Rounds × Rounds)

/-- Two lists of written rounds are the same. -/
def sameR (a b : Rounds) : Bool := decide (a = b)

/-- Six lists are the same, list by list. -/
def sameSix (x L : Six) : Bool :=
  sameR x.1.1 L.1.1 && sameR x.1.2.1 L.1.2.1 && sameR x.1.2.2 L.1.2.2 && sameR x.2.1 L.2.1 &&
    sameR x.2.2.1 L.2.2.1 && sameR x.2.2.2 L.2.2.2

/-- **Of what the planner and the sendings have made**: the rounds are L and the depth is a. It
takes no file and no digest. Where the rounds or the depth are not made, the test says no. -/
def planIs (L : Six) (a : ℕ) (m : Made) : Bool :=
  match roundsAt m, depthOf m with
  | .ok x, .ok d => sameSix x L && decide (d = a)
  | _, _ => false

/-- **At the full size's key** the six lists of rounds and the depth are the written ones. At every
other key: yes. -/
def planPinnedFull (m : Made) : Bool :=
  if keyOf m = fullKey then planIs (dryKeyFull, dryProofFull) 32 m else true

end VerifiableInference.PlanWritten
