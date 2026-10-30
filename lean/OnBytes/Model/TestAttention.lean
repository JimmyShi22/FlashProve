-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttention.lean: tests of OnBytes/Model/Attention.lean, the frame of the check of
the attention sub-proof.

The tests run when this file is compiled. The program does not import this file.

The padding of the lookup calls is described twice: by the number of padding keys in each tree,
which the shape derives from the calls' numbers of keys, and by the places that the key forms leave
to the padding, which laidPadding counts from the pieces. The check refuses unless the two agree. At
every shape that shapeHid returns, each piece has a weight in a key form, and both counts then come
from Forest.pubRun with the same arguments. So the eight guards on paddingAgrees show that
weighedUnits lists every unit, and nothing more. The numbers themselves are compared in
OnBytes/Model/TestAttentionShape.lean with known answers of the C++ test, copied by hand. The eight
configurations are typed there: the small configuration (small), and seven of the eight lines APUB
of verifier/tests/forest_weights.txt (all except small_both). They differ in the lists of calls, in
the depth of a tree and in the number of shifts. One more guard takes a segment out of its call's
list. Its pieces then count as padding, and the check's own comparison refuses.

Some tests of the frame are not meant to fail on an honest proof: that every call's key form is set
once, that every sent scalar has a coefficient in the one equation (this one can fail by chance of
the draws), the six tests of countsHeld at the end, and that the padding key is 0 where a key form
has no term for the padding. Here each is run on a record that is in order and on records in which
one thing is not, and the guards compare the name under which the routine refuses. A last guard ties
the sizes of the plan's own rounds (Plan.own) to a second computation of them (ownOf).

Not tested, here or in another test of this folder: the check as a whole (run) and the steps
Seam.start to Seam.finish, which can only be run inside a chain, on a whole sub-proof. So the tests
that run makes itself (internal-f-fun-closed, internal-slot-count, internal-f-fun-moved) are never
seen to refuse. hear and claims are run by OnBytes/Model/TestAttentionHonest.lean.
-/
import OnBytes.Model.Attention
import OnBytes.Model.TestAttentionShape
import OnBytes.Model.TestAttentionPlan

namespace OnBytes.Attention.Test

/-- True if a shape exists and both descriptions of the padding agree. -/
def paddingAgrees (lid : Nat) (cf : Cfg) : Bool :=
  match shapeHid lid cf with
  | .error _ => false
  | .ok (A, h) =>
    match laidPadding A h with
    | .error _ => false
    | .ok laid => laid == h.pub

-- profile4
#guard paddingAgrees 22 (cfgOf 4 2 1 4 2 13 13 #[8, 8] 5 7 6 11 7 8 list0)
-- profile4-12
#guard paddingAgrees 22 (cfgOf 4 2 1 4 2 12 13 #[8, 8] 5 7 6 11 7 8 list0)
-- profile4-11
#guard paddingAgrees 22 (cfgOf 4 2 1 4 2 11 13 #[8, 8] 5 7 6 11 7 8 list0)
-- the small configuration
#guard paddingAgrees 24 small
-- full_prompt
#guard paddingAgrees 28 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list0)
-- two-shifts
#guard paddingAgrees 28 (cfgOf 10 6 3 7 5 20 16 #[9, 8, 9, 9] 8 16 16 14 13 16 list0)
-- lidb-binds
#guard paddingAgrees 24 (cfgOf 10 6 3 7 5 20 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list0)
-- IX-by-itself
#guard paddingAgrees 28 (cfgOf 10 6 3 7 5 24 16 #[8, 8, 8, 8] 8 16 16 14 13 16 list1)

/-- The units whose pieces have a weight in a key form (weighedUnits). Each is given as the number
of its call and the place of its segment in Seg.all. -/
def unitsAt (lid : Nat) (cf : Cfg) : List (Nat × Nat) :=
  match shapeHid lid cf with
  | .error _ => []
  | .ok (A, _) => (weighedUnits A).map fun u => (u.1, Seg.all.idxOf u.2)

-- The calls are KR, KFD, R16, WH. The segments' places: rm 0, rd 1, fm 2, fd 3, wl 4, wh 5, ix 6.
#guard unitsAt 24 small == [(0, 0), (0, 1), (1, 2), (1, 3), (2, 4), (2, 6), (3, 5)]

/-! ## Tests of the frame that are not meant to fail on an honest proof -/

open OnBytes.Model in
/-- The name under which a routine of the sub-proof's engine refuses from the state F, on a view
without rounds. Returns none if the routine goes through. -/
def refusedAs (x : SubM Unit) (F : Fork := {}) : Option String :=
  match Blk.runNamed (x.run F) { entries := [], st := {} } false [] [] with
  | .error e => some e.name
  | .ok _ => none

-- every call's key form has been set, and set once
#guard refusedAs (allJoined { kf := #[{}, {}], joined := #[1, 1] }) == none
#guard refusedAs (allJoined { kf := #[{}, {}], joined := #[1, 0] }) == some "af-unclosed-call"
#guard refusedAs (allJoined { kf := #[{}, {}], joined := #[1, 2] }) == some "af-unclosed-call"
-- a slot of a message without a coefficient in the one equation
#guard refusedAs (noFreeSlot 2) { LS := #[oneE, oneE] } == none
#guard refusedAs (noFreeSlot 2) { LS := #[oneE, zeroE] } == some "internal-a-free-slot"
#guard refusedAs (noFreeSlot 1) { LS := #[oneE, zeroE] } == none

open OnBytes.Model in
/-- The engine's state at the end of a run. planned is the number of claims that the state has
planned, added the number that were added. The power of every planned claim has been handed out. -/
def endState (planned added : Nat) : Fork :=
  { nClaim := added, planClaimsF := planned, kapMapF := Array.replicate planned true }

open OnBytes.Model in
/-- The record of the smallness test at the end of a run that is in order: the sums of every matrix
were taken, the matrix of combinations was drawn once, and the lookup ran. -/
def endTail (P : Plan) : HTailF2 :=
  { P.seam.tl with
    foldTakenF := Array.replicate P.seam.tl.NM true, foldDrawn := 1, heard := some default }

open OnBytes.Model in
/-- The name under which the tests at the end refuse at the plan of the small configuration
(smallPlan in OnBytes/Model/TestAttentionPlan.lean); some none if they hold. planned and added are
given as differences from the plan's number of claims. f changes the record of the smallness test,
and g the engine's state. -/
def countsRefusal (planned added : Nat) (f : HTailF2 → HTailF2 := id) (g : Fork → Fork := id) :
    Option (Option String) :=
  smallPlan.toOption.map fun P =>
    refusedAs (countsHeld P (f (endTail P))) (g (endState (P.nLin + planned) (P.nLin + added)))

#guard countsRefusal 0 0 == some none
-- one claim more is planned in the state than was added
#guard countsRefusal 1 0 == some (some "internal-f-draws")
-- the power of one planned claim was not handed out: this test has no name of its own, so the
-- failure has the general name refused
#guard countsRefusal 0 0 id (fun F => { F with kapMapF := F.kapMapF.set! 0 false }) ==
  some (some "refused")
-- the sums of one matrix were not taken
#guard countsRefusal 0 0 (fun tl => { tl with foldTakenF := tl.foldTakenF.set! 0 false }) ==
  some (some "internal-f-draws")
-- as many claims were added as the state has planned, but not as many as the plan has
#guard countsRefusal 1 1 == some (some "internal-a-claim-count")
-- the matrix of combinations was drawn 0 times; then 2 times
#guard countsRefusal 0 0 (fun tl => { tl with foldDrawn := 0 }) ==
  some (some "internal-af-rows-booked")
#guard countsRefusal 0 0 (fun tl => { tl with foldDrawn := 2 }) ==
  some (some "internal-af-rows-booked")
-- the lookup of the smallness test did not run
#guard countsRefusal 0 0 (fun tl => { tl with heard := none }) ==
  some (some "internal-a-calls-booked")

open OnBytes.Model in
/-- The name under which paddingLaid refuses at the small configuration, after f has changed the
calls; some none if both descriptions of the padding agree. -/
def paddingRefusal (f : ACall → ACall) : Option (Option String) :=
  match shapeHid 24 small with
  | .error _ => none
  | .ok (A, h) =>
    some (refusedAs
      (paddingLaid { A with calls := A.calls.map f } { shape := h, leaves := default }))

#guard paddingRefusal id == some none
-- the padding key of the call of kind KR is row 1 of its table, which is not 0
#guard paddingRefusal (fun c =>
    if c.kind == .kr then { c with call := { c.call with t0 := 1 } } else c) ==
  some (some "internal-af-padding-key")
-- the call of kind WH holds no segment: the pieces of wh count as padding, and the counts differ
#guard paddingRefusal (fun c => if c.kind == .wh then { c with segs := [] } else c) ==
  some (some "internal-forest-padding-places")

-- The sizes of the own rounds in the plan (Plan.own, at smallPlan of
-- OnBytes/Model/TestAttentionPlan.lean) are those of the second computation (ownOf in
-- OnBytes/Model/TestAttentionShape.lean). rows is left out.
#guard (smallPlan.toOption.map fun P => decide ({ P.own with rows := 0 } = ownOf P.S)) ==
  some true

end OnBytes.Attention.Test
