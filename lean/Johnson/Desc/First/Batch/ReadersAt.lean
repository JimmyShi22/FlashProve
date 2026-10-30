-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ReadersAt.lean: THE RUNS' READERS, SEGMENT BY SEGMENT, AS ONE TERM OFF THE
CHAIN's
LINKS AND THE PUBLIC PARAMETERS: the term that is meant for the letter Rd of the table of joints'
composed
filling (Johnson/Desc/First/PubAll.lean). Definitions with code; three equations. No Mathlib.
  `phAt X m`: the head's public numbers, layout and sub-proof's plan off the public parameters, with
  the
    place of the reads' quiet step at segment m: what the filling of the second hole takes.
  `holesAt X mH m l`: the two holes of `readersOfLink`
  (Johnson/Desc/First/Batch/ReadersOfLink.lean): the
    first: `smallReader` (Johnson/Desc/First/Batch/SmallReader.lean), at every segment; the second:
    at
    the head's segment (m == mH) the output head's authors' `k6Silent`
    (Johnson/Desc/Kinds/Law/K6SilentCode.lean) at the link's own runs; elsewhere nothing.
  `readersAt lk X mH m`: `readersOfLink` at these holes and at link number m (lk m); where there is
  no
    such link: a reader that answers nowhere.
  `readersAt_some`, `readersAt_none`: the two arms.
  `smallReader_same`: the first hole's reader reads of the verifier's state its `tl?` and its
  `funs?` alone.
Limits: lk is a letter here (meant: the proof file's first chain's links off the public part). THESE
THREE DEFINITIONS HAVE RUN NOWHERE: on our sheets `readersOfLink` has run at both stored plans with
the
second hole filled so and THE FIRST HOLE EMPTY, over copies of the second hole's three definitions;
`smallReader` has run apart. `phAt`'s place is as these sheets laid it; `k6Silent` reads of its
first
argument the three other fields alone. Nothing on what a reader answers. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.SmallReader
import Johnson.Desc.Kinds.Law.K6SilentCode
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent)

/-- What the filling of the second hole takes, off the public parameters. -/
def phAt (X : OnBytes.Model.Verify.Public) (m : Nat) : K8.ReadsQuiet.PH :=
  ⟨⟨1, some m, 5, .K1⟩, X.hS, X.HLy, X.H⟩

/-- The two holes at segment m. -/
def holesAt (X : OnBytes.Model.Verify.Public) (mH m : Nat) (l : Link S Claim) : LinkHoles :=
  { small := smallReader
    silent := if m == mH then k6Silent (phAt X m) (statesOfLink l) else fun _ _ _ => none }

/-- **The runs' readers at segment m.** -/
def readersAt (lk : Nat → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH m : Nat) :
    Readers :=
  match lk m with
  | some l => readersOfLink (holesAt X mH m l) l
  | none => ⟨fun _ _ _ => none⟩

theorem readersAt_some (lk : Nat → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m : Nat) (l : Link S Claim) (h : lk m = some l) :
    readersAt lk X mH m = readersOfLink (holesAt X mH m l) l := by
  unfold readersAt
  rw [h]

theorem readersAt_none (lk : Nat → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m : Nat) (h : lk m = none) : readersAt lk X mH m = ⟨fun _ _ _ => none⟩ := by
  unfold readersAt
  rw [h]

/-- What the first hole's reader reads of the verifier's state: two of its readers' answers. -/
theorem smallReader_same (s s' : S) (et : s'.tl? = s.tl?) (ef : s'.funs? = s.funs?) :
    smallReader s' = smallReader s := by
  unfold smallReader
  rw [et, ef]

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.smallReader_same
#print axioms VerifiableInference.Desc.K9.readersAt_some
#print axioms VerifiableInference.Desc.K9.readersAt_none
