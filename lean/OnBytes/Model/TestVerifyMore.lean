-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyMore.lean: tests of planesHeld (OnBytes/Model/VerifyPublic.lean) and of the
test that readCall (OnBytes/Model/VerifyHeads.lean) makes on the kind of a named policy.

Each test is checked when the file compiles. The file is no part of the program.
-/
import OnBytes.Model.Verify

namespace OnBytes.Model.TestVerifyMore

open Verify Stages

-- planesHeld: a multiplicity has 2^kappa bits. Lay.callRecord (OnBytes/Model/LayerLayout.lean)
-- writes the constant 5, 32 bits, into every call, whatever the parameter file says: the test
-- guards the program's own records. A list in which one call has 16 bits is refused
#guard (planesHeld #[{ kappa := 5 }, { kappa := 5 }]).toOption.isSome
#guard (planesHeld #[{ kappa := 5 }, { kappa := 4 }]).toOption.isNone

/-- No file at all. -/
def noFiles : Files :=
  { policy := none, KL := none, layout := none, key := none, request := none, y := none,
    proof := none }

/-- True for the end of a call with a bad command line. -/
def isUsage {α : Type} : Except CallEnd α → Bool
  | .error (.usage _) => true
  | _ => false

/-- True for the end of a call whose parameter file, policy.txt, cannot be read. -/
def noParameterFile {α : Type} : Except CallEnd α → Bool
  | .error (.unreadable .policy) => true
  | _ => false

-- a named policy: the kind, then C, theta, cap, s, sh (what they mean: the head of
-- OnBytes/Model/VerifyHeads.lean). One of a kind that no command line can name ends the call
-- before a file is looked at. With the same numbers and the kind exact-match the call goes on to
-- the parameter file, which is missing. The other kind that can be named, clipped-gap, is not
-- tried here
#guard isUsage (readCall { policy := some ⟨"another-table", 32, 32, 0, 1, 5⟩ } noFiles)
#guard noParameterFile (readCall { policy := some ⟨"exact-match", 32, 32, 0, 1, 5⟩ } noFiles)

end OnBytes.Model.TestVerifyMore
