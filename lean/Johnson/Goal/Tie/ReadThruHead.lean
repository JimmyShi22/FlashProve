-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/ReadThruHead.lean: the two public readings of the goals' verifier ARE the two
values that the running head reads through the function O that is handed in: `PV.Head.cThru` and
`PV.Head.sevenThru` (Johnson/PV/HeadCore.lean), at the hash function `hashOf O`. Each is
Ladder/ReadThru.lean's equation under these names.
-/
import Ladder.ReadThru
import Johnson.PV.HeadCore

set_option autoImplicit false

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Tie
open _root_.Run (digToBytes bytesToDig)

/-- The three public files, as the running head takes them. -/
def asDescriptionFiles (Z : PublicFiles) : OnBytes.K.Pub := ⟨Z.pol, Z.lay, Z.KL⟩

/-- **`readConfig` returns `cThru`.** -/
theorem readConfig_thru (O : ByteArray → ByteArray) (Z : PublicFiles) :
    (readConfig Z).evaluate (hashOf O) = bytesToDig (PV.Head.cThru O (asDescriptionFiles Z)) :=
  readConfig_of O Z

/-- **`readMoreAt` returns `sevenThru`**, at the bytes of the digest that it is given. -/
theorem readMoreAt_thru (O : ByteArray → ByteArray) (G : EntryGround) (Z : PublicFiles) (c : Digest) :
    (readMoreAt G Z c).evaluate (hashOf O) =
      (PV.Head.sevenThru O G (asDescriptionFiles Z) (digToBytes c)).map bytesToDig :=
  readMoreAt_of O G Z c

/-- **The two readings, as `verify` makes them, return `cThru` and `sevenThru` at `cThru`**, where
`cThru` has 32 bytes (the running head tests that). -/
theorem readBoth_thru (O : ByteArray → ByteArray) (G : EntryGround) (Z : PublicFiles)
    (h : (PV.Head.cThru O (asDescriptionFiles Z)).size = 32) :
    (readBoth G Z).evaluate (hashOf O) =
      (bytesToDig (PV.Head.cThru O (asDescriptionFiles Z)),
        (PV.Head.sevenThru O G (asDescriptionFiles Z) (PV.Head.cThru O (asDescriptionFiles Z))).map bytesToDig) :=
  readBoth_of O G Z h

end VerifierAndGoals

#print axioms VerifierAndGoals.readConfig_thru
#print axioms VerifierAndGoals.readMoreAt_thru
#print axioms VerifierAndGoals.readBoth_thru
