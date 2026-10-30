-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/DoorHead.lean: WHAT THE ROWS OF THE PROOF FILE's ENTRY TESTS SHARE. Definitions
alone.

The entry tests (`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean) are tests on public data: the
three public files and what is computed from them. The rows from the ninth on read the
public plan that the verifier computes from these files. That plan is computed ONCE for all rows:

  planOf      the public plan of the three files, or nothing where none is made: by the very
              function,
              at the very arguments, by which the proof file's IOP as written in Lean is made
              (`ProofFile.pureRoad.pub o pol lay KL`): so it is the same value (Laid/DoorHeadLaw.lean)
  atFullKey   the parameter file's strict scan has the full size's key (layers, width, vocabulary):
              the key test of the first row (`PlanWritten.fullKey`)
  every       a row that is asked at every size: where no plan is made it rejects
  atFull      a row that is true of the full size alone: at any other key it accepts without asking;
              where no plan is made it rejects

In the goals' scope the key is the full size's, so there a yes of `atFull` is a yes of the test.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.Ok.PlanWritten.Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Door

/-- **The public plan of the three public files**, computed once for all rows. -/
def planOf (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Option ProofFile.Pub :=
  (ProofFile.pureRoad.pub o pol lay KL).toOption

/-- The plan stands at the full size's key. -/
def atFullKey (Z : ProofFile.Pub) : Bool :=
  decide (PlanWritten.keyOfScan Z.p.X.P = PlanWritten.fullKey)

/-- **A row that is asked at every size.** -/
def every (M : Option ProofFile.Pub) (t : ProofFile.Pub → Bool) : Bool := M.any t

/-- **A row of the full size alone.** -/
def atFull (M : Option ProofFile.Pub) (t : ProofFile.Pub → Bool) : Bool :=
  M.any fun Z => !atFullKey Z || t Z

end VerifiableInference.Desc.Door
