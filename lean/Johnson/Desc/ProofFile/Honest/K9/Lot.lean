-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Lot.lean: the lot's honest side with both kinds' halves: K9's lot
(`k9Ninth`, Johnson/Desc/ProofFile/Lot/K9.lean) lays the batching (K9) and the closing (K10) of
every segment. A definition with code, and one equation by `rfl`.

  `closeLot borne fold`   `batLot` (Honest/K9/Part.lean) at K10's halves (`K10.closings`,
                          Honest/K10/AtLot.lean). borne: the oracle messages that the closing's part
                          at a place carries: public data. fold: the prover's side of the rounds from
                          "FOLD epsilon" on: a parameter: the shared fold's part
  `closeLot_name`         its name is the lot's own

Limits. No line runs it: it wants a public part (`Pub`). `fold` is a letter: `closeLot` fixes no part. Which part is to
be laid for the closing: `foldShellT true` (Honest/K10/Sim.lean), which the head of Honest/K10/SeatLotT.lean calls the
cured, total part, and Honest/K10/SeatLot.lean and Words.lean the row's. SeatLotT.lean lays it by `batLot` itself, not
by `closeLot`. At the older caller's part (`closeFold`, Honest/K10/Words.lean) `closeLot` is not to be laid. No property
of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.Part
import Johnson.Desc.ProofFile.Honest.K10.AtLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9

variable {V W X : Type}

/-- **The lot's honest side**, with both kinds' halves. -/
def closeLot (borne : Pub → VerifiableInference.Desc.First.Close.Par → List ProofFile.Honest.K10.Borne)
    (fold : ProofFile.Honest.K10.ClosePub → Part V W X) : HLot V W X :=
  batLot (ProofFile.Honest.K10.closings borne fold)

/-- The name is the lot's own. -/
theorem closeLot_name
    (borne : Pub → VerifiableInference.Desc.First.Close.Par → List ProofFile.Honest.K10.Borne)
    (fold : ProofFile.Honest.K10.ClosePub → Part V W X) (Z : Pub) :
    (closeLot borne fold).name = (k9Ninth Z).name := rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.closeLot
#print axioms ProofFile.Honest.K9.closeLot_name
