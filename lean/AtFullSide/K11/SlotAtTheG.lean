-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/SlotAtTheG.lean: the kind K11's lot with its simulator, for the field rows of OpenG
(AtFullSide/Honest/TheLetters.lean).

  k11SimLot        the lot's name and the kind's rows
  k11SimLot_fit    with the simulators forgotten the rows are the filling's sides of the lot
  k11_lot_named    the kind's lot of the filling (k11_split) has that name

Limits. Names and lists alone. What the simulator does is in LendsAtTheTerm.lean.
-/
import AtFullSide.K11.ForTheRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K11
open OnBytes.HonestTrace (Sz)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest
open ProofFile.Honest.K11
open AtPublicFiles.AtFiles.HonestTerm.K11Term

/-- **The kind's lot with its simulator.** -/
def k11SimLot {W₀ : Type} (I : WiderIn W₀) : SLot (Input W₀) (Input W₀) Unit ProofFile.Inst :=
  ⟨"the merge of the weights' claims", k11Rows I⟩

/-- **With the simulators forgotten the rows are the filling's sides of the lot.** -/
theorem k11SimLot_fit {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz) (Zq : ProofFile.Pub)
    (G : ProofFile.Ground) :
    ((k11SimLot I).rows Zq G).map (·.half) =
      (HLot.byPub I.weights (LongLots.plain o S openHonest).k11 :
        HLot (Input W₀) (Input W₀) Unit).halves Zq G :=
  rfl

/-- **The lot's name is the filling's.** -/
theorem k11_lot_named {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz) :
    (HLot.byPub I.weights (LongLots.plain o S openHonest).k11 :
      HLot (Input W₀) (Input W₀) Unit).name = (k11SimLot I).name :=
  rfl

end AtFullSide.K11

#print axioms AtFullSide.K11.k11SimLot_fit
#print axioms AtFullSide.K11.k11_lot_named
