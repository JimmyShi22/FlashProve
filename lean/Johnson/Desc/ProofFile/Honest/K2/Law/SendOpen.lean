-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SendOpen.lean: the kind "the code switch" (K2): WHEREVER THE
PROOF FILE's DESCRIPTION IS RETURNED, AT EVERY PLACE OF THE KIND's LOT THE FIRST LAW ON THE SENDER
(`SendSameLaw`, Honest/K2/Exact.lean) HOLDS OF THE LOT's OWN SENDER (`coreSender freshTable`): the
field `send` of `ExactAsks` there. One statement with its proof, one term; no definition.

  `send_open`    by `sendSameLaw_core` (Honest/K2/Law/AtCore.lean) and `noWord_open`
                 (Honest/K2/Law/SampledOpen.lean)

Limits. As good as another writer's theorem on the shared sending's rows that AtCore.lean calls.
Inside the law its own hypotheses stand as they were: the shared sending's public test and "the
table that rides has one row" at the place, the seeds, the positions: none is shown here. One field
of `ExactAsks` of eight. Where the lot has no place the sentence is idle. Nothing on the second law.
Nothing here says what the law would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.AtCore
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

/-- **Wherever the proof file's description is returned: the first law at every place of the lot.**
-/
theorem send_open {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ p ∈ switchPlaces Z Bs.G₀,
      SendSameLaw (coreSender freshTable) p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) :=
  fun p hp => sendSameLaw_core (noWord_open O p hp) fun _ _ _ _ _ => rfl

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.send_open
