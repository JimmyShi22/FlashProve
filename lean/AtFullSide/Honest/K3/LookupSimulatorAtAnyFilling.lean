-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean: AT ANY FILLING. The kind "lookup" (K3): the
lookups' hand-in for their lot of rows with simulators, at whatever the maker `onlineProverFromPublicFiles`
(Honest/AtPure.lean) returns: at its own description, book, public part and ground. General in the
maker's filling and in the lookups' filling F. Two theorems. "Honest/" stands for
Johnson/Desc/ProofFile/Honest/.

  `lookupsOwnNoCoinAtAnyFilling`        `LookupsOwnNoCoin` at the return's book
  `lookupSimulatorHandInAtAnyFilling`   `LookupHandIn` (Honest/K3/Term/LookupSimulatorHandIn.lean:
                                        what is handed in is listed in its head) at the return's
                                        fields: a call of `lookupSimulatorHandInAtAReturn`, its
                                        three premises on the return paid

By what. The premise on the book: `lookupsOwnNoCoinInTheBookAtAnyFilling` (LookupsOwnNoCoin.lean).
The public part: `publicPartAtAnyFillingIsTheHeads` (the same file). The description:
`makers_ahead_at_atPure` (AtFullSide/K14/MakersBookOne.lean).

READ THE HEAD OF Honest/K3/Term/LookupSimulatorAtTheHead.lean: exact is the spender's half alone;
fresh is true and empty; On and bud are "true"; `Good` is at A and B "false".

Hypotheses that remain. head: the library's one hypothesis at the full size. made: that `onlineProverFromPublicFiles`
returns.

Limits. As in the heads of the files named. That F is the filling whose lot the maker's filling lays
is not asked here: E2E/Lookup/LookupSimulatorAtTheTerm.lean, LookupSimulatorAtTheBaseProver.lean.
Nothing on any property of the protocol.
-/
import AtFullSide.Honest.K3.LookupsOwnNoCoin
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorHandIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)

variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}

/-- **THE PREMISE ON THE BOOK HOLDS AT THE BOOK OF WHATEVER THE MAKER RETURNS**, by its name. -/
theorem lookupsOwnNoCoinAtAnyFilling
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    {makersFilling : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL makersFilling = .ok returned) :
    LookupsOwnNoCoin returned.B publicPart :=
  lookupsOwnNoCoinInTheBookAtAnyFilling head made

/-- **THE LOOKUPS' HAND-IN AT WHATEVER THE MAKER RETURNS**, general in the maker's filling and in
the lookups'. Conditional on the head and on the return. -/
theorem lookupSimulatorHandInAtAnyFilling
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    {makersFilling : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL makersFilling = .ok returned)
    (F : Pub → K3.Fill (Local W₀ Rc Inst Tr))
    (threads : Local W₀ Rc Inst Tr →
      Thread returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X
        Inst)
    (saids : Local W₀ Rc Inst Tr → Nat → Coins returned.B → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (falls : List (Fall returned.F.S₁)) :
    LookupHandIn returned.F returned.B ((lookupSimulatorLot F).rows returned.Z returned.G) threads
      saids falls :=
  lookupSimulatorHandInAtAReturn head returned (publicPartAtAnyFillingIsTheHeads head made)
    (AtFullSide.K14.makers_ahead_at_atPure head made).2 (lookupsOwnNoCoinAtAnyFilling head made) F
    threads saids falls

end AtFullSide.Honest.K3

#print axioms AtFullSide.Honest.K3.lookupsOwnNoCoinAtAnyFilling
#print axioms AtFullSide.Honest.K3.lookupSimulatorHandInAtAnyFilling
