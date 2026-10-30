-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySendIs.lean: the three closed terms
of (d2), and the test that holds a made list of sendings against a written one. Definitions alone.
  sendIs x W     x returned a list of sendings that PlanWritten.sameChain holds to be W.
  keyMade0 | keyMade1 | keyMade2   what sendsFrom's inner routine (IM.oneSend) returns for the key
                 file's three chains at the typed sizes keyFull, the written setting's number of
                 samples and the three written plans. (d2): IMR/KeySendsAtMade.lean.
No theorem. No soundness.
-/
import Johnson.IMR.KeySendsOne
import Johnson.G.SendsWritten
import Johnson.Desc.Ok.PlanWritten.SendsTest
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open Johnson.G
open VerifiableInference VerifiableInference.Number.ByRuns
open Lk6.AtPlan (keyFull)

def sendIs (x : Except String ChainSends) (W : ChainSends) : Bool :=
  match x with
  | .ok k => PlanWritten.sameChain k W
  | .error _ => false

def keyMade0 : Except String ChainSends :=
  (wSend keyFull.once.shape).bind fun w =>
    oneSend "key" 0 keyFull.codes (keyListed0 keyFull recordSet.samples w) keyThree.A.plan

def keyMade1 : Except String ChainSends :=
  (linSharedSends keyFull.once.shape recordSet.samples).bind fun s =>
    oneSend "key" 1 keyFull.codes s keyThree.B.plan

def keyMade2 : Except String ChainSends :=
  oneSend "key" 2 keyFull.codes
    (ioppSends "the own test" recordSet.samples keyFull.once.shape.choice.masksRide 1
      keyFull.once.shape.testOwn) keyThree.C.plan

end IM
