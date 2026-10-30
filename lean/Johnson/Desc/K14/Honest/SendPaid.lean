--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SendPaid.lean: the premise SendSays of
Johnson/Desc/K14/Honest/SendKept.lean is a theorem, at all parameters: it is the shared sending's
own law send_holds_of_yes (Johnson/Prover/Send/SaysForth.lean). So the two shared sendings of the
linear claim keep what the statement claims, with no premise on credit.

  sendSays        SendSays Q, for every Q
  sendU_holds, sendOmega_holds   where "send o_u" or "send o_omega" accepts, its parameters pass
                  K1's test on the plan, its two rounds have the stated form and the OOD answers
                  shown are the sample rows' own left sides at the held words: AllMet
                  (Johnson/Desc/Means/Forth/AllMet.lean) in front, at the words w, gives AllMet
                  behind, at the held words

The rows V are free: the two theorems hold of any rows whatever, as long as the answers shown are
computed from them.

What is not claimed. That a sending accepts. Nothing on the written columns, on how the random
values are distributed, on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.SendKept
import Johnson.Prover.Send.SaysForth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (Rows held send_holds_of_yes)

/-- **The premise SendSays holds at all parameters.** -/
theorem sendSays (Q : VerifiableInference.Desc.K1.Par) : SendSays Q :=
  fun d x r₁ r₂ ids w V _ _ hy ha hI hH => send_holds_of_yes Q none d x r₁ r₂ ids w V hy ha hI hH

/-- **"send o_u" keeps what the statement claims.** -/
theorem sendU_holds (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hM : Means.AllMet rdE d.st w) :
    Means.AllMet rdE d'.st (held w d.st.oracles.size Q V) :=
  sendU_met P n Q inFront groups d d' r₁ r₂ gs w V (sendSays Q) hB hfit h ha hM

/-- **"send o_omega" keeps what the statement claims.** -/
theorem sendOmega_holds (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (d d' : St) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (w : Words Cb.Gl.E) (V : ℕ → Rows)
    (hB : VerifiableInference.Desc.K1.planOkOwn Q = true)
    (hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] =
      true)
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d [r₁, r₂] gs = .ok d')
    (ha : r₂.vals = answersAt Q d.st r₁ w V) (hM : Means.AllMet rdE d.st w) :
    Means.AllMet rdE d'.st (held w d.st.oracles.size Q V) :=
  sendOmega_met P n Q inFront groups d d' r₁ r₂ gs w V (sendSays Q) hB hfit h ha hM

end Desc.K14.Honest

#print axioms Desc.K14.Honest.sendSays
#print axioms Desc.K14.Honest.sendU_holds
#print axioms Desc.K14.Honest.sendOmega_holds
