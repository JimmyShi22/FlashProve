-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MarkOfStart.lean: CONDITIONAL.

What is here. Two hypotheses of the laws on the feed-forward layers' own rounds (sub-protocol K4) at
a ready run's thread, from the test on the instance of the proof file's own description (`P5J.F0T`,
Johnson/P5J/AtTerm.lean: its field okStart), which the frame's statements over a run take anyway
(hx). hVd: the verifier's tests on the request's words that read no reply (`reqFine`,
Law/TokensSeat.lean): the end of the library's `reqOk_of_okStart`
(Johnson/AtFull/Shape/ReqOkOfStart.lean) is that definition's body. hmark: the first chain's start
bears no mark: the library's `Meaning.K2.start_noMark` (Johnson/IMR/EndFive.lean) has it where the
request passes that test and the public part is what the maker's road computes, which is a field of
h (`LaidAt.pub`, Johnson/P5J/LaidOpens.lean). The third of the kind, that the request file is whole
words, is `whole_of_okStart` (Law/W/WholeAtStart.lean). Nothing new is shown: a call, and two calls.
`k4_exchange_own_ready` (Law/ExchangeOwnReady.lean) calls the second, so that it and
`k4_exchange_own_still_ready` (Law/ExchangeOwnStill.lean) take no hypothesis on the mark beside h
and hx; `hVd_of_readyInput` (Law/ExchangeOwnInput.lean) calls the first.

  `reqFine_of_okStart`   **`reqFine Zp ξ.pub = true`**, from hx alone.
  `hmark_of_okStart`   **`(ProofFile.startS Zp ξ.pub).failed = none`**, from h and hx.

Not shown here. hx: THAT okStart ACCEPTS AT ANY INSTANCE: a hypothesis; the frame's `ready`
(Honest/Frame.lean) does not call it. Of okStart's two halves the first alone is spent (`ProofFile.okBy`).
The side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hx no example is known to us; `reqFine_of_okStart` takes no h. No test
that can fail stands beside them. `hmark_of_okStart`: THE FULL SIZE ALONE; both: the format's
second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other
property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 71 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 79 is not counted: all the numbers are floors. They
come with h and with Law/TokensSeat.lean. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one.
-/
import Johnson.AtFull.Shape.ReqOkOfStart
import Johnson.IMR.EndFive
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on hx. **WHERE THE SEATED DESCRIPTION's okStart ACCEPTS, THE REQUEST PASSES
`reqFine`.** The library's `reqOk_of_okStart` under our name for its end. -/
theorem reqFine_of_okStart {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) : reqFine Zp ξ.pub = true :=
  Johnson.AtFull.Shape.reqOk_of_okStart hx

/-- CONDITIONAL: on h and hx. **WHERE THE SEATED DESCRIPTION's okStart ACCEPTS, THE FIRST CHAIN's
START BEARS NO MARK.** -/
theorem hmark_of_okStart (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    (ProofFile.startS Zp ξ.pub).failed = none :=
  Meaning.K2.start_noMark h.laid.pub (Johnson.AtFull.Shape.reqOk_of_okStart hx)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.reqFine_of_okStart
#print axioms ProofFile.Honest.K4.W.hmark_of_okStart
