-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/ThirdAtConst.lean: TWO NAMES FOR TERMS AT THE COMPOSED MEANING's CLOSED CONSTANT,
    WHICH THE FILES ON THE CODE SWITCH's NAMED CONDITION (`P5J.AtMgA.K2Cond`,
    Johnson/Goal/Skeleton/Kinds/K2Bridge.lean) SHARE. Two abbreviations, no theorem. A law file: no
    sub-protocol imports it.

What is said.
  `frC Dw`: the first chain's frame at the laid data.
  `dC Hd`: the constant's structure of parameters under the head Hd (`AtMg.𝔇` at `AtMgA.𝔇`,
      Johnson/P5J/MgAtConst.lean | MgAtAll.lean, under a name of its own).

Limits. Names alone. The import lines are wider than the two names need: the files above take
    Johnson/P1K2R/Shorter.lean, TableAtConst.lean and the others through this one. No soundness is
        claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Goal.Skeleton.Kinds.K2Bridge
import Johnson.P1K2R.Shorter
import Johnson.P1K2R.TableAtConst
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Top.H0.K2Ties.AtConstant
import Johnson.Top.H0.Tw.K2C.FitsAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound

/-- The first chain's frame at the laid data. -/
abbrev frC (Dw : WholeD) : Frame := VerifiableInference.Desc.Sound.frameAt (Dw.at frS.P.T.a) (allOf
    (Dw.at frS.P.T.a)) (Dw.at frS.P.T.a).key₁ 0

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The constant's structure of parameters under the head (`AtMg.𝔇` at `AtMgA.𝔇`, under a name
    of its own). -/
noncomputable abbrev dC (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) := Hd.toAtMg.𝔇 Hd.𝔇

end VerifiableInference.Desc.First.K2Caller
