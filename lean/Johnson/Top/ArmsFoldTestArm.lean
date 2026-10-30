-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldTestArm.lean: `armBoundD_test` (Johnson/Top/ArmsFoldTest.lean: the bound on the
check V of the key file) at the two concrete checks of the key file (concrete: defined in
this library, not parameters), the one with the lax Test and the one with the strict Test. Its two
hypotheses on the public strings become one, hO; its other hypotheses stay.

What this file states. `armBoundD_testL`: the bound at the check with the lax Test (`armTL`).
`armBoundD_testS`: at the check with the strict Test (`armTS`, both in
Johnson/TypedOracleCompiler/RecCompile/KeyAnsPr.lean). `armBoundD_test` takes the family of checks as a parameter V
and requires, of a set Pt of public strings and at every d: the check at d is a check in the sense
of `IsArmT`; over the hash function it asks no string of Pt (hno); a string of Pt codes no leaf and
no node under the coding at d (hT). At `armTL` and `armTS` the first is a theorem, and these checks
ask no point of the spare oracle (`hno_armTL`, `hno_armTS`,
Johnson/TypedOracleCompiler/RecCompile/KeyAnsPublic.lean). So hno and hT follow from hO. This reduces the question
whether hno and hT can be met together to one hypothesis: they are met by every family of codings
under which the public strings are points of the spare oracle. For a page that writes no string with
the tag of the number 169, the strings of calls with that number are such points
(OnBytes/TypedOracleCompiler/Run/Other169Any.lean [not in this library]), and at the format's strings every public
string is the string of a call with that number (`ptN_call169`, Johnson/Top/Pub/PubMany.lean).
The two are not joined here.

Under which hypotheses. hO: at every d, every string of Pt codes a point of the spare oracle under
the coding at d. The other hypotheses are those of `armBoundD_test`: Test's soundness round by round
among them.

What it does not show. hO is proved for no coding here. The record's wire S, the code of the answers
cA, the coding m and the reading Pub stay parameters, and so do L, aT, aL and W. All else that the
head of Johnson/Top/ArmsFoldTest.lean does not claim: soundness alone; no yes is shown; Test's
soundness is a hypothesis; the reading and the set of its public strings are fixed before the
function is drawn.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldTest

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D X' : Type}

/-- `armBoundD_test` at the check with the lax Test. Asked of the public strings: at every d each
codes a point of the spare oracle under the coding at d (hO). -/
theorem armBoundD_testL {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hO : ∀ d s, Pt s → IsOther (m d) s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub)
      (armTestOf (X' := X') (aL := aL) (fun d => armTL W (S d) (cA d)) m Pub)
      (holdsTestOf (W := W) m) fun tC tP =>
        (((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armBoundD_test hsT hlT hcT hW hA hSd hbT (fun d => isArmT_armTL W (S d) (cA d)) hlam m Pt
    (fun d s h => isOther_tree (m d) s (hO d s h))
    (fun d z => (hno_armTL (m d) (S d) (cA d) z).mono fun _ s h hp => h (hO d s hp))
    Pub hPc hPa hPr

/-- `armBoundD_test` at the check with the strict Test, at parameters p. That Test's wire has its
laws, which `isArmT_armTS` asks, is a field of hW. -/
theorem armBoundD_testS {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hlam : 0 < lam)
    (p : Params)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hO : ∀ d s, Pt s → IsOther (m d) s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub)
      (armTestOf (X' := X') (aL := aL) (fun d => armTS W (S d) (cA d) p) m Pub)
      (holdsTestOf (W := W) m) fun tC tP =>
        (((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armBoundD_test hsT hlT hcT hW hA hSd hbT (fun d => isArmT_armTS W (S d) (cA d) hW.T p) hlam m
    Pt
    (fun d s h => isOther_tree (m d) s (hO d s h))
    (fun d z => (hno_armTS (m d) (S d) (cA d) p z).mono fun _ s h hp => h (hO d s hp))
    Pub hPc hPa hPr

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_testL
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_testS
