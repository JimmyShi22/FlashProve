-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldSessArm.lean: `armBoundD_sess` (Johnson/Top/ArmsFoldSess.lean: the bound on the
check V of the proof file) at the two concrete checks of the proof file (concrete: defined
in this library, not parameters), the one with the lax session and the one with the strict session.
Its hypotheses on the family of checks are proved, and its two hypotheses on the public strings
become one, hO; its other hypotheses stay.

What this file states. `armBoundD_sessL`: the bound at the check with the lax session (`armBL`).
`armBoundD_sessS`: at the check with the strict session (`armBS`, both in
Johnson/TypedOracleCompiler/RecCompile/ProofAnsPr.lean). After Johnson/Top/ArmsFoldTestArm.lean, which has this for
the key's check. `armBoundD_sess` takes the family of checks as a parameter V and requires, of a set
Pt of public strings and at every d: the check at d is a check in the sense of `IsArmB` whose log
begins with the seed's queries (`HeadSeedB`); over the hash function it asks no string of Pt (hno);
a string of Pt codes no leaf and no node under the coding at d (hT). At `armBL` and `armBS` the
first two are theorems (the second in Johnson/TypedOracleCompiler/RecCompile/ProofAnsStage.lean), and these checks
ask no point of the spare oracle (`hno_armBL`, `hno_armBS`,
Johnson/TypedOracleCompiler/RecCompile/ProofAnsPublic.lean). So hno and hT follow from hO.

Under which hypotheses. hO: at every d, every string of Pt codes a point of the spare oracle under
the coding at d. The other hypotheses are those of `armBoundD_sess`: the session's soundness round
by round among them.

What it does not show. hO is proved for no coding here. The record's wire S, the code of the answers
cA, the record r₀, the coding m and the reading Pub stay parameters, and so do L, aT, aL, W and the
type of keys. All else that the head of Johnson/Top/ArmsFoldSess.lean does not claim: soundness
alone; no yes is shown; the session's soundness is a hypothesis; the public strings are fixed before
the function is drawn.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldSess
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsStage

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D Wn Kt : Type}

/-- `armBoundD_sess` at the check with the lax session. Asked of the public strings: at every d each
codes a point of the spare oracle under the coding at d (hO). -/
theorem armBoundD_sessL (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs) (hbB : Err.Below εB εs) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hO : ∀ d s, Pt s → IsOther (m d) s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ : Kt => Pub)
      (armSessOf (aT := aT) (aL := aL) (fun d => armBL W (S d) (cA d) r₀) m Pub)
      (holdsSessOf (W := W) Rno m) fun tC tP =>
        (((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armBoundD_sess Rno wit hsB hlB hco hW hA hSd hbB (fun d => isArmB_armBL W (S d) (cA d) r₀)
    (fun d => headSeedB_armBL (S d) (cA d) r₀) hlam m Pt
    (fun d s h => isOther_tree (m d) s (hO d s h))
    (fun d z => (hno_armBL (m d) (S d) (cA d) r₀ z).mono fun _ s h hp => h (hO d s hp))
    Pub hPc hPa hPr

/-- `armBoundD_sess` at the check with the strict session, at parameters p. That the session's wire
has its laws, which `isArmB_armBS` asks, is a field of hW. -/
theorem armBoundD_sessS (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs) (hbB : Err.Below εB εs) (hlam : 0 < lam) (p : Params)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hO : ∀ d s, Pt s → IsOther (m d) s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ : Kt => Pub)
      (armSessOf (aT := aT) (aL := aL) (fun d => armBS W (S d) (cA d) r₀ p) m Pub)
      (holdsSessOf (W := W) Rno m) fun tC tP =>
        (((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armBoundD_sess Rno wit hsB hlB hco hW hA hSd hbB
    (fun d => isArmB_armBS W (S d) (cA d) r₀ hW.B p)
    (fun d => headSeedB_armBS (S d) (cA d) r₀ p) hlam m Pt
    (fun d s h => isOther_tree (m d) s (hO d s h))
    (fun d z => (hno_armBS (m d) (S d) (cA d) r₀ p z).mono fun _ s h hp => h (hO d s hp))
    Pub hPc hPa hPr

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_sessL
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_sessS
