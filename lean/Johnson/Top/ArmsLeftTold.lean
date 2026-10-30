-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsLeftTold.lean: the record `ArmsLeft b` (Johnson/Top/FrontPaid.lean: the bounds on
the input's checks of the key file and of the proof file, and that neither tosses a coin) at the
input whose typed key holds a part of a public reading's value (`ArmFam.told`,
Johnson/Top/ArmsTwoSpellings.lean), from bounds on the two typed checks that ask for their public
digests themselves. The two bounds are hypotheses.

What this file states. `armsLeft_told`: `ArmsLeft b` at every b for `F.told encT c₀`. It is
`armsLeft_of_bounds` (Johnson/Top/ArmsLeftOf.lean) at r := `F.told encT c₀`. There each check is
"run F's reading (a computation that queries the hash function); no, unless the part of its value is
the key's c; then F's member at that value". So what is required of r's checks is required here of
F's members at the value of F's reading. `noCoin_told`, `yes_told`: the two steps on "run the
reading; no, unless the part is c; then A d": it tosses no coin if the reading and every A d toss
none, and its yes at a function gives the yes of A at the reading's value there.

Under which hypotheses. By name:
  * the key file's and the proof file's members toss no coin, at every d (hnK, hnP);
  * at every function f, where the member at the value of F's reading at f says yes, "the typed
    check's own reading, then the typed check at its value through its own coding" says yes (hyK,
    hyP).
Also required, as in ArmsLeftOf.lean: F's reading tosses no coin (hF); b's reading tosses none at
any key (hb); each typed check's own reading tosses none (hPK, hPP); each member of a typed family
meets `IsArmT` | `IsArmB` (hVT, hVB); the two equations of words (wK, wP); the two bounds (bK, bP),
at errors that are at most b's (hεK, hεP). A member may ask the function: a member that runs the
typed check's own reading and then the typed check meets hyK or hyP by definition.

What it does not show. All that the head of ArmsLeftOf.lean does not claim: the two bounds are
premises, and their own premises are proved in none of these files: what is required moves to them
and is not proved; the two equations of words (wK, wP) are shown of no coding. F is a parameter: no
family is given here. b is any record `BesideArmsCD` of that input: its reading b.rd is a parameter
of its own, tied to F's reading by nothing but wK and wP. Nothing is said of the test of c: it only
makes the check say no more often. Soundness alone.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsLeftOf
import Johnson.Top.ArmsTwoSpellings

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles

/-- "Run the reading; no, unless the part of its value is c; then A at that value" tosses no coin,
if the reading and A toss none. -/
theorem noCoin_told {D : Type} {Pub : OComp (rom 256) D} (hP : Pub.NoCoin) (part : D → Dig 256)
    {A : D → OComp (rom 256) Bool} (hA : ∀ d, (A d).NoCoin) (c : Dig 256) :
    (Pub.bind fun d => if part d = c then A d else .pure false).NoCoin :=
  hP.bind fun d => by
    split
    · exact hA d
    · trivial

/-- Its yes at a function holds the yes of A at the reading's value there. -/
theorem yes_told {D : Type} (Pub : OComp (rom 256) D) (part : D → Dig 256)
    (A : D → OComp (rom 256) Bool) (c : Dig 256) (f : Fam (rom 256))
    (h : (Pub.bind fun d => if part d = c then A d else .pure false).det f = true) :
    (A (Pub.det f)).det f = true := by
  rw [OComp.det_bind] at h
  split at h
  · exact h
  · exact Bool.noConfusion h

variable (F : ArmFam) (encT : Dig 256 × KeyRoot 256 F.L → Option ZKCP.Str) (c₀ : Dig 256)
  {Bd : Type} {W : QueryLayout 256 (typedOracleCarrier F.L Bd F.aT F.aL)}

/-- **What is left beside the entry file's check, at the input whose key is told a part.** -/
theorem armsLeft_told (b : BesideArmsCD (F.told encT c₀)) (hb : ∀ k, (b.rd k).NoCoin)
    (hF : F.Pub.NoCoin) {DK DP : Type}
    {ST : DK → OutOfDomainSampleQueryLayout 256 W.K F.L Bd F.aT F.aL} {cT : DK → F.L.OutOfDomainAnswer → List (Dig 256)}
    {VT : DK → OutTA 256 F.L F.aT → TypedOracleComputation 256 W.K (typedOracleCarrier F.L Bd F.aT F.aL) Bool}
    (hVT : ∀ d, IsArmT W (ST d) (cT d) (VT d))
    (mT : DK → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier F.L Bd F.aT F.aL)) 256) {PubK : OComp (rom 256) DK}
    (hPK : PubK.NoCoin) (hnK : ∀ d cm rc p, (F.vK d cm rc p).NoCoin)
    (hyK : ∀ (f : Fam (rom 256)) cm rc p, (F.vK (F.Pub.det f) cm rc p).det f = true →
      (armKOf VT mT PubK cm rc p).det f = true)
    (wK : ∀ (f : Fam (rom 256)) k tr cm,
      wordL mT (PubK.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {εk : ℕ → ℕ → ℝ≥0∞}
    (bK : ZKCP.Gen.ArmBoundD (fun _ => PubK) (armTestOf (X' := F.X) (aL := F.aL) VT mT PubK)
      (holdsTestOf (W := W) mT) εk) (hεK : ∀ tC tP, εk tC tP ≤ b.εK tC tP)
    {SB : DP → OutOfDomainSampleQueryLayout 256 W.K F.L Bd F.aT F.aL} {cB : DP → F.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : F.L.Rec}
    {VB : DP → OutBA 256 F.L → TypedOracleComputation 256 W.K (typedOracleCarrier F.L Bd F.aT F.aL) Bool}
    (hVB : ∀ d, IsArmB W (SB d) (cB d) r₀ (VB d))
    (mB : DP → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier F.L Bd F.aT F.aL)) 256) {PubP : OComp (rom 256) DP}
    (hPP : PubP.NoCoin) (hnP : ∀ d cm x rc n p, (F.vP d cm x rc n p).NoCoin)
    (hyP : ∀ (f : Fam (rom 256)) cm x rc n p, (F.vP (F.Pub.det f) cm x rc n p).det f = true →
      (PubP.bind fun d => (VB d (cm, x, rc, p)).overOne (mB d)).det f = true)
    (wP : ∀ (f : Fam (rom 256)) k tr cm,
      wordL mB (PubP.det f) tr cm = b.wordOf ((b.rd k).det f) tr cm)
    {εp : ℕ → ℕ → ℝ≥0∞}
    (bP : ZKCP.Gen.ArmBoundD (fun _ : Dig 256 × KeyRoot 256 F.L => PubP)
      (armSessOf (aT := F.aT) (aL := F.aL) VB mB PubP) (holdsSessOf (W := W) b.Rno mB) εp)
    (hεP : ∀ tC tP, εp tC tP ≤ b.εP tC tP) : ArmsLeft b :=
  armsLeft_of_bounds (r := F.told encT c₀) (W := W) b hb hVT mT hPK
    (fun c cm rc p => noCoin_told hF F.part (fun d => hnK d cm rc p) c)
    (fun f c cm rc p h => hyK f cm rc p (yes_told F.Pub F.part (fun d => F.vK d cm rc p) c f h))
    wK bK hεK hVB mB hPP
    (fun c cm x rc n p => noCoin_told hF F.part (fun d => hnP d cm x rc n p) c)
    (fun f c cm x rc n p h =>
      hyP f cm x rc n p (yes_told F.Pub F.part (fun d => F.vP d cm x rc n p) c f h))
    wP bP hεP

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.armsLeft_told
