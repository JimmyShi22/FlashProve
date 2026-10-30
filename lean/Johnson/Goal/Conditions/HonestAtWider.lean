-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestAtWider.lean: **THE HONEST SIDE's QUERIES ARE WITHIN honestBudget**
(HonestWithin, Ladder.lean: one of the conjuncts of G3'pol), AT EVERY MEMBER OF theWider
(Johnson/Goal/Conditions/WiderAtThe.lean), from bounds on the member's own sampler and prover and
one test on numbers; then at theHome (Johnson/Goal/Conditions/WiderHome.lean). A theorem about the
goals' own definition at a member. This file states no goal.

Main names.
  honestWithin_theWider   at K, W, o, Z: from: the public files are read · K.sample asks at most qS
    times · K.prove at most qP times, at all weights, randomness and requests · qS + (2 + count₀ Z)
    + qP + 7 + 1 ≤ honestBudget.
  readMore_wider_within, parse_wider_within, tCommit_wider, commit_wider_within,
    sample_wider_within, prove_wider_within   the five parts, each by a theorem of the library or by
    unfolding, behind names that Lean is told not to unfold.
  honestWithin_theHome    at theHome Rand ρOf pf ra sb: the sampler asks nothing; from: the prover's
    program pf asks at most qP times at each number that is drawn.

What pays what. 2 + count₀ Z: the committer: commitCount_withTerms
(Johnson/Goal/Conditions/BindsOwn.lean) at bindLaws_wider: two queries of the coins' algorithm; the
public reading's eight, two for each leaf of the tree, the seed's two typed queries of K + 1 digests
each, one for the key's code (count₀, Johnson/Goal/Conditions/BindsPlain.lean). 7: the further
reading (queryBound_readMoreAt, Johnson/Goal/Conditions/WithinAtThe.lean). 1: the parser
(descriptionOfDataOnBytes_within, Johnson/Goal/Tie/DescriptionOfData.lean).

Limits. qP IS A LETTER AND ITS BOUND A PREMISE: no prover is named here (for the program proveForm
by the first-block exit: queryBound_proveForm, Johnson/Prover/Home/CountF.lean). THE TEST ON NUMBERS
IS A PREMISE: no numeral stands here. Not counted, as in the goals' own text: the one query of
readConfig and the queries of innerCompiledVerifier. NO COMPLETENESS: that the verifier says yes is not spoken
of. WiderAtThe.lean's limits travel whole: flashProveData's decisions and data.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderHome
import Johnson.Goal.Conditions.BindsOwn
import Johnson.Goal.Conditions.WithinAtThe
import Rom.OneOfCount

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (K : TheCoins) (W : WiderCoins K) (o : SecondHashFunctionType) (Z : PublicFiles)

/- The member's text. -/
set_option quotPrecheck false in
local notation "DW" => (flashProveDescription.reBound W.bound).withTerms (theWiderTerms K W)

section
/- Lean compares these names and does not unfold them. (descriptionOfDataOnBytes is left open here: its form, its
further reading and its parser are read off its text.) -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding
  theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers
  theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem

/-- The further reading of a member: at most seven queries. -/
theorem readMore_wider_within (c : Digest) : ((DW).readMore Z c).toRandomized.QueryBound 7 :=
  queryBound_readMoreAt recordGround Z c

/-- The parser of a member: at most one. -/
theorem parse_wider_within : Parser.Within ((DW).parse Z) 1 := descriptionOfDataOnBytes_within flashProveData Z

/-- The sampler of a member is K's. -/
theorem sample_wider_within (qS : ℕ) (hS : K.sample.QueryBound qS) : (DW).sample.QueryBound qS :=
  hS

/-- The prover of a member is K's. -/
theorem prove_wider_within (s : IntegerTransformer.Settings) (qP : ℕ)
    (hP : ∀ w ρ p t, (K.prove Z s w ρ p t).QueryBound qP) :
    ∀ (w : ModelWeights s) (ρ : (DW).Rand) (p t : List Token),
      ((DW).prove Z s w ρ p t).QueryBound qP := hP

end

section
/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem
  descriptionOfDataOnBytes

/-- The committer's count at a member is the written committer's. -/
theorem tCommit_wider : (theWiderTerms K W).tCommit Z 8 + 1 = count₀ Z := rfl

set_option maxHeartbeats 1600000 in
/-- The committer of a member, at the count of the honest side's terms. -/
theorem commit_wider_raw (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (ρ : (theWiderTerms K W).Rand) :
    ((DW).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound
      (2 + ((theWiderTerms K W).tCommit Z 8 + 1)) :=
  commitCount_withTerms (bindLaws_wider K W Z pp hr) w ρ

set_option maxHeartbeats 1600000 in
/-- The committer of a member: the coins' two queries, and the written committer's count. -/
theorem commit_wider_within (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (ρ : (theWiderTerms K W).Rand) :
    ((DW).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound (2 + count₀ Z) := by
  have h := commit_wider_raw K W Z pp hr w ρ
  rw [tCommit_wider] at h
  exact h

end

section
/- Lean compares these by their names. -/
attribute [local irreducible] count₀ descriptionOfDataOnBytes theWiderTerms

set_option maxHeartbeats 1600000 in
/-- HonestWithin at the member's text. -/
theorem honestWithin_text (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (qS qP : ℕ)
    (hS : K.sample.QueryBound qS)
    (hP : ∀ w ρ p t, (K.prove Z (settingsOfRead pp) w ρ p t).QueryBound qP)
    (number : qS + (2 + count₀ Z) + qP + 7 + 1 ≤ honestBudget) :
    HonestWithin (DW) Z (settingsOfRead pp) :=
  ⟨qS, 2 + count₀ Z, qP, 7, 1, number, sample_wider_within K W qS hS,
    commit_wider_within K W Z pp hr, prove_wider_within K W Z _ qP hP,
    readMore_wider_within K W Z, parse_wider_within K W Z⟩

end

/-- **HonestWithin at every member of theWider.** -/
theorem honestWithin_theWider (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (qS qP : ℕ)
    (hS : K.sample.QueryBound qS)
    (hP : ∀ w ρ p t, (K.prove Z (settingsOfRead pp) w ρ p t).QueryBound qP)
    (number : qS + (2 + count₀ Z) + qP + 7 + 1 ≤ honestBudget) :
    HonestWithin (theWider K W o) Z (settingsOfRead pp) :=
  honestWithin_text K W Z pp hr qS qP hS hP number

section Home
variable {B N : ℕ} (Rand : Type) (ρOf : Fin (B + 1) → Rand)
  (pf : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → Fin (N + 1) → Rom.OComp (rom 256) FormBytes)
  (ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)) (sb : Rand → ℕ → ByteArray)

/-- **HonestWithin at theHome.** -/
theorem honestWithin_theHome (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (qP : ℕ)
    (hP : ∀ w ρ p t a, (pf Z (settingsOfRead pp) w ρ p t a).QueryBound qP)
    (number : 0 + (2 + count₀ Z) + qP + 7 + 1 ≤ honestBudget) :
    HonestWithin (atSecondHashFunction (theHome Rand ρOf pf ra sb)) Z (settingsOfRead pp) :=
  honestWithin_theWider (homeCoins Rand ρOf pf).digits (named_digits (homeCoins Rand ρOf pf) ra sb)
    _ Z pp hr 0 qP (fun _ => trivial)
    (fun w ρ p t a => queryBound_deterministicOf _ qP (queryBound_ofRom _ qP (hP w ρ p t a)))
    number

end Home

end FlashProve

#print axioms FlashProve.readMore_wider_within
#print axioms FlashProve.parse_wider_within
#print axioms FlashProve.tCommit_wider
#print axioms FlashProve.commit_wider_raw
#print axioms FlashProve.commit_wider_within
#print axioms FlashProve.sample_wider_within
#print axioms FlashProve.prove_wider_within
#print axioms FlashProve.honestWithin_text
#print axioms FlashProve.honestWithin_theWider
#print axioms FlashProve.honestWithin_theHome
