-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/LinkLaidTold.lean

Summary. E2E/LinkLaidPrivacy.lean is stated at homeR b Z: the parameters with an all-zero digest of
the public files and an empty second public reading. This file proves four of its results
(premW_laid, linkLaidWithBound, linkLaidStrings, linkLaidAtOnce) with the OOD phase's compilation
data and the code of the OOD answers taken at an arbitrary fixed value d of the two public readings:
d.1 is the digest, d.2 the second reading. All else is unchanged and is typed at homeR b Z: the
wiring, the salt lengths, the three provers (laidAt: one explicit link prover and two placeholders
that send fixed messages), the three simulators and the numbers. The family in d is the told record
homeT b Z (Johnson/Goal/Conditions/HomeAtWider.lean); its parameters at d, (homeT b Z).at d, are
those of the built description at the digest d.1 and the second reading d.2 (at_home).

What depends on d, and what does not.
- Of what the statements read, only (homeT b Z).Sd d depends on d, and only in its field cfg, which
  is [d.1]: (homeT b Z).Sd d is (homeR b Z).seedQueries with cfg set to [d.1] (seed_reads_digest here;
  seed_is, E2E/LinkLaidToldAsks.lean). The code of the answers is the same at every d (code_told).
- PremW and zetaW do not read cfg (premW_cfg and zetaW_cfg, E2E/LinkLaidToldAsks.lean; zetaW reads
  of these data the tag alone: zetaW_tag, here). So premW_laid_told says of the twenty premises no
  more than premW_laid does: it follows from it (premW_laid_told_again, E2E/LinkLaidToldAsks.lean).
  zeta_told holds for the same plain reason. They are stated for their type: one structure of
  provers, typed at one value of the parameters, at every d.
- The digest occurs in the text of the committer, the verifier and the simulator of the conclusions
  (EndAt, AtOnceAt, the scheme's own run): the first query of a table's OOD seed holds cfg
  (told_seed_query, E2E/LinkLaidToldAsks.lean, whose head says what of this is by definition only).
- The second reading d.2 is not read by Sd (seed_reading), nor by EndAt and AtOnceAt (endAt_reading,
  atOnceAt_reading); it occurs in the coding of the typed oracles into one hash function, the field
  m of the parameters at d.

The main limit. d is fixed before the oracles are drawn. VerifierAndGoals.verify takes no digest: it asks the
hash function for d.1 at the public files' string, and for d.2 at strings made from d.1. So in
verify's use d consists of answers of the same hash function into which the typed oracles are
coded. No statement here covers that: here the oracles are independent of d.

Theorems, for every d : (homeT b Z).D. Premises and bounds are those of the statements of
E2E/LinkLaidPrivacy.lean.
  premW_laid_told        the twenty premises (PremW) of wholeKeyPrivacy, at (homeT b Z).Sd d and
                         (homeT b Z).cA d, for laidAt.
  zeta_told              zetaW at (homeT b Z).Sd d is zetaW at (homeR b Z).seedQueries.
  zeta_laid_told         so its bound boundZ (9 + CT + CL + CB) M t n, for n ≤ s1.
  linkLaidWithBound_told EndAt (E2E/LinkLaidPrivacy.lean) at (homeT b Z).at d: the conclusion of
                         wholeKeyPrivacy with the bound on its error.
  linkLaidStrings_told   with at least 2 ^ 40 tries in every search the proofs are produced, except
                         with probability at most (M + 2) · 71 · 2 ^ -256.
  linkLaidAtOnce_told    AtOnceAt (E2E/LinkLaidPrivacy.lean) at (homeT b Z).at d: both, for one
                         copy, ℓ := 320 and every search limit 2 ^ 40, with the number 2 ^ -135.

Limits.
- premW_laid_told has no lower bounds: ℓ = 0 free bits, search limits 0 and s1 = 0 are admitted.
  What the conclusion of wholeKeyPrivacy is worth at such values is not stated here. The premises
  of zeta_laid_told and linkLaidWithBound_told bound the search limits from above only, and boundZ
  is given no number there. In this file the number 2 ^ -135, with search limits at which proofs
  are produced, is in linkLaidAtOnce_told alone (it is also in linkLaidEight_told,
  E2E/LinkLaidEightTold.lean).
- All limits of E2E/LinkLaidPrivacy.lean hold but the one on the all-zero digest and the empty
  second reading, which becomes the main limit above. Among them: two of the three provers are
  placeholders; nothing says that any verifier accepts; there is no negative test at these
  parameters.
- laidAt's tables' leaf salts begin with sMT - ℓ zeros at every d. The library's own prover program
  over homeT b Z (pfOf, Johnson/Goal/Conditions/HomeAtWider.lean) starts them with the bytes of the
  digest that was read (saltsAt, Johnson/Goal/Conditions/WiderSalts.lean).
- laid_rounds (E2E/LinkLaidRounds.lean) also reads the digest, through seedQueries. It is not carried here:
  its statement LinkRoundsAt is typed at homeR b Z.
- It is stated at flashProveDescription, the value that the library builds. VerifierAndGoals.theDescription_eq
  (Johnson/Goal/Description/Description.lean) says that the description of the top-level
  statements, read at atSecondHashFunction, is that value; no statement here is carried along that equation.
- What these statements are worth as statements on hiding is not settled here.

Tests and notes.
- Two digests give two values of Sd (seed_injective). That is a statement on the term Sd d, not on
  PremW, zetaW or the scheme.
- The statements of E2E/LinkLaidPrivacy.lean are the case d := (allZeroDigest, []): seed_zeros, endAt_zeros,
  atOnceAt_zeros, run_zeros. withBound_again, strings_again and atOnce_again prove
  linkLaidWithBound, linkLaidStrings and linkLaidAtOnce anew from the theorems here; their proofs do
  not call these three.
- The value of the record's public reading at a hash function is (cAt Z hash, sevenAt Z hash)
  (FlashProve.pub_det_home, Johnson/Prover/At/HomeAt.lean). That this is the pair at which
  VerifierAndGoals.verify calls the compiled verifier is FlashProve.verify_evaluate
  (Johnson/Goal/Tie/VerifyEval.lean) with FlashProve.mAt_descriptionOfFields
  (Johnson/Goal/Tie/DescribeT.lean).
- The premises name no d, so what meets them reads no d: bitsE_listed, bd_home, sMT_home
  (E2E/LinkLaidPrivacy.lean), index_home (here), instance_home (E2E/LinkLaidAllAtOnce.lean).
- salts_any: the field compilerParameters (the salt lengths among it) of the built description's parameters is that
  of homeR b Z at every digest and second reading. For the wiring no such equation is stated: its
  type depends on the parameters.

Terms: E2E/HidingTerms.lean. Terms of this file. A told record (LayoutsByPublicReading,
Johnson/Top/InnerCompiledVerifierByPublicReading.lean): over parameters r, the fields of r that depend on the value d of
the two public readings, as functions of d; T.at d is r with these fields taken at d. The OOD
phase's compilation data: the field seedQueries (OutOfDomainSampleQueryLayout, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean): how a table's OOD
seed is made from two oracle answers. The code of the OOD answers: the field answerCode.

How it is proved. Section 1 is stated for arbitrary parameters r and an arbitrary told record T over
them; the later sections only apply it. So Lean never compares the built parameters at two digests
with each other: asked to, it does not finish within the default limits.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  twelve_at, tries_at: two statements on the parameters read neither seedQueries nor answerCode, so they hold at
    T.at d where they hold at r.
-/
import E2E.LinkLaidPrivacy
import Johnson.TypedOracleCompiler.Top.TieIdBytes

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid.Told
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.Shown
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference (Digest)
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open OnBytes.K.Arm.Pub (D8)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR homeT flashProveDescription allZeroDigest)

/-! ## 1. For an arbitrary told record: what reads neither seedQueries nor answerCode, and what reads them alone

Every lemma of this section is stated for arbitrary parameters r, an arbitrary told record T over
them and arbitrary values d of its public reading, so that Lean compares no two built parameters
with each other. -/

/-- Two values of the OOD phase's compilation data with one tag give one error. -/
theorem zetaW_tag {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S S' : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : S.t = S'.t) (p : _root_.Compile.Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd)
    (u : NumsW) : zetaW W S p a c u = zetaW W S' p a c u := by
  unfold zetaW eW
  rw [h]

section Letters
variable {r : InnerCompilerInput} (T : LayoutsByPublicReading r) (d : T.D)

/-- NoProverSide at the parameters at d, read in r's wiring and T's two fields at d. -/
theorem noProverSide_of_at {Gs : r.protocol.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ} {capT capL capB : ℕ → ℕ}
    (h : NoProverSide (T.at d).queryLayout (T.at d).seedQueries (T.at d).answerCode Gs N M capT capL capB) :
    NoProverSide r.queryLayout (T.Sd d) (T.cA d) Gs N M capT capL capB := h

/-- NoProverSide does not read the field coinBound. -/
theorem noProverSide_told_reBound (n : ℕ) {Gs : r.protocol.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ}
    {capT capL capB : ℕ → ℕ} (h : NoProverSide r.queryLayout (T.Sd d) (T.cA d) Gs N M capT capL capB) :
    NoProverSide (r.reBound n).queryLayout ((T.reBound n).Sd d) ((T.reBound n).cA d) Gs N M capT capL capB :=
  h

theorem twelve_at (h : Twelve r) : Twelve (T.at d) :=
  ⟨h.sMT, h.sFS, h.depth, h.lvT, h.lvL, h.lvB, h.rT, h.rL, h.rB, h.qT, h.qL, h.qB⟩

theorem tries_at (h : Tries r) : Tries (T.at d) := ⟨h.nT, h.nL, h.nB, h.bT, h.bL, h.bB⟩

/-- PremW for the placeholder provers, from its fifteen premises that name no prover. -/
theorem premW_fixed_at (b₀ : r.LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) (hℓ : ℓ ≤ r.compilerParameters.sMT)
    (Ryes : r.Index → r.Instance → Prop)
    (h0 : NoProverSide r.queryLayout (T.Sd d) (T.cA d) (fun _ => True) (indexPrivacyNumbers s1 0 0 0 0 0 0) M capT capL
      capB) :
    PremW r.queryLayout (T.Sd d) (T.cA d) r.compilerParameters (silentAtC r b₀ M ℓ ℓr capT capL capB) (fixedSims r.protocol)
      (fun _ => True) (fun _ => True) Ryes (coinNums r b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) :=
  have h5 := fiveLeft_fixed r b₀ M s1 ℓ ℓr capT capL capB hℓ (fun _ => True) Ryes
  (premW_iff r.queryLayout (T.Sd d) (T.cA d) r.compilerParameters (silentAtC r b₀ M ℓ ℓr capT capL capB) (fixedSims r.protocol)
    (fun _ => True) (fun _ => True) Ryes (coinNums r b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)).2
    ⟨h0, h5.ext, h5.runVals, h5.good, h5.stops, h5.coins⟩

variable {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol} {c : CoinNums r.LeafBody} {N : NumsW}
  {R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit} {i₀ : r.Index}

/-- endAt_of (E2E/LinkLaidPrivacy.lean) at the parameters at d. -/
theorem endAt_at {Ryes : r.Index → r.Instance → Prop} (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (h : PremW r.queryLayout (T.Sd d) (T.cA d) r.compilerParameters a Sm (fun _ => True) (fun _ => True) Ryes c N)
    (h12 : Twelve r) (s1 M CT CL CB : ℕ) (e1 : N.s1 = s1) (e2 : a.M = M)
    (hT : ∀ i, a.capT i ≤ CT) (hL : ∀ i, a.capL i ≤ CL) (hB : ∀ i, a.capB i ≤ CB)
    (hz : N.zT = 0 ∧ N.zL = 0 ∧ N.zO = 0 ∧ N.hT = 0 ∧ N.hL = 0 ∧ N.hO = 0 ∧ N.δ = 0)
    (hℓ : 256 ≤ c.ℓ) : EndAt (T.at d) a Sm c N R i₀ s1 (9 + CT + CL + CB) M :=
  endAt_of (T.at d) R i₀ hR h (twelve_at T d h12) s1 M CT CL CB e1 e2 hT hL hB hz hℓ

/-- full_side (E2E/LinkLaidPrivacy.lean) at the parameters at d. -/
theorem full_at (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (ht : Tries r)
    (hL : LawFit r.queryLayout (T.Sd d) h.capT h.capL h.capB) (hW : WiresFit r.queryLayout (T.cA d))
    (hs : NeverStops h.st) (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1) (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1)
    (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (runOf (T.at d) h i x) {y | ¬ FullTo (h.M + 1) y} ≤
      ((h.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  full_side (T.at d) h (tries_at T d ht) hL hW hs h1 h2 h3 i x

/-- atOnceAt_of (E2E/LinkLaidPrivacy.lean) at the parameters at d. -/
theorem atOnceAt_at {s1 : ℕ}
    (hE : EndAt (T.at d) a Sm c N R i₀ s1 (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (h1 : 1 ≤ s1)
    (ht : Tries r) (hL : LawFit r.queryLayout (T.Sd d) a.side.capT a.side.capL a.side.capB)
    (hW : WiresFit r.queryLayout (T.cA d)) (hs : NeverStops a.side.st)
    (c1 : ∀ i, 2 ^ 40 ≤ a.side.capT i + 1) (c2 : ∀ i, 2 ^ 40 ≤ a.side.capL i + 1)
    (c3 : ∀ i, 2 ^ 40 ≤ a.side.capB i + 1) : AtOnceAt (T.at d) a Sm c N R i₀ s1 :=
  atOnceAt_of (T.at d) hE h1 (tries_at T d ht) hL hW hs c1 c2 c3

/-- **EndAt reads of d only T.Sd d and T.cA d.** -/
theorem endAt_move (d' : T.D) (hS : T.Sd d = T.Sd d') (hc : T.cA d = T.cA d') (s1 k M : ℕ) :
    EndAt (T.at d) a Sm c N R i₀ s1 k M ↔ EndAt (T.at d') a Sm c N R i₀ s1 k M := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = T.Sd d' → cA' = T.cA d' →
      (EndAt { r with seedQueries := S, answerCode := cA' } a Sm c N R i₀ s1 k M ↔
        EndAt (T.at d') a Sm c N R i₀ s1 k M) := by
    rintro _ _ rfl rfl
    exact Iff.rfl
  exact key _ _ hS hc

/-- Where T.Sd d and T.cA d are r's own, EndAt at the parameters at d is EndAt at r. -/
theorem endAt_home (hS : T.Sd d = r.seedQueries) (hc : T.cA d = r.answerCode) (s1 k M : ℕ) :
    EndAt (T.at d) a Sm c N R i₀ s1 k M ↔ EndAt r a Sm c N R i₀ s1 k M := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = r.seedQueries → cA' = r.answerCode →
      (EndAt { r with seedQueries := S, answerCode := cA' } a Sm c N R i₀ s1 k M ↔
        EndAt r a Sm c N R i₀ s1 k M) := by
    rintro _ _ rfl rfl
    exact Iff.rfl
  exact key _ _ hS hc

/-- **AtOnceAt reads of d only T.Sd d and T.cA d.** -/
theorem atOnceAt_move (d' : T.D) (hS : T.Sd d = T.Sd d') (hc : T.cA d = T.cA d') (s1 : ℕ) :
    AtOnceAt (T.at d) a Sm c N R i₀ s1 ↔ AtOnceAt (T.at d') a Sm c N R i₀ s1 := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = T.Sd d' → cA' = T.cA d' →
      (AtOnceAt { r with seedQueries := S, answerCode := cA' } a Sm c N R i₀ s1 ↔
        AtOnceAt (T.at d') a Sm c N R i₀ s1) := by
    rintro _ _ rfl rfl
    exact Iff.rfl
  exact key _ _ hS hc

/-- Where T.Sd d and T.cA d are r's own, AtOnceAt at the parameters at d is AtOnceAt at r. -/
theorem atOnceAt_home (hS : T.Sd d = r.seedQueries) (hc : T.cA d = r.answerCode) (s1 : ℕ) :
    AtOnceAt (T.at d) a Sm c N R i₀ s1 ↔ AtOnceAt r a Sm c N R i₀ s1 := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = r.seedQueries → cA' = r.answerCode →
      (AtOnceAt { r with seedQueries := S, answerCode := cA' } a Sm c N R i₀ s1 ↔
        AtOnceAt r a Sm c N R i₀ s1) := by
    rintro _ _ rfl rfl
    exact Iff.rfl
  exact key _ _ hS hc

/-- Where T.Sd d and T.cA d are r's own, the scheme's own run at the parameters at d is that at
r. -/
theorem runOf_home (hS : T.Sd d = r.seedQueries) (hc : T.cA d = r.answerCode)
    (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (i : r.Index) (x : r.Instance) :
    runOf (T.at d) h i x = runOf r h i x := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = r.seedQueries → cA' = r.answerCode → runOf { r with seedQueries := S, answerCode := cA' } h i x = runOf r h i x := by
    rintro _ _ rfl rfl
    rfl
  exact key _ _ hS hc

end Letters

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows _root_.Run.digToBytes

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-! ## 2. The told record homeT b Z at a value of the two public readings -/

/-- **The parameters at d are those of the built description at the digest d.1 and the second public
reading d.2**, with the field coinBound set to b Z. -/
theorem at_home (d : D8) : (homeT b Z).at d = (flashProveDescription.reBound b).input Z d.1 d.2 :=
  congrArg (fun r : InnerCompilerInput => r.reBound (b Z))
    ((FlashProve.dataAtFiles flashProveData Z).at_layoutsByPublicReading allZeroDigest [] d)

/-- **The OOD phase's compilation data read the digest**: their field cfg, the digests of a table's
name behind the root, is the list of d.1 alone. -/
theorem seed_reads_digest (d : D8) : ((homeT b Z).Sd d).cfg = [d.1] := by
  show PV.MFull.cfgF (_root_.Run.digToBytes d.1) = [d.1]
  unfold PV.MFull.cfgF TypedOracleCompiler.Run.SeedVals.cfgL
  rw [OnBytes.K.Arm.bytesToDig_digToBytes]

/-- Two digests give two values of the OOD phase's compilation data. -/
theorem seed_injective (d d' : D8) (h : (homeT b Z).Sd d = (homeT b Z).Sd d') : d.1 = d'.1 :=
  (List.cons.inj ((seed_reads_digest b Z d).symm.trans
    ((congrArg (fun S => S.cfg) h).trans (seed_reads_digest b Z d')))).1

/-- The OOD phase's compilation data do not read the second public reading. -/
theorem seed_reading (c : Digest) (m : List (Dig 256)) :
    (homeT b Z).Sd (c, m) = (homeT b Z).Sd (c, []) := rfl

/-- At the all-zero digest the OOD phase's compilation data are those of homeR b Z. -/
theorem seed_zeros : (homeT b Z).Sd (allZeroDigest, []) = (homeR b Z).seedQueries := rfl

/-- The tag of the OOD phase's compilation data is that of homeR b Z, at every d. -/
theorem tag_told (d : (homeT b Z).D) : ((homeT b Z).Sd d).t = (homeR b Z).seedQueries.t := rfl

/-- The code of the OOD answers is that of homeR b Z, at every d. -/
theorem code_told (d : (homeT b Z).D) : (homeT b Z).cA d = (homeR b Z).answerCode := rfl

/-- The field compilerParameters (the salt lengths among it) of the built description's parameters is that of
homeR b Z, at every digest and second public reading. -/
theorem salts_any (c : Digest) (m : List (Dig 256)) :
    ((flashProveDescription.reBound b).input Z c m).compilerParameters = (homeR b Z).compilerParameters :=
  (congrArg (fun r : InnerCompilerInput => r.compilerParameters) (at_home b Z (c, m))).symm

/-- The type of indices has a member. -/
theorem index_home : Nonempty (homeR b Z).Index := ⟨fun _ _ => 0⟩

/-- The fifteen premises of PremW that name no prover, at d: noProverSide_atFiles
(E2E/PremisesAtFiles.lean) at the digest d.1 and the second reading d.2, carried along the equation
of parameters DescriptionDataAtFiles.at_layoutsByPublicReading (Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
theorem noProverSide_told (d : D8) (scope : InScope Z = true) (M s1 : ℕ)
    (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞)
    (capT capL capB : ℕ → ℕ) :
    NoProverSide (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  noProverSide_told_reBound ((FlashProve.dataAtFiles flashProveData Z).layoutsByPublicReading allZeroDigest []) d (b Z)
    (noProverSide_of_at ((FlashProve.dataAtFiles flashProveData Z).layoutsByPublicReading allZeroDigest []) d
      (Eq.mpr
        (congrArg (fun r : InnerCompilerInput => NoProverSide r.queryLayout r.seedQueries r.answerCode (fun _ => True)
            (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB)
          ((FlashProve.dataAtFiles flashProveData Z).at_layoutsByPublicReading allZeroDigest [] d))
        (noProverSide_atFiles Z scope d.1 d.2 M s1 hM hs zT zL zO hT hL hO capT capL capB)))

/-! ## 3. PremW, and the error -/

section
variable (d : (homeT b Z).D) (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- **PremW holds for laidAt, at the OOD phase's compilation data and the code of the answers at
d.** One structure of provers and parameters for all d, typed at homeR b Z. PremW does not read the
field of Sd d that depends on d. There are no lower bounds: ℓ = 0, search limits 0 and s1 = 0 are
admitted. -/
theorem premW_laid_told (scope : InScope Z = true) (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127)
    (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK) (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol)) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  premW_withLaid b Z ((homeT b Z).Sd d) ((homeT b Z).cA d)
    (fixedAt b Z b₀ M ℓ ℓr capT capL capB) (fixedSims (homeR b Z).protocol) (fun _ => True)
    (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E
    (premW_fixed_at (homeT b Z) d b₀ M s1 ℓ ℓr capT capL capB hℓ Ryes
      (noProverSide_told b Z d scope M s1 hM hs 0 0 0 0 0 0 capT capL capB))
    trivial hE

/-- **The error is the same function at every d.** -/
theorem zeta_told (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (cn : CoinNums (homeR b Z).LeafBody) (N : NumsW) :
    zetaW (homeR b Z).queryLayout ((homeT b Z).Sd d) (homeR b Z).compilerParameters a cn N =
      zetaW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).compilerParameters a cn N :=
  zetaW_tag (homeR b Z).queryLayout ((homeT b Z).Sd d) (homeR b Z).seedQueries (tag_told b Z d) (homeR b Z).compilerParameters a cn N

/-- The bound on the error, at d. Its premises bound the search limits from above only, and boundZ
is given no number here. -/
theorem zeta_laid_told (scope : InScope Z = true) (CT CL CB : ℕ) (hℓ : 256 ≤ ℓ)
    (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL) (hB : ∀ i, capB i ≤ CB) (t n : ℕ)
    (hn : n ≤ s1) :
    zetaW (homeR b Z).queryLayout ((homeT b Z).Sd d) (homeR b Z).compilerParameters (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
      (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) t n ≤
      boundZ (9 + CT + CL + CB) M t n :=
  le_of_eq_of_le (congrFun (congrFun (zeta_told b Z d _ _ _) t) n)
    (zeta_laid b Z b₀ M s1 ℓ ℓr capT capL capB E scope CT CL CB hℓ hT hL hB t n hn)

/-! ## 4. The conclusion of wholeKeyPrivacy, with the bound -/

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope and every d**: EndAt at the parameters at d, for laidAt. -/
theorem linkLaidWithBound_told (scope : InScope Z = true) (CT CL CB : ℕ)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)
    (hE : E.OK) (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127) (hℓ : 256 ≤ ℓ)
    (hℓ' : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL)
    (hB : ∀ i, capB i ≤ CB) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    EndAt ((homeT b Z).at d) (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
      (fitSims (fixedSims (homeR b Z).protocol)) (coinNums (homeR b Z) b₀ ℓ ℓr)
      (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 (9 + CT + CL + CB) M :=
  endAt_at (homeT b Z) d hR
    (premW_laid_told b Z d b₀ M s1 ℓ ℓr capT capL capB E scope hM hs hℓ' hE Ryes)
    (twelve_home b Z scope) s1 M CT CL CB rfl rfl hT hL hB ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hℓ

/-! ## 5. The proofs are produced -/

/-- **For public files Z in scope and every d**: with at least 2 ^ 40 tries in every search, in the
scheme's own run at d the first table's proof, all M + 1 link proofs and the session's proof are
produced, except with probability at most (M + 2) · 71 · 2 ^ -256. -/
theorem linkLaidStrings_told (scope : InScope Z = true) (h1 : ∀ i, 2 ^ 40 ≤ capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ capB i + 1) (i : (homeR b Z).Index)
    (x : (homeR b Z).Instance) :
    PrFrom (Table.empty _)
      (runOf ((homeT b Z).at d) (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side i x)
      {y | ¬ FullTo (M + 1) y} ≤ ((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  full_at (homeT b Z) d (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side (tries_home b Z scope)
    (FlashProve.lawFit_home b Z d capT capL capB) (FlashProve.wiresFit_home b Z d)
    (neverStops_laid b Z b₀ M ℓ ℓr capT capL capB E) h1 h2 h3 i x

end

/-! ## 6. The bound with its number, and that the proofs are produced, for one choice of search
limits -/

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope with a live description and every d**: AtOnceAt at the parameters
at d, for laidAt with one copy, ℓ := 320 and every search limit 2 ^ 40. -/
theorem linkLaidAtOnce_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ)
    (E : BitsE b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)
    (hE : E.OK) (h1 : 1 ≤ s1) (h2 : s1 ≤ 688127) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    AtOnceAt ((homeT b Z).at d)
      (laidAt b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (fitSims (fixedSims (homeR b Z).protocol)) (coinNums (homeR b Z) b₀ 320 ℓr)
      (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 :=
  atOnceAt_at (homeT b Z) d
    (linkLaidWithBound_told b Z d b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
      (fun _ => 2 ^ 40) E scope (2 ^ 40) (2 ^ 40) (2 ^ 40) Ryes R i₀ hE (by norm_num) h2
      (by norm_num) (by rw [sMT_home b Z scope live]; norm_num) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) hR)
    h1 (tries_home b Z scope) (FlashProve.lawFit_home b Z d _ _ _)
    (FlashProve.wiresFit_home b Z d)
    (neverStops_laid b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
    (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

/-! ## 7. The statements of E2E/LinkLaidPrivacy.lean are the case of the all-zero digest and the
empty second reading; EndAt and AtOnceAt do not read the second reading -/

section
variable (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (Sm : Sims (homeR b Z).protocol) (cn : CoinNums (homeR b Z).LeafBody) (N : NumsW)
  (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)

/-- EndAt at the parameters at (allZeroDigest, []) is EndAt at homeR b Z. -/
theorem endAt_zeros (s1 k M : ℕ) :
    EndAt ((homeT b Z).at (allZeroDigest, [])) a Sm cn N R i₀ s1 k M ↔
      EndAt (homeR b Z) a Sm cn N R i₀ s1 k M :=
  endAt_home (homeT b Z) (allZeroDigest, []) (seed_zeros b Z) (code_told b Z _) s1 k M

/-- AtOnceAt at the parameters at (allZeroDigest, []) is AtOnceAt at homeR b Z. -/
theorem atOnceAt_zeros (s1 : ℕ) :
    AtOnceAt ((homeT b Z).at (allZeroDigest, [])) a Sm cn N R i₀ s1 ↔
      AtOnceAt (homeR b Z) a Sm cn N R i₀ s1 :=
  atOnceAt_home (homeT b Z) (allZeroDigest, []) (seed_zeros b Z) (code_told b Z _) s1

/-- The scheme's own run at the parameters at (allZeroDigest, []) is that at homeR b Z. -/
theorem run_zeros (i : (homeR b Z).Index) (x : (homeR b Z).Instance) :
    runOf ((homeT b Z).at (allZeroDigest, [])) a.side i x = runOf (homeR b Z) a.side i x :=
  runOf_home (homeT b Z) (allZeroDigest, []) (seed_zeros b Z) (code_told b Z _) a.side i x

/-- EndAt does not read the second public reading. -/
theorem endAt_reading (c : Digest) (m : List (Dig 256)) (s1 k M : ℕ) :
    EndAt ((homeT b Z).at (c, m)) a Sm cn N R i₀ s1 k M ↔
      EndAt ((homeT b Z).at (c, [])) a Sm cn N R i₀ s1 k M :=
  endAt_move (homeT b Z) (c, m) (c, []) (seed_reading b Z c m) rfl s1 k M

/-- AtOnceAt does not read the second public reading. -/
theorem atOnceAt_reading (c : Digest) (m : List (Dig 256)) (s1 : ℕ) :
    AtOnceAt ((homeT b Z).at (c, m)) a Sm cn N R i₀ s1 ↔
      AtOnceAt ((homeT b Z).at (c, [])) a Sm cn N R i₀ s1 :=
  atOnceAt_move (homeT b Z) (c, m) (c, []) (seed_reading b Z c m) rfl s1

end

/-- linkLaidWithBound (E2E/LinkLaidPrivacy.lean), from linkLaidWithBound_told at (allZeroDigest, []). -/
theorem withBound_again (scope : InScope Z = true) : LinkLaidWithBound b Z :=
  fun b₀ M s1 ℓ ℓr CT CL CB capT capL capB E Ryes R i₀ hE hM hs hℓ hℓ' hT hL hB hR =>
    (endAt_zeros b Z _ _ _ _ R i₀ s1 _ M).1
      (linkLaidWithBound_told b Z (allZeroDigest, []) b₀ M s1 ℓ ℓr capT capL capB E scope CT CL CB Ryes R
        i₀ hE hM hs hℓ hℓ' hT hL hB hR)

/-- linkLaidStrings (E2E/LinkLaidPrivacy.lean), from linkLaidStrings_told at (allZeroDigest, []). -/
theorem strings_again (scope : InScope Z = true) : LinkLaidStrings b Z :=
  fun capT capL capB h1 h2 h3 b₀ M ℓ ℓr E i x =>
    le_of_eq_of_le
      (congrArg (fun c => PrFrom (Table.empty _) c {y | ¬ FullTo (M + 1) y})
        (run_zeros b Z (laidAt b Z b₀ M ℓ ℓr capT capL capB E) i x).symm)
      (linkLaidStrings_told b Z (allZeroDigest, []) b₀ M ℓ ℓr capT capL capB E scope h1 h2 h3 i x)

/-- linkLaidAtOnce (E2E/LinkLaidPrivacy.lean), from linkLaidAtOnce_told at (allZeroDigest, []). -/
theorem atOnce_again (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LinkLaidAtOnce b Z :=
  fun b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR =>
    (atOnceAt_zeros b Z _ _ _ _ R i₀ s1).1
      (linkLaidAtOnce_told b Z (allZeroDigest, []) scope live b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR)

end AtPublicFiles.LinkLaid.Told

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.Told.zetaW_tag
#print axioms AtPublicFiles.LinkLaid.Told.noProverSide_of_at
#print axioms AtPublicFiles.LinkLaid.Told.noProverSide_told_reBound
#print axioms AtPublicFiles.LinkLaid.Told.twelve_at
#print axioms AtPublicFiles.LinkLaid.Told.tries_at
#print axioms AtPublicFiles.LinkLaid.Told.premW_fixed_at
#print axioms AtPublicFiles.LinkLaid.Told.endAt_at
#print axioms AtPublicFiles.LinkLaid.Told.full_at
#print axioms AtPublicFiles.LinkLaid.Told.atOnceAt_at
#print axioms AtPublicFiles.LinkLaid.Told.endAt_move
#print axioms AtPublicFiles.LinkLaid.Told.endAt_home
#print axioms AtPublicFiles.LinkLaid.Told.atOnceAt_move
#print axioms AtPublicFiles.LinkLaid.Told.atOnceAt_home
#print axioms AtPublicFiles.LinkLaid.Told.runOf_home
#print axioms AtPublicFiles.LinkLaid.Told.at_home
#print axioms AtPublicFiles.LinkLaid.Told.seed_reads_digest
#print axioms AtPublicFiles.LinkLaid.Told.seed_injective
#print axioms AtPublicFiles.LinkLaid.Told.seed_reading
#print axioms AtPublicFiles.LinkLaid.Told.seed_zeros
#print axioms AtPublicFiles.LinkLaid.Told.tag_told
#print axioms AtPublicFiles.LinkLaid.Told.code_told
#print axioms AtPublicFiles.LinkLaid.Told.salts_any
#print axioms AtPublicFiles.LinkLaid.Told.index_home
#print axioms AtPublicFiles.LinkLaid.Told.noProverSide_told
#print axioms AtPublicFiles.LinkLaid.Told.premW_laid_told
#print axioms AtPublicFiles.LinkLaid.Told.zeta_told
#print axioms AtPublicFiles.LinkLaid.Told.zeta_laid_told
#print axioms AtPublicFiles.LinkLaid.Told.linkLaidWithBound_told
#print axioms AtPublicFiles.LinkLaid.Told.linkLaidStrings_told
#print axioms AtPublicFiles.LinkLaid.Told.linkLaidAtOnce_told
#print axioms AtPublicFiles.LinkLaid.Told.endAt_zeros
#print axioms AtPublicFiles.LinkLaid.Told.atOnceAt_zeros
#print axioms AtPublicFiles.LinkLaid.Told.run_zeros
#print axioms AtPublicFiles.LinkLaid.Told.endAt_reading
#print axioms AtPublicFiles.LinkLaid.Told.atOnceAt_reading
#print axioms AtPublicFiles.LinkLaid.Told.withBound_again
#print axioms AtPublicFiles.LinkLaid.Told.strings_again
#print axioms AtPublicFiles.LinkLaid.Told.atOnce_again
