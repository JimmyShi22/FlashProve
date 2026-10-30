-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/ToldMember.lean: a value of the type `LayoutsByPublicReading` at which the six added premises are
  theorems. CONDITIONAL: it is not yet a member of the premises of `innerCompiledVerifier_sound_byPublicReading`
  (Johnson/Top/InnerCompiledVerifierByPublicReading.lean): "each" is shown at no letters.

At the frame at the full size, general in both files' rounds' data and both decisions. It is the
  slot into which data and decisions go.
  R := `innerCompilerInputWithFixedLinkAtFullSize T₀` (Johnson/Flat/TwoSizesAt.lean).
  D := `D8`: the configuration's digest and the list of the seven chains' parameters' digests
    (Johnson/Top/PreThreePub.lean).
  Pub := `pub8 recordGround pol KL lay`: the public algorithm of that file.
  Pt := `IsCall169` (OnBytes/Slice/WalkOff.lean): every call under 169: wider than the reading's own
    strings, so "spare" is shown of more than is asked.
  part d := `cfg8 d`: the configuration's digest.
  m d := `mFamilyFull` at c := the bytes of d.1, pdL := `ent8 d`, dK := `key8 d`, dP := `prf8 d`
    (Johnson/PV/FamilyFull.lean).
  Sd d := T₀'s own record's wire with t, cfg, shape, pl0, pl1 laid from d; num, the seed's map and
    the test of equality are T₀'s.
  cA d := `codeA`. encT := `encId` at this object (Johnson/TypedOracleCompiler/Top/IdSeedAt.lean). The honest side:
    letters of which nothing is asked.
Of T₀: t, cfg, shape, pl0, pl1, m, enc are overwritten at every d or idle; ISK, commit, prove, π₀
  ride unread; ext, εId, x₀ are read by nothing at `sound_toldOf`.
What is had: the six premises that the told statement adds can be met together, as theorems, at a
  family whose reading asks the hash function (`pub8`), whose coding at d lays all eight digests of
  d where the format's strings hold them, whose record's wire holds the configuration's digest and
  whose code of a key is the string of the commitment ID: at the full size, at every rounds' data
  that pass two tests and at every two decisions. So the six clash neither with one another nor with
  a coding of the format's make.
Limits: the sixteen hypotheses at every d are shown at no letters; at the one member of the letters'
  type that is written elsewhere the builder returns nothing, so that the verifier refuses every
  proof and the conclusion holds there without the statement. Not touched: that the compiled
  verifier's own queries pass the coding's tests of fitness at this value; that the data DK, DP and
  the records belong to the three public files that the reading hashes. DK, DP name no answer of the
  hash, by their types; runK, runP, rK, rP and T₀'s r₀, p, build, nextToken are letters. The entry's
  decision names `recordRead`, whose given data hold a typed digest (`recordCfg`); by reading, the
  decision takes the link's shape, the plan's rounds and samples and the codes, not that digest; no
  theorem says so. The run's values are no part of d: m d reads them off the typed query (a first
  query's salt, the joining round's and the seam's messages, a leaf's salt): here they count as sent
  by the prover, and no test of this make holds them against the hash. S: at an empty front set the
  proof file's first query is an escape. The second hash function: `par7` inside `pub8` calls
  `plannedAt`, which hashes with it at seven places as a fixed function of pol, KL, lay; and the
  front set's spelling sp is meant to hold that hash's item of the request: a fixed function inside
  T.m d. Where the planner refuses at c, d.2 has one entry and `key8`, `prf8` fall back on d.1: the
  told verifier goes on at such a d, where the program's planner refuses.

-/
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.Top.PreThreePub
import Johnson.TypedOracleCompiler.Top.IdSeedAt
import Johnson.Flat.TwoSizesAt
import Johnson.PV.FamilyFull
import Johnson.PV.WordAll

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
      salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)

/-- The told code at this object (`encId`, Johnson/TypedOracleCompiler/Top/IdSeedAt.lean). -/
def encTOf : Dig 256 × KeyRoot 256 (innerCompilerInputWithFixedLinkAtFullSize T₀).protocol → Option ZKCP.Str :=
  encId recordGround (restOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P)

/-- **«code» at it.** -/
theorem code_encTOf : ZKCP.CodeIsOneToOne (encTOf T₀) :=
  encId_oneToOne recordGround (restOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt
      P)

/- so that Lean compares the name and does not unfold the code (unfolded, it did not decide «(toldOf
U).encT is encTOf T₀» within 200,000 heartbeats) -/
attribute [irreducible] encTOf

/-- What stays a letter beside T₀; three fields are hypotheses (hDK, hDP, hK), and S holds three
laws. -/
structure ToldLetters (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)
    where
  pol : ByteArray
  KL : ByteArray
  lay : ByteArray
  h₀ : HId
  k : OnBytes.Params.KeyChains
  c' : OnBytes.Params.ProofChains
  sp : X → ByteArray × ByteArray
  /-- the front set, AT innerCompiledVerifier's OWN FIXED RECORD T₀.r₀: the record that xinBA lays into the
  proof file's first query -/
  S : FrontSet ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers P) sp
      T₀.r₀
  sR : ℕ
  /-- an interface of which the code of leaves reads no field -/
  L0 : _root_.Iop.BatchProtocol Unit Unit
  back : ByteArray → StrCode (AllPts 256 (K + 1) (carW4 A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP
      depthReq early salt P))
  hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true
  hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true
  hK : K + 1 + 1 < 2 ^ 49
  ISK : Type
  commit : (innerCompilerInputWithFixedLinkAtFullSize T₀).Index → Rom.OComp (rom 256) ((Dig 256 × KeyRoot 256 (innerCompilerInputWithFixedLinkAtFullSize
                                     T₀).protocol) × ISK)
  prove : ISK → (l : List ((innerCompilerInputWithFixedLinkAtFullSize T₀).Instance × Unit)) → Rom.OComp (rom 256)
    (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (innerCompilerInputWithFixedLinkAtFullSize T₀).protocol (innerCompilerInputWithFixedLinkAtFullSize T₀).offlineRoundSplits (innerCompilerInputWithFixedLinkAtFullSize
                                                                                                    T₀).linkRoundSplits) l)
  π₀ : (Dig 256 × KeyRoot 256 (innerCompilerInputWithFixedLinkAtFullSize T₀).protocol) ×
    OfflineLinkOnlineProof 256 (innerCompilerInputWithFixedLinkAtFullSize T₀).protocol (innerCompilerInputWithFixedLinkAtFullSize T₀).offlineRoundSplits (innerCompilerInputWithFixedLinkAtFullSize T₀).linkRoundSplits

variable {T₀} (U : ToldLetters T₀)

/-- Three digests as bytes. -/
def pd3Of (a b c : Dig 256) : Pd3 := ⟨digToBytes a, digToBytes b, digToBytes c⟩

/-- THE ONE CODING AT d. -/
def mTold (d : D8) : OracleCoding (typedOracleFamily 256 (K + 1) (carW4 A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq
                         early salt P)) 256 :=
  mFamilyFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P U.h₀ U.k U.c' U.S U.sR U.L0
    U.hDK U.hDP U.hK U.back (digToBytes d.1) (size_digToBytes d.1) (ent8 d)
    (pd3Of (key8 d).1 (key8 d).2.1 (key8 d).2.2) (pd3Of (prf8 d).first (prf8 d).shared (prf8
        d).second)

/-- **THE VALUE.** -/
def toldOf : LayoutsByPublicReading (innerCompilerInputWithFixedLinkAtFullSize T₀) where
  D := D8
  Pub := pub8 recordGround U.pol U.KL U.lay
  Pt := OnBytes.Slice.IsCall169
  part := cfg8
  Sd := fun d => outOfDomainSampleQueryLayoutOfCode ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers
                                   P) (List Bool) _ _ (v := frS.P.v) (lg := 29) (s := 1) .test
    (TypedOracleCompiler.Run.SeedVals.cfgL (digToBytes d.1)) pubShapeTopFull (p0OfFull A (relationsAndEncodingOfClaims A E) DK DP
                runK runP rK rP depthReq early salt P)
    (p0OfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P) T₀.num (recSeedK recT
                              recLg recS T₀.W.K T₀.hK) id seedEqFull
  cA := fun _ => codeA (v := frS.P.v) (s := 1)
  m := mTold U
  encT := encTOf T₀
  ISK := U.ISK
  commit := U.commit
  prove := U.prove
  π₀ := U.π₀

/-! ## The six added premises -/

theorem told_noCoin : (toldOf U).Pub.NoCoin := pub8_noCoin _ _ _ _

theorem told_asks : (toldOf U).Pub.AsksIn fun _ s => (toldOf U).Pt s := pub8_asks169 _ _ _ _

theorem told_once : NoRepeat (toldOf U).Pub := pub8_noRepeat _ _ _ _

/-- **«spare».** -/
theorem told_spare : ∀ d s, (toldOf U).Pt s → IsOther ((toldOf U).m d) s := by
  rintro d s ⟨half, t, i, st, bs, hh, hs, rfl⟩
  show ((mTold U d).dec _).1 = TypedOracleCompiler.Compile.Batch.OracleName.other
  unfold mTold mFamilyFull mOfFull mOne
  exact mAll_isOther _ _ _ _ (mAll_call _ _ _ 169 (by decide) half hh t i st bs hs 0)

/-- **«word».** -/
theorem told_word : ∀ d d', (toldOf U).part d = (toldOf U).part d' →
    (extractorOverOneHashFunction ((toldOf U).m d) (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputWithFixedLinkAtFullSize T₀).queryLayout)).Ei =
      (extractorOverOneHashFunction ((toldOf U).m d') (indexExtractorAtRootAndOutOfDomainSample (innerCompilerInputWithFixedLinkAtFullSize T₀).queryLayout)).Ei := by
  rintro ⟨c, l⟩ ⟨c₁, l₁⟩ (h : c = c₁)
  subst h
  show (extractorOverOneHashFunction (mTold U (c, l)) (indexExtractorAtRootAndOutOfDomainSample T₀.W)).Ei = (extractorOverOneHashFunction (mTold U (c, l₁)) (indexExtractorAtRootAndOutOfDomainSample
                                                                               T₀.W)).Ei
  unfold mTold mFamilyFull mOfFull mOne
  exact word_mAll T₀.W _ _ _ _ _ rfl rfl

/-- **«code».** -/
theorem told_code : ZKCP.CodeIsOneToOne (toldOf U).encT := code_encTOf T₀

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.told_code
#print axioms VerifiableInference.OnPublicFiles.toldOf
#print axioms VerifiableInference.OnPublicFiles.told_noCoin
#print axioms VerifiableInference.OnPublicFiles.told_asks
#print axioms VerifiableInference.OnPublicFiles.told_once
#print axioms VerifiableInference.OnPublicFiles.told_spare
#print axioms VerifiableInference.OnPublicFiles.told_word
