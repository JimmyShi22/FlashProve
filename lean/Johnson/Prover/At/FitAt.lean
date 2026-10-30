-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/FitAt.lean: at the input of the full size (`innerCompilerInputAtFullSize`,
Johnson/Flat/Dec/TwoSizesAt.lean) the two records of premises on wires, marks and caps under which
the runs of a whole request are spoken of: `WiresFit` (Johnson/Prover/All/Yes.lean) and `LawFit`
(Johnson/Prover/All/Law.lean). For all data of the three files, under tests on public numbers.

Main names.
  `NumbersFit K DK ds DP` (namespace `VerifiableInference.OnPublicFiles`)   the tests on public numbers,
      as one record: the six of `oka_fullD` (Johnson/Prover/At/LawsAt.lean), and: at most two trees
      in a round of each of the three files
  `offAt_of_depth` (namespace `OnBytes.Prover`)   for all wirings and all tags: if both plain parts
      of the seeds' queries are of round 0, no query of the committer or the seeds is a place that
      the chain's freshness asks to be empty
  `putsFree_wiresSL`, `putsApart_wqW` (namespace `OnBytes.Prover`)   at the written link's wire
      record the numbers that a search tries are written apart, at all caps
  `wiresFit_fullD`   NumbersFit → WiresFit r.queryLayout r.answerCode
  `lawFit_fullD`     NumbersFit → both plain parts of round 0 → LawFit r.queryLayout r.seedQueries capT capL capB, at
      all caps
  `depth_pl0_tOf`, `depth_pl1_tOf` (namespace `FlashProve`)   at the letters S of one set of public
      files both plain parts are of round 0

Limits. `NumbersFit` is a premise: that the data of a set of public files meet it is not shown here.
Nothing says that a verifier says yes, or how likely a run is to fail. Nothing on soundness or
completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.LawsAt
import Johnson.Prover.All.Yes
import Johnson.Prover.All.Law
import Johnson.Prover.Law.PutsAt
import Johnson.Prover.Law.MadeFit
import Johnson.Prover.Print.EntryAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- **The seeds' queries lie off every chain's places**, if both their plain parts are of round 0:
at the seeds' own tag by `seedQ_off`, at another by `seedQ_other`. -/
theorem offAt_of_depth (t : Tag) (h0 : PlainPart.depth _ _ S.pl0 = 0) (h1 : PlainPart.depth _ _ S.pl1 = 0) :
    OffAt W S t (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t) id := by
  intro q hq
  by_cases ht : t = S.t
  · subst ht
    exact seedQ_off (seedsOff_of_depth h0 h1) q hq
  · exact seedQ_other ht q

end

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem putsFree_wiresSL : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    PutsFree _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨fun g hg => grApart_Dn _ g hg, (fun _ hg => by cases hg), putsFree_wiresSL ds⟩

variable (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
  (dec : Y → View → Bool)

theorem putsFree_wqW : PutsFree _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh :=
  ⟨(fun _ hg => by cases hg), (fun _ hg => by cases hg), putsFree_wiresSL C K chal ds⟩

/-- **At the written link's wire record the numbers that a search tries are written apart.** -/
theorem putsApart_wqW (cap : ℕ → ℕ) (i : ℕ) :
    PutsApart _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh cap i :=
  putsApart_of_free _ _ _ (putsFree_wqW C K chal ds a xs dec) cap i

end

end OnBytes.Prover

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Prover (WiresFit LawFit offAt_of_depth putsApart_wqWhole putsApart_wqW fewJ_wqWhole
  few0_wqWhole)
open Johnson.Prover.Print (fewJ_wqW few0_wqW)

/-- The tests on public numbers. -/
structure NumbersFit (K : ℕ) (DK : WholeD) (ds : List TypedOracleCompiler.Run.PQ.RD) (DP : WholeD) :
    Prop where
  blocks : kThree .two DK [] DP ≤ K
  entry : EntryFit K ds
  workK : DK.workFit = true
  depthK : DK.depthFit = true
  workP : DP.workFit = true
  depthP : DP.depthFit = true
  fewK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.trees.length ≤ 2
  fewL : ∀ d ∈ ds, d.trees.length ≤ 2
  fewP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.trees.length ≤ 2

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- **What is asked of the wires, the marks and the three verifiers.** -/
theorem wiresFit_fullD (h : NumbersFit K DK ds DP) :
    WiresFit (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).answerCode where
  oka := oka_fullD T h.blocks h.entry h.workK h.depthK h.workP h.depthP
  fewT := ⟨fewJ_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK h.fewK,
    few0_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK h.fewK⟩
  fewL := ⟨fewJ_wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K) h.fewL,
    few0_wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K)⟩
  fewB := ⟨fewJ_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP h.fewP,
    few0_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP h.fewP⟩
  loc := ⟨keyLocal_fullD T, entryLocal_fullD T, proofLocal_fullD T⟩
  coh := ⟨keyCoherent_fullD T, entryCoherent_fullD T, proofCoherent_fullD T⟩
  fmt := ⟨keyFmt_fullD T, entryFmt_fullD T, proofFmt_fullD T⟩

/-- **What the three chains and the seeds ask of the wires and the caps**, at all caps. -/
theorem lawFit_fullD (h : NumbersFit K DK ds DP) (h0 : PlainPart.depth _ _ T.pl0 = 0)
    (h1 : PlainPart.depth _ _ T.pl1 = 0) (capT capL capB : ℕ → ℕ) :
    LawFit (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).seedQueries capT capL capB where
  offT := offAt_of_depth (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).seedQueries Tag.test h0 h1
  offL := offAt_of_depth (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).seedQueries Tag.link h0 h1
  offB := offAt_of_depth (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).seedQueries Tag.onl h0 h1
  okT := (wiresFit_fullD T h).oka.T
  okL := (wiresFit_fullD T h).oka.Lk
  okB := (wiresFit_fullD T h).oka.B
  fmt := ⟨keyFmt_fullD T, entryFmt_fullD T, proofFmt_fullD T⟩
  putsT := putsApart_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty silK runK capT 0
  putsL := putsApart_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec capL 0
  putsB := putsApart_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP capB 0

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch (PlainPart.depth)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (_root_.Iop.Dig 256))

theorem depth_pl0_tOf : PlainPart.depth _ _ (S.inputFieldsAtReadings c m).pl0 = 0 := by exact rfl
theorem depth_pl1_tOf : PlainPart.depth _ _ (S.inputFieldsAtReadings c m).pl1 = 0 := by exact rfl

end FlashProve
