-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/FirstBlockAt.lean: the premises of the first-block exit
(Johnson/Prover/Law/FirstBlockLaws.lean, CountF.lean), PAID AT THE FRAME's OWN LETTERS: the one
encoding of all typed oracles (mAll, Johnson/PV/CutAll.lean; mAny, Johnson/PV/LawsAny.lean); the
wiring of the three files at the full size at any data of rounds (wireOfFullD,
Johnson/Flat/Dec/WiresAtSizes.lean); the seeds' two queries (Johnson/TypedOracleCompiler/RecCompile/Seeds.lean).
Calls: it adds no strength.

Main names.
  firstIs_mAll     FirstIs at the one encoding, at every cut and every number of blocks above 0.
  workFrame DK ds DP   A DEFINITION: the bits of work by the tag and the round's number: the key
    file's, the copy's file's, the proof file's. It names no goal's form.
  testsAt_frameT, testsAt_frameL, testsAt_frameB   TestsAt at the three wire records of wireOfFullD,
    at embP := id, at ONE function passAt (workFrame DK ds DP): no premise.
  askedWhole_seedQ0, askedWhole_seedQ1   the seeds' two queries are asked whole, where their plain
    parts are of round 0.

Limits. THE FULL SIZE ALONE (the small size's wiring has the same text; not typed). DK, DP, ds and
the two decisions are letters: nothing here says which data stand at any public files. That the wire
of an input that verify() reads off the hash function IS wireOfFullD is not shown here. "Of round 0"
is a premise here (for the frame's own plain part: by unfolding, in another file). No prover is
called: that the compiled provers at these records factor and what they cost follows by
factors_proveX and hashCalls_proveX; not typed here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.PassAt
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.PV.CutAll
import Johnson.TypedOracleCompiler.RecCompile.Seeds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The encoding -/

section Enc
open OnBytes.K.Arm TypedOracleCompiler.Run
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} {C : BothCut L K}

/-- **FirstIs at the one encoding of all typed oracles.** -/
theorem firstIs_mAll (hK : 0 < K) (H : BothLaws C) {lL : ℕ} (G : LinkLaws C lL)
    (back : StrCode (AllPts 256 K L)) : FirstIs hK (mAll H G back) :=
  firstIs_of hK _ (fun _ => rfl) fun _ _ _ => rfl

end Enc

/-! ## The seeds -/

section Seeds
variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (work : Tag → ℕ → ℕ)

theorem askedWhole_seedQ0 (h : PlainPart.depth _ _ S.pl0 = 0) (cm : Dig 256) :
    AskedWhole (passAt (typedOracleCarrier L Bd aT aL) work) (OracleName.fb S.t) (seedQ0 W S cm) := fun b =>
  passAt_off _ work S.t (seedQ0 W S cm) b (by
    show (1 : ℕ) ≠ PlainPart.depth _ _ S.pl0
    rw [h]
    decide)

theorem askedWhole_seedQ1 (h : PlainPart.depth _ _ S.pl1 = 0) (v : Bits) :
    AskedWhole (passAt (typedOracleCarrier L Bd aT aL) work) (OracleName.fb S.t) (seedQ1 W S v) := fun b =>
  passAt_off _ work S.t (seedQ1 W S v) b (by
    show (2 : ℕ) ≠ PlainPart.depth _ _ S.pl1
    rw [h]
    decide)

end Seeds

/-! ## The wiring -/

/-- The bits of work by the tag and the round's number. a: the stored tables' depth. -/
def workFrame (a : ℕ) (DK : OnBytes.Maker.WholeD) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (DP : OnBytes.Maker.WholeD) : Tag → ℕ → ℕ
  | .test => OnBytes.Maker.Page.workAt (DK.at a)
  | .link => workL ds
  | .onl => OnBytes.Maker.Page.workAt (DP.at a)

section Frame
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

local notation "WW" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT
set_option quotPrecheck false in
local notation "LL" =>
  typedOracleCarrier ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
    (List Bool) (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annT
    (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).annL

/-- **The key file's wire record.** -/
theorem testsAt_frameT :
    TestsAt (Nat.succ_pos K) (passAt LL (workFrame frS.P.T.a DK ds DP)) Tag.test 0 _ _ (wTC WW).sh
      id :=
  testsAt_wqWhole LL (workFrame frS.P.T.a DK ds DP) Tag.test (ckP .two) K (chalP .two K)
    (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK id (fun _ => rfl)
    fun _ => rfl

/-- **The copy's file's.** -/
theorem testsAt_frameL :
    TestsAt (Nat.succ_pos K) (passAt LL (workFrame frS.P.T.a DK ds DP)) Tag.link 0 _ _ (wLC WW).sh
      id :=
  testsAt_wqW LL (workFrame frS.P.T.a DK ds DP) Tag.link (ckP .two) K (chalP .two K) ds frS.P.T.a
    xs dec id (fun _ => rfl) fun _ => rfl

/-- **The proof file's.** -/
theorem testsAt_frameB :
    TestsAt (Nat.succ_pos K) (passAt LL (workFrame frS.P.T.a DK ds DP)) Tag.onl 0 _ _ (wBC WW).sh
      id :=
  testsAt_wqWhole LL (workFrame frS.P.T.a DK ds DP) Tag.onl (ckP .two) K (chalP .two K)
    (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP id (fun _ => rfl)
    fun _ => rfl

end Frame

end OnBytes.Prover

#print axioms OnBytes.Prover.firstIs_mAll
#print axioms OnBytes.Prover.askedWhole_seedQ0
#print axioms OnBytes.Prover.askedWhole_seedQ1
#print axioms OnBytes.Prover.testsAt_frameT
#print axioms OnBytes.Prover.testsAt_frameL
#print axioms OnBytes.Prover.testsAt_frameB
