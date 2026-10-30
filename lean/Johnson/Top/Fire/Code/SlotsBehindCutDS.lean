-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/SlotsBehindCutDS.lean: the verifier's side of the object of the small size in
the frame's make (the rounds' data DK, DP, the two decisions runK, runP and five more are letters),
written out as a value of `LHV`, and the slots Sd and W at it, each as a definition without a mark.
The entry file's protocol, its marks, its wire record and its two maps on bodies are letters here,
and so are the number of blocks and the seed's map. Three examples tie what is written out here to
the library's terms at the makers' data.
-/
import Johnson.Flat.TwoSizes
import Johnson.TypedOracleCompiler.RecCompile.CmsAnsSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutDS
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS)

variable {X : Type} (DK DP : WholeD) (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall)
  (depthReq depthReqT : ℕ) (early : X → X)
  (lk : InteractiveOracleProof (RecSmall × RecSmall) (twoExternalStrings (2 ^ srS.P.T.a) _root_.Run.PQ.SgX))

/-- The verifier's side of the object, written out; the entry file's protocol a letter. -/
def LvOf : LHV X where
  n := 2 ^ srS.P.T.a
  Sg := _root_.Run.PQ.SgX
  Seed := Fin 1 → (Fin 19 → GE) × NZ
  Ans := (Fin srS.P.v → Bool) × Fin 1 → GE
  test := (reductionOfWholeFile (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK
    runK).toInteractiveOracleProof
  link := lk
  N := 2 ^ depthReq
  bat := ⟨(reductionOfWholeFile (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP).toInteractiveOracleProof,
    (chainsOf (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).ann⟩
  early := early
  late := none

local notation "LV" => LvOf DK DP runK runP rK rP depthReq early lk

/-- The key file's marks, at it. -/
def aTOf : RoundSplits (LV).test.shape :=
  (chainsOf (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).ann

local notation "AT" => aTOf DK DP runK runP rK rP depthReq early lk

variable (K salt : ℕ)

/-- The slot Sd at the verifier's side. -/
def probe_SdV (aL : RoundSplits (LV).link.shape) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (carrierV LV (List Bool) AT aL) t)
      (annOf (carrierV LV (List Bool) AT aL) t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin K → Dig 256) → (LV).Seed) :
    SeedV 256 K LV (List Bool) AT aL where
  t := t
  cfg := cfg
  shape := shape
  pl0 := pl0
  pl1 := pl1
  seed := seed
  code := fun r => codeP (fun β : NZ => β.val) r
  num := num
  decS := seedEqSmall

/-- The slot W at the verifier's side: `wireOf2`'s body, written out. -/
def probe_WV (aL : RoundSplits (LV).link.shape) (wL : ProtocolQueryLayout 256 (K + 1) (batLV LV aL))
    (embL : (p : OPos (LV).link.shape) → OSym (LV).link.shape p → List Bool)
    (prjL : (p : OPos (LV).link.shape) → List Bool → Option (OSym (LV).link.shape p)) :
    QueryLayout 256 (carrierV LV (List Bool) AT aL) where
  K := K + 1
  T := ⟨(wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).sh,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).ext,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).decO,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).nOpen,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).maxDepth⟩
  Lk := ⟨wL.sh, wL.ext, wL.decO, wL.nOpen, wL.maxDepth⟩
  B := ⟨(wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).sh,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).ext,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).decO,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).nOpen,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).maxDepth⟩
  depth := srS.P.T.a
  depthReq := depthReq
  depthReqT := depthReqT
  depthReqL := 0
  embE := (bodyS srS.P.T.a salt).embE
  prjE := (bodyS srS.P.T.a salt).getE
  embT := SCode.emb _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty)
  prjT := SCode.prj _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty)
  embL := embL
  prjL := prjL
  embB := SCode.emb _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty)
  prjB := SCode.prj _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty)

/-! ## what is written out here, against the library's terms at the makers' data -/

section Tie
variable (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The written verifier's side is the library's object's. -/
example : LvOf (dataKSmall G) (dataPSmall G) (runKSmall G) (runPSmall G) G.rec₀ G.z₀.2 G.depthReq
    G.early linkSibSmall = ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P).v := rfl

/-- The written slot Sd is the library's `outOfDomainSampleQueryLayoutOfCode` at the library's object. -/
example (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
               (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t)
      (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL) t))
    (num : ℕ → Plains ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool)
    (seed : (Fin K → Dig 256) → ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P).OutOfDomainSeed) :
    (outOfDomainSampleQueryLayoutOfCode ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool) _ _ (v := srS.P.v) (lg := 19) (s := 1)
        t cfg shape pl0 pl1 num seed id seedEqSmall).v =
      probe_SdV (dataKSmall G) (dataPSmall G) (runKSmall G) (runPSmall G) G.rec₀ G.z₀.2 G.depthReq
        G.early linkSibSmall K (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL t cfg shape pl0 pl1 num seed :=
  rfl

/-- The written slot W is the library's `wireSmallK`. -/
example : wireSmallK A E G P K salt =
    probe_WV (dataKSmall G) (dataPSmall G) (runKSmall G) (runPSmall G) G.rec₀ G.z₀.2 G.depthReq
      G.k.oneTime.binding.logLeaves G.early linkSibSmall K salt (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).annL
      (wSib (restSmallAt A E G P) K (chalP .two K))
      (TypedOracleCompiler.StringsList.embT salt (ckP .two) dsSmall)
      (TypedOracleCompiler.StringsList.prjT salt (ckP .two) dsSmall) := rfl

end Tie

end VerifiableInference.OnPublicFiles.SlotsBehindCutDS

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.LvOf
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.aTOf
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.probe_SdV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.probe_WV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.carrierV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.batLV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.SeedV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
set_option pp.proofs true in
set_option pp.deepTerms true in
set_option pp.maxSteps 100000 in
#check @VerifiableInference.OnPublicFiles.SlotsBehindCutDS.probe_SdV
