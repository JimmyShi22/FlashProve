-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/SlotsBehindCutD.lean: the verifier's side of the object of the full size in
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

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS)

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (depthReq depthReqT : ℕ) (early : X → X)
  (lk : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX))

/-- The verifier's side of the object, written out; the entry file's protocol a letter. -/
def LvOf : LHV X where
  n := 2 ^ frS.P.T.a
  Sg := _root_.Run.PQ.SgX
  Seed := Fin 1 → (Fin 29 → GE) × NZ
  Ans := (Fin frS.P.v → Bool) × Fin 1 → GE
  test := (reductionOfWholeFile (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK
    runK).toInteractiveOracleProof
  link := lk
  N := 2 ^ depthReq
  bat := ⟨(reductionOfWholeFile (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP).toInteractiveOracleProof,
    (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).ann⟩
  early := early
  late := none

local notation "LV" => LvOf DK DP runK runP rK rP depthReq early lk

/-- The key file's marks, at it. -/
def aTOf : RoundSplits (LV).test.shape :=
  (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).ann

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
  decS := seedEqFull

/-- The slot W at the verifier's side: `wireOf2`'s body, written out. -/
def probe_WV (aL : RoundSplits (LV).link.shape) (wL : ProtocolQueryLayout 256 (K + 1) (batLV LV aL))
    (embL : (p : OPos (LV).link.shape) → OSym (LV).link.shape p → List Bool)
    (prjL : (p : OPos (LV).link.shape) → List Bool → Option (OSym (LV).link.shape p)) :
    QueryLayout 256 (carrierV LV (List Bool) AT aL) where
  K := K + 1
  T := ⟨(wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).sh,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).ext,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).decO,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).nOpen,
    (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK).maxDepth⟩
  Lk := ⟨wL.sh, wL.ext, wL.decO, wL.nOpen, wL.maxDepth⟩
  B := ⟨(wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).sh,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).ext,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).decO,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).nOpen,
    (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty silP runP).maxDepth⟩
  depth := frS.P.T.a
  depthReq := depthReq
  depthReqT := depthReqT
  depthReqL := 0
  embE := (bodyS frS.P.T.a salt).embE
  prjE := (bodyS frS.P.T.a salt).getE
  embT := SCode.emb _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty)
  prjT := SCode.prj _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty)
  embL := embL
  prjL := prjL
  embB := SCode.emb _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty)
  prjB := SCode.prj _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty)

/-! ## what is written out here, against the library's terms at the makers' data -/

section Tie
variable (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers)

/-- The written verifier's side is the library's object's. -/
example : LvOf (dataKFull G) (dataPFull G) (runKFull G) (runPFull G) G.rec₀ G.z₀.2 G.depthReq
    G.early linkSibFull = ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P).v := rfl

/-- The written slot Sd is the library's `outOfDomainSampleQueryLayoutOfCode` at the library's object. -/
example (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
               (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t)
      (annOf (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool)
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annT (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL) t))
    (num : ℕ → Plains ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool)
    (seed : (Fin K → Dig 256) → ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P).OutOfDomainSeed) :
    (outOfDomainSampleQueryLayoutOfCode ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P) (List Bool) _ _ (v := frS.P.v) (lg := 29) (s := 1)
        t cfg shape pl0 pl1 num seed id seedEqFull).v =
      probe_SdV (dataKFull G) (dataPFull G) (runKFull G) (runPFull G) G.rec₀ G.z₀.2 G.depthReq
        G.early linkSibFull K (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL t cfg shape pl0 pl1 num seed := rfl

/-- The written slot W is the library's `wireFullK`. -/
example : wireFullK A E G P K salt =
    probe_WV (dataKFull G) (dataPFull G) (runKFull G) (runPFull G) G.rec₀ G.z₀.2 G.depthReq
      G.k.oneTime.binding.logLeaves G.early linkSibFull K salt (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).annL
      (wSib (restFullAt A E G P) K (chalP .two K))
      (TypedOracleCompiler.StringsList.embT salt (ckP .two) dsFull)
      (TypedOracleCompiler.StringsList.prjT salt (ckP .two) dsFull) := rfl

end Tie

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.LvOf
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.aTOf
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.probe_SdV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.probe_WV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.carrierV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.batLV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.SeedV
#print axioms TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
set_option pp.proofs true in
set_option pp.deepTerms true in
set_option pp.maxSteps 100000 in
#check @VerifiableInference.OnPublicFiles.SlotsBehindCutD.probe_SdV
