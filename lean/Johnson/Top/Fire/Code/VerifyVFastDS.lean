-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/VerifyVFastDS.lean: the second half of the fast twin of `verifyV`, at the
small size: the verifier's answer at an input in the frame's make, as a plain function of the
letters, a hash function and what an outside parser hands over, in which no wire record is built.

Why. `verifyOneProtocol` walks the list of all positions of the stored tables (`WireE.all`: 2 ^ a members),
and whoever builds a wire record builds that list (OnBytes/TypedOracleCompiler/Compile/Batch/ListedExt.lean tells
both in its head). At the full size (a = 32) that does not end; this is the small size's twin (a =
23), made of the full size's file by program.
Main names. `DvE`: `DvOf` (VerifyVAtDS.lean) with the entry file's five letters made of the letters
ds, xs, dec (`linkProtocolOfRoundData`; `allLo`; `wqW`; `embT`, `prjT`), and the two depths taken off two shapes of
binding trees. `proofE`: the proof that is laid, on the verifier's side, of two carriers
(`File.toBPrfAt`) and of the entry's chain as read with its two tables (`assembleW`). `fastF`:
build; the code of the key; the test of the commitment ID; then, over a typed family F, a letter:
the stored copy's number, the two seeds' tests, the key's and the proof's arm by `verifyWholeX`
along the lists off the carriers, the entry's arm by `stagesWL`. `fastD`: `fastF` at F :=
`readBlocksV m` of the hash function. `FastDIs`: THE STATEMENT, a proposition at the section's
letters, not proved here: at all further letters and all inputs `fastD` is `verifyVDet` at `DvE` and
`proofE`.
Limits. No theorem. It stands over the files of the lesser wire record
(OnBytes/TypedOracleCompiler/Compile/Batch/LessWire.lean and beside it) and of the strict link
(Johnson/RunOne/StrictLink*.lean). That no list of 2 ^ a members is built is by reading. Of a proof
that is not laid of carriers nothing is said. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.VerifyVDet
import Johnson.Top.Fire.Code.VerifyVAtDS
import OnBytes.Maker.ListedCarrierTop
import OnBytes.Maker.LessWhole
import Johnson.RunOne.StrictLinkWL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutDS
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL)

variable {X : Type} (DK DP : WholeD) (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → PQ.View → Bool) (K salt : ℕ)

local notation "LKe" => linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) ds srS.P.T.a xs dec
local notation "ALe" => _root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds)
local notation "LV" => LvOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "AT" => aTOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "CV" => carrierV LV (List Bool) AT ALe

/-- The input: `DvOf` with the entry file's five letters made of ds, xs, dec. -/
def DvE (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X) : InputV :=
  DvOf DK DP runK runP rK rP sB.logLeaves sT.logLeaves early LKe K salt ALe
    (wqW (ckP .two) ds srS.P.T.a xs dec K (chalP .two K))
    (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
    (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds)
    t cfg shape pl0 pl1 num seed r₀ p m enc build

/-- What an outside parser hands over for a whole file: the carrier, the configuration's bytes, and
the plain parts of the three silent rounds. -/
structure FileIn where
  k : Carrier.File
  cfg : ByteArray
  pF : FrontMsg (List OnBytes.E)
  pJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray
  p3 : ByteArray

/-- What it hands over for the entry file: the root, the record, the configuration's bytes, the
chain as read, and the two tables. -/
structure EntryIn where
  cm : Dig 256
  rcd : RecSmall
  cfg : ByteArray
  o : _root_.Fmt.ChainOut
  tab : Johnson.RunOne.StrictB.Tab
  tx : Johnson.RunOne.StrictB.Tab

/-- The key file's string, laid of its carrier. -/
def piTE (f : FileIn) : Option (OneProtocolProof 256 (batTV LV AT)) :=
  f.k.toBPrfAt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK f.cfg
    sT f.pF f.pJ f.p3

/-- The proof file's. -/
def piBE (f : FileIn) : Option (OneProtocolProof 256 (LV).bat) :=
  f.k.toBPrfAt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP f.cfg
    sB f.pF f.pJ f.p3

/-- The entry file's. -/
def piLE (e : EntryIn) : Option (OneProtocolProof 256 (batLV LV ALe)) :=
  assembleW (ckP .two) ds srS.P.T.a xs dec e.cfg e.o e.tab e.tx

/-- The proof that is laid of what the parser hands over. -/
def proofE (aux : List Token) (cm : Dig 256) (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn)
    (fB : FileIn) : List Token × (KeyRootV 256 LV × PrfRootV 256 LV AT ALe) :=
  (aux, ⟨cm, rcd⟩, ⟨copy, piTE DK DP runK runP rK rP sT sB early ds xs dec fT,
    (e.cm, e.rcd, piLE DK DP runK runP rK rP sB early ds xs dec e),
    piBE DK DP runK runP rK rP sB early ds xs dec fB⟩)

/-- The test of a seed: `seedIsV`'s text (Johnson/TypedOracleCompiler/RecCompile/Seeds.lean), with no wire record
among its arguments. -/
def seedE (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t)) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (cm : Dig 256) (s : (LV).Seed) : TypedOracleComputation 256 (K + 1) CV Bool :=
  (OComp.ask (S := typedOracleFamily 256 (K + 1) CV) (OracleName.fb t)
    (⟨1, .f1 (cm :: cfg) none shape, [], pl0⟩ : FbIn 256 CV t)).bind fun a0 =>
    (OComp.ask (S := typedOracleFamily 256 (K + 1) CV) (OracleName.fb t)
      (⟨2, .f2 none (TypedOracleCompiler.Compile.Batch.link
        (show TypedOracleCompiler.Compile.Batch.FsAns 256 (K + 1) from a0)), [], pl1⟩ :
        FbIn 256 CV t)).bind fun a1 =>
      OComp.pure (@decide _ (seedEqSmall
        (seed (show TypedOracleCompiler.Compile.Batch.FsAns 256 (K + 1) from a1).1) s))

/-- **The fast form, the typed family a letter.** -/
def fastF (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  match build (prompt, output) aux with
  | none => false
  | some x =>
    match enc ⟨cm, rcd⟩ with
    | none => false
    | some code =>
      if hash code = commitment then
        match piTE DK DP runK runP rK rP sT sB early ds xs dec fT,
          piLE DK DP runK runP rK rP sB early ds xs dec e,
          piBE DK DP runK runP rK rP sB early ds xs dec fB with
        | some πT, some πL, some πB =>
          let cA := codeA (v := srS.P.v) (s := 1)
          num copy πB.plains &&
          (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed cm
            rcd.1).det F &&
          (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed e.cm
            e.rcd.1).det F &&
          (verifyWholeX (L := CV) (ckP .two) K (chalP .two K) (DK.at srS.P.T.a) (front₀ rK)
            (join₀ rK) ByteArray.empty silK runK p.sMT p.sFS Tag.test
            (SCode.emb _ (scWhole salt (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
              ByteArray.empty)) id (fun _ => none) (bodyS srS.P.T.a salt).embE sT.logLeaves
            (cm :: cA rcd.2) rcd πT (ownOfCarrier (DK.at srS.P.T.a) fT.k)
            (listedOfCarrier (DK.at srS.P.T.a).a fT.k)).det F &&
          ((stagesWL (ckP .two) ds srS.P.T.a xs dec K (chalP .two K) CV p.sMT p.sFS
              (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds) id (fun _ => none)
              (bodyS srS.P.T.a salt).embE 0 F (cm :: e.cm :: (cA rcd.2 ++ cA e.rcd.2))
              (rcd, e.rcd) πL e.tab e.tx).map OnBytes.Maker.Steps.yes).getD false &&
          (verifyWholeX (L := CV) (ckP .two) K (chalP .two K) (DP.at srS.P.T.a) (front₀ rP)
            (join₀ rP) ByteArray.empty silP runP p.sMT p.sFS Tag.onl
            (SCode.emb _ (scWhole salt (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
              ByteArray.empty)) id (fun a : X × RecSmall => some (some a.1, r₀, r₀))
            (bodyS srS.P.T.a salt).embE sB.logLeaves (e.cm :: e.cm :: cA e.rcd.2) (x, e.rcd) πB
            (ownOfCarrier (DP.at srS.P.T.a) fB.k)
            (listedOfCarrier (DP.at srS.P.T.a).a fB.k)).det F
        | _, _, _ => false
      else false

/-- **The fast form**: `fastF` at the family that is read off the hash function through m. -/
def fastD (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  fastF DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
    (readBlocksV m fun _ => hash) enc build hash commitment prompt output aux cm rcd copy fT e fB

/-- **The statement**, a proposition at the section's letters (X, DK, DP, runK, runP, rK, rP, sT,
sB, early, ds, xs, dec, K, salt): at all further letters and all inputs the fast form is
`verifyVDet` at `DvE` and `proofE`. -/
def FastDIs : Prop :=
  ∀ (t : Tag) (cfg : List (Dig 256)) (shape : Bits) (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    fastD DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p m
        enc build hash commitment prompt output aux cm rcd copy fT e fB =
      verifyVDet
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        hash commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB)

end VerifiableInference.OnPublicFiles.SlotsBehindCutDS

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.DvE
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.proofE
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastF
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastD
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.FastDIs
