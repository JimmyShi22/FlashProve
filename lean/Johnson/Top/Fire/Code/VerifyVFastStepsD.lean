-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/VerifyVFastStepsD.lean: the steps of the fast form `fastF` (VerifyVFastD.lean)
by name, for a print, at the full size.

Why. `fastF` gives one Bool. A print is to say each step's yes or no by name, and what it prints
should be tied to `fastF` by a law, not by a copy of its text in a sheet.
Main names. `armTE`, `armLE`, `armBE`: the three arms, each the text that stands in `fastF`.
`FastSteps`: twelve Bools: buildOk, encOk, idOk; laidT, laidL, laidB; num, seed0, seedJ, armT, armL,
armB. `FastSteps.yes`: their «and». `fastSteps`: the twelve at `fastF`'s own arguments.
`FastStepsIs`: THE STATEMENT, a proposition at the section's letters, not proved here: `fastF` is
`(fastSteps …).yes`.
Limits. No theorem. A later step is false where an earlier one that it needs has failed: such a
false says nothing of that step. All twelve are computed when the record is built: no step is spared
by an earlier no among the last six. Nothing on time or memory. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.VerifyVFastD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne.StrictW (wqW assembleW stagesWL)

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (K salt : ℕ)

local notation "LKe" => linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) ds frS.P.T.a xs dec
local notation "ALe" => _root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds)
local notation "LV" => LvOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "AT" => aTOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "CV" => carrierV LV (List Bool) AT ALe

/-- The key's arm: the verifier of a whole file along the lists off the carrier, at a family. -/
def armTE (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (cm : Dig 256) (rcd : RecFull)
    (fT : FileIn) (πT : OneProtocolProof 256 (batTV LV AT)) : Bool :=
  (verifyWholeX (L := CV) (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK)
    (join₀ rK) ByteArray.empty silK runK p.sMT p.sFS Tag.test
    (SCode.emb _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty)) id (fun _ => none) (bodyS frS.P.T.a salt).embE sT.logLeaves
    (cm :: codeA (v := frS.P.v) (s := 1) rcd.2) rcd πT (ownOfCarrier (DK.at frS.P.T.a) fT.k)
    (listedOfCarrier (DK.at frS.P.T.a).a fT.k)).det F

/-- The entry's arm: the strict link's fourteen lines. -/
def armLE (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (cm : Dig 256) (rcd : RecFull)
    (e : EntryIn) (πL : OneProtocolProof 256 (batLV LV ALe)) : Bool :=
  ((stagesWL (ckP .two) ds frS.P.T.a xs dec K (chalP .two K) CV p.sMT p.sFS
      (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds) id (fun _ => none)
      (bodyS frS.P.T.a salt).embE 0 F
      (cm :: e.cm :: (codeA (v := frS.P.v) (s := 1) rcd.2 ++
        codeA (v := frS.P.v) (s := 1) e.rcd.2))
      (rcd, e.rcd) πL e.tab e.tx).map OnBytes.Maker.Steps.yes).getD false

/-- The proof's arm. -/
def armBE (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (x : X) (e : EntryIn)
    (fB : FileIn) (πB : OneProtocolProof 256 (LV).bat) : Bool :=
  (verifyWholeX (L := CV) (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP)
    (join₀ rP) ByteArray.empty silP runP p.sMT p.sFS Tag.onl
    (SCode.emb _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
      ByteArray.empty)) id (fun a : X × RecFull => some (some a.1, r₀, r₀))
    (bodyS frS.P.T.a salt).embE sB.logLeaves
    (e.cm :: e.cm :: codeA (v := frS.P.v) (s := 1) e.rcd.2) (x, e.rcd) πB
    (ownOfCarrier (DP.at frS.P.T.a) fB.k) (listedOfCarrier (DP.at frS.P.T.a).a fB.k)).det F

/-- The twelve steps of the fast form, by name. A later step is false where an earlier one that it
needs has failed. -/
structure FastSteps where
  /-- an instance is built -/
  buildOk : Bool
  /-- the key has a code -/
  encOk : Bool
  /-- the hash of the key's code is the commitment ID -/
  idOk : Bool
  /-- the three strings are laid -/
  laidT : Bool
  laidL : Bool
  laidB : Bool
  /-- the six conjuncts of the verifier, in its order -/
  num : Bool
  seed0 : Bool
  seedJ : Bool
  armT : Bool
  armL : Bool
  armB : Bool

/-- All twelve. -/
def FastSteps.yes (s : FastSteps) : Bool :=
  s.buildOk && s.encOk && s.idOk && s.laidT && s.laidL && s.laidB &&
    (s.num && s.seed0 && s.seedJ && s.armT && s.armL && s.armB)

/-- **The fast form's steps.** -/
def fastSteps (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : FastSteps :=
  match build (prompt, output) aux with
  | none => ⟨false, false, false, false, false, false, false, false, false, false, false, false⟩
  | some x =>
    match enc ⟨cm, rcd⟩ with
    | none => ⟨true, false, false, false, false, false, false, false, false, false, false, false⟩
    | some code =>
      if hash code = commitment then
        match piTE DK DP runK runP rK rP sT sB early ds xs dec fT,
          piLE DK DP runK runP rK rP sB early ds xs dec e,
          piBE DK DP runK runP rK rP sB early ds xs dec fB with
        | some πT, some πL, some πB =>
          ⟨true, true, true, true, true, true, num copy πB.plains,
            (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed cm
              rcd.1).det F,
            (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed e.cm
              e.rcd.1).det F,
            armTE DK DP runK runP rK rP sT sB early ds xs dec K salt p F cm rcd fT πT,
            armLE DK DP runK runP rK rP sB early ds xs dec K salt p F cm rcd e πL,
            armBE DK DP runK runP rK rP sB early ds xs dec K salt r₀ p F x e fB πB⟩
        | a, b, c =>
          ⟨true, true, true, a.isSome, b.isSome, c.isSome, false, false, false, false, false,
            false⟩
      else ⟨true, true, false, false, false, false, false, false, false, false, false, false⟩

/-- **The statement on the steps**: the fast form is the «and» of its twelve steps. -/
def FastStepsIs : Prop :=
  ∀ (t : Tag) (cfg : List (Dig 256)) (shape : Bits) (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    fastF DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p F
        enc build hash commitment prompt output aux cm rcd copy fT e fB =
      (fastSteps DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed
        r₀ p F enc build hash commitment prompt output aux cm rcd copy fT e fB).yes

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.armTE
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.armLE
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.armBE
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.fastSteps
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.FastStepsIs
