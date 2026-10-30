-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
IT TWINS VerifyVFastStepsD.lean AND VerifyVFastD.lean: WHETHER IT SERVES IS FOR A RUN TO SHOW.

Johnson/PV/KitWholeF.lean: THE WHOLE FAST FORM AND ITS TWELVE STEPS WITH THE TWO BIG ARMS AT THE KIT
  MADE FOR A RUN, THE FULL SIZE: fastSteps | fastF (VerifyVFastStepsD.lean; VerifyVFastD.lean
  beneath) WITH armTET | armBET (Johnson/PV/KitArmsF.lean) IN THE TWO ARMS' PLACES; ALL ELSE TO THE
  LETTER.
  **fastStepsT · fastStepsT_eq : fastStepsT … = fastSteps …** · **fastFT · fastFT_eq : fastFT … =
    fastF …**: no premise: by cases on what is built and laid, then armTET_eq | armBET_eq.
SO WHATEVER IS SAID OF fastF | fastSteps (fastF_reads_is_verifyV; the statement on the steps) IS
  SAID OF WHAT RUNS. No soundness.


-/
import Johnson.PV.KitArmsF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)

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

/-- **The fast form's steps, the two big arms at the kit made for a run.** -/
def fastStepsT (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
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
            armTET DK DP runK runP rK rP sT sB early ds xs dec K salt p F cm rcd fT πT,
            armLE DK DP runK runP rK rP sB early ds xs dec K salt p F cm rcd e πL,
            armBET DK DP runK runP rK rP sB early ds xs dec K salt r₀ p F x e fB πB⟩
        | a, b, c =>
          ⟨true, true, true, a.isSome, b.isSome, c.isSome, false, false, false, false, false,
            false⟩
      else ⟨true, true, false, false, false, false, false, false, false, false, false, false⟩

/-- **They are fastSteps (VerifyVFastStepsD.lean).** -/
theorem fastStepsT_eq (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastStepsT DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
        F enc build hash commitment prompt output aux cm rcd copy fT e fB = fastSteps DK DP runK
        runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p F enc build hash
        commitment prompt output aux cm rcd copy fT e fB := by
  unfold fastStepsT fastSteps
  cases build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases enc ⟨cm, rcd⟩ with
    | none => rfl
    | some code =>
      dsimp only
      by_cases h : hash code = commitment
      · rw [if_pos h, if_pos h]
        generalize piTE DK DP runK runP rK rP sT sB early ds xs dec fT = a
        generalize piLE DK DP runK runP rK rP sB early ds xs dec e = b
        generalize piBE DK DP runK runP rK rP sB early ds xs dec fB = c
        rcases a with _ | πT <;> rcases b with _ | πL <;> rcases c with _ | πB <;>
          first
          | rfl
          | (dsimp only
             rw [armTET_eq, armBET_eq]
             skip)
      · rw [if_neg h, if_neg h]

/-- **The fast form, the two big arms at the kit made for a run.** -/
def fastFT (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
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
          num copy πB.plains &&
          (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed cm
            rcd.1).det F &&
          (seedE DK DP runK runP rK rP sB early ds xs dec K t cfg shape pl0 pl1 seed e.cm
            e.rcd.1).det F &&
          armTET DK DP runK runP rK rP sT sB early ds xs dec K salt p F cm rcd fT πT &&
          armLE DK DP runK runP rK rP sB early ds xs dec K salt p F cm rcd e πL &&
          armBET DK DP runK runP rK rP sB early ds xs dec K salt r₀ p F x e fB πB
        | _, _, _ => false
      else false

/-- **It is fastF (VerifyVFastD.lean).** -/
theorem fastFT_eq (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastFT DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p F
        enc build hash commitment prompt output aux cm rcd copy fT e fB = fastF DK DP runK runP rK
        rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p F enc build hash
        commitment prompt output aux cm rcd copy fT e fB := by
  unfold fastFT fastF
  cases build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases enc ⟨cm, rcd⟩ with
    | none => rfl
    | some code =>
      dsimp only
      by_cases h : hash code = commitment
      · rw [if_pos h, if_pos h]
        generalize piTE DK DP runK runP rK rP sT sB early ds xs dec fT = a
        generalize piLE DK DP runK runP rK rP sB early ds xs dec e = b
        generalize piBE DK DP runK runP rK rP sB early ds xs dec fB = c
        rcases a with _ | πT <;> rcases b with _ | πL <;> rcases c with _ | πB <;>
          first
          | rfl
          | (dsimp only
             rw [armTET_eq, armBET_eq]
             rfl)
      · rw [if_neg h, if_neg h]

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.fastStepsT_eq
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.fastFT_eq
