-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/FastDProbeS.lean: the statement `FastDIs` (VerifyVFastDS.lean), proved, at the
small size; and with it the equation of the fast form with `verifyV`.

Main names (namespace `VerifiableInference.OnPublicFiles.SlotsBehindCutDS`).
  `fastD_is`: `FastDIs`: `fastD` is `verifyVDet` at `DvE` and `proofE`.
  `fastD_is_verifyV`: so `fastD` is the evaluation of `verifyV` at `DvE` and `proofE`, at every hash
    function (by `verifyVDet_is`, VerifyVDetProbe.lean).
  `fastF_is_verifyV`: the same for `fastF` over a typed family F, under one premise: F is what is
    read off the hash function through m (`readBlocksV`).
They rest on the three arms' laws (ArmsAtCarrierXS.lean, ArmEntryAtTablesS.lean) and on `VRAV_det`
(VCAVDet.lean).
Limits. They speak of a proof of `proofE`'s make alone; the parser stands outside the equation, on
both sides. That the input `DvE` is one of which a soundness theorem speaks is not shown here. The
premise of `fastF_is_verifyV` is met here at `fastD`'s own family alone; that a family made for a
run meets it is `ReadsAs` (FastFamProbe.lean), of which no member is in the library. Nothing on time
or memory. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.VerifyVFastDS
import Johnson.Top.Fire.Code.ArmsAtCarrierXS
import Johnson.Top.Fire.Code.ArmEntryAtTablesS
import Johnson.Top.Fire.Code.VCAVDet
import Johnson.Top.Fire.Code.VerifyVDetProbe

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

theorem and6 {a a' b b' c c' d d' e e' f f' : Bool} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') (h5 : e = e') (h6 : f = f') :
    (a && b && c && d && e && f) = (a' && b' && c' && d' && e' && f') := by
  subst h1 h2 h3 h4 h5 h6
  rfl

theorem fastD_is : FastDIs DK DP runK runP rK rP sT sB early ds xs dec K salt := by
  intro t cfg shape pl0 pl1 num seed r₀ p m enc build hash commitment prompt output aux cm rcd
    copy fT e fB
  unfold fastD fastF verifyVDet
  dsimp only [DvE, DvOf, proofE]
  cases build (prompt, output) aux with
  | none => rfl
  | some x =>
    dsimp only
    cases enc ⟨cm, rcd⟩ with
    | none => rfl
    | some code =>
      dsimp only
      by_cases hd : hash code = commitment
      · rw [if_pos hd, if_pos hd, VRAV_det]
        dsimp only
        cases hT : piTE DK DP runK runP rK rP sT sB early ds xs dec fT with
        | none => rfl
        | some πT =>
          cases hL : piLE DK DP runK runP rK rP sB early ds xs dec e with
          | none => rfl
          | some πL =>
            cases hB : piBE DK DP runK runP rK rP sB early ds xs dec fB with
            | none => rfl
            | some πB =>
              have kT := keyArm_carrierX DK DP runK runP rK rP sB.logLeaves early
                (linkProtocolOfRoundData (ckP .two) ds srS.P.T.a xs dec) K salt
                (_root_.Run.Twin.allLo (SOf (ckP .two) ds))
                (wqW (ckP .two) ds srS.P.T.a xs dec K (chalP .two K))
                (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
                (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds)
                (codeA (v := srS.P.v) (s := 1)) p cm rcd sT fT.k fT.cfg fT.pF fT.pJ fT.p3
              have kB := proofArm_carrierX DK DP runK runP rK rP sT.logLeaves early
                (linkProtocolOfRoundData (ckP .two) ds srS.P.T.a xs dec) K salt sB
                (_root_.Run.Twin.allLo (SOf (ckP .two) ds))
                (wqW (ckP .two) ds srS.P.T.a xs dec K (chalP .two K))
                (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
                (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds)
                (codeA (v := srS.P.v) (s := 1)) r₀ p e.cm x e.rcd fB.k fB.cfg fB.pF fB.pJ fB.p3
              have kL := entryArm_tables DK DP runK runP rK rP sB.logLeaves sT.logLeaves early ds
                xs dec K salt (codeA (v := srS.P.v) (s := 1)) p cm e.cm rcd e.rcd e.cfg e.o e.tab
                e.tx πL hL (readBlocksV m fun _ => hash)
              unfold carrierAtX at kT kB
              unfold piTE at hT
              unfold piBE at hB
              rw [hT] at kT
              rw [hB] at kB
              have kT' := congrArg (Rom.OComp.det (readBlocksV m fun _ => hash)) kT
              have kB' := congrArg (Rom.OComp.det (readBlocksV m fun _ => hash)) kB
              dsimp only [Option.elim] at kT' kB'
              exact and6 rfl rfl rfl kT' kL kB'
      · rw [if_neg hd, if_neg hd]

/-- **The one equation**: the fast form is the evaluation of `verifyV` at `DvE` and `proofE`: at all
letters, every hash function and all that a parser can hand over. No premise. -/
theorem fastD_is_verifyV :
  ∀ (t : Tag) (cfg : List (Dig 256)) (shape : Bits) (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    fastD DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p m
        enc build hash commitment prompt output aux cm rcd copy fT e fB =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e
          fB)).evaluate hash := by
  intro t cfg shape pl0 pl1 num seed r₀ p m enc build hash commitment prompt output aux cm rcd
    copy fT e fB
  rw [verifyVDet_is]
  exact fastD_is DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed
    r₀ p m enc build hash commitment prompt output aux cm rcd copy fT e fB

/-- **The same with the family a letter**: under one premise: F is what is read off the hash
function through m. -/
theorem fastF_is_verifyV :
  ∀ (t : Tag) (cfg : List (Dig 256)) (shape : Bits) (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (F : Fam (typedOracleFamily 256 (K + 1) CV))
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    F = (readBlocksV m fun _ => hash) →
    fastF DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p F
        enc build hash commitment prompt output aux cm rcd copy fT e fB =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e
          fB)).evaluate hash := by
  intro t cfg shape pl0 pl1 num seed r₀ p m F enc build hash commitment prompt output aux cm rcd
    copy fT e fB hF
  subst hF
  exact fastD_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1
    num seed r₀ p m enc build hash commitment prompt output aux cm rcd copy fT e fB

end VerifiableInference.OnPublicFiles.SlotsBehindCutDS

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastD_is
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastD_is_verifyV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastF_is_verifyV
