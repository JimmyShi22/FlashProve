-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieProved.lean: THE FOUR PROPOSITIONS OF TieStated.lean, PROVED. The full
size.
  `tieT0` : `TieT0` · `tieT1` : `TieT1` · `tieT2D` : `TieT2D` · `tieT2F` : `TieT2F`, each at all the
  section's letters.
How. (T0): the thirteen fields one by one, each by unfolding (the wiring through
`wireOfFull_eq_sibD`); the record by
`InputV.mk_congr` (TieKit.lean). (T1): `DvE` at T's letters is `DvOf` at them, by unfolding, but for
the depth of the key file's request
tree, which sT's hypothesis gives. (T2): `fastD_is_verifyV` (FastDProbe.lean) |
`fastF_reads_is_verifyV` (FastFamProbe.lean), then (T1)
under `verifyV` (`verifyV_congr`), then `verifyV_toInputV_system` (Johnson/Top/InnerCompiledVerifierBack.lean).
LIMITS: THE EIGHT OF TieStated.lean's HEAD GO WITH THESE THEOREMS WHEREVER THEY ARE TOLD; above all:
∀ T, and no T is laid here; T is bound
outside the probability; they are a link at one member `innerSystem (innerCompilerInputAtFullSize T)`, and pay no
hypothesis of the soundness theorem.

-/
import Johnson.Top.Fire.Code.TieStated
import Johnson.Top.Fire.Code.TieKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull}
  {sB : Params.LinBindingShape} {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers}

/-! ## (T0): the fields -/

section Fields
variable (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P)

/-- The wiring: through `wireOfFull_eq_sibD`. -/
theorem tie_W : (innerCompilerInputAtFullSize T).toInputV.W = (DvT T).W := by
  show wireOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt P K T.depthReqT = _
  rw [wireOfFull_eq_sibD]
  rfl

theorem tie_Sd : (innerCompilerInputAtFullSize T).toInputV.Sd = (DvT T).Sd := rfl

set_option maxRecDepth 20000 in
theorem tie_cA : (innerCompilerInputAtFullSize T).toInputV.cA = (DvT T).cA := rfl

theorem tie_r₀ : (innerCompilerInputAtFullSize T).toInputV.r₀ = (DvT T).r₀ := rfl

theorem tie_p : (innerCompilerInputAtFullSize T).toInputV.p = (DvT T).p := rfl

theorem tie_m : (innerCompilerInputAtFullSize T).toInputV.m = (DvT T).m := rfl

theorem tie_enc : (innerCompilerInputAtFullSize T).toInputV.enc = (DvT T).enc := rfl

theorem tie_build : (innerCompilerInputAtFullSize T).toInputV.build = (DvT T).build := rfl

end Fields

variable (A E DK DP runK runP ds xs dec rK rP sB early salt K P)

set_option maxRecDepth 20000 in
/-- **(T0)**: the verifier's side of the soundness theorem's input is the sheet's value `DvOf` at
the letters of T. -/
theorem tieT0 : TieT0 A E DK DP runK runP ds xs dec rK rP sB early salt K P := fun T =>
  InputV.mk_congr (tie_W T) (heq_of_eq (tie_Sd T)) (tie_cA T) (tie_r₀ T) (tie_p T)
    (heq_of_eq (tie_m T)) (tie_enc T) (tie_build T)

variable {A E DK DP runK runP ds xs dec rK rP sB early salt K P}

/-! ## (T1) -/

/-- `DvT` with the depth of the key file's request tree a letter d. -/
abbrev DvTd (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (d : ℕ) : InputV :=
  DvOf DK DP runK runP rK rP sB.logLeaves d early (linkFullD ds xs dec) K salt
    (_root_.Run.Twin.allLo (SOf (ckP .two) ds))
    (wSib (restOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt P) K (chalP .two K))
    (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
    (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
    (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build

set_option maxRecDepth 20000 in
/-- `DvE` at T's letters is `DvOf` at them, at sT's depth: by unfolding. -/
theorem DvET_eq (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape) :
    DvET T sT = DvTd T sT.logLeaves := rfl

variable (A E DK DP runK runP ds xs dec rK rP sB early salt K P)

/-- **(T1)**: the same at `DvE`, the value at which the fast form's equations stand. -/
theorem tieT1 : TieT1 A E DK DP runK runP ds xs dec rK rP sB early salt K P := fun T sT h =>
  (tieT0 A E DK DP runK runP ds xs dec rK rP sB early salt K P T).trans
    ((congrArg (DvTd T) h.symm).trans (DvET_eq T sT).symm)

variable {A E DK DP runK runP ds xs dec rK rP sB early salt K P}

/-! ## (T2) -/

set_option maxRecDepth 20000 in
/-- `verifyV` at `DvE` and `proofE` is the verifier of `innerSystem (innerCompilerInputAtFullSize T)` at the
proof's image under the way back. -/
theorem tie_verify (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape)
    (h : sT.logLeaves = T.depthReqT) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    verifyV (DvET T sT) commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB) =
      (innerSystem (innerCompilerInputAtFullSize T)).verify commitment prompt output
        ((innerCompilerInputAtFullSize T).back
          (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB)) :=
  (verifyV_congr (tieT1 A E DK DP runK runP ds xs dec rK rP sB early salt K P T sT h).symm commitment prompt output HEq.rfl).trans
    (verifyV_toInputV_system (innerCompilerInputAtFullSize T) commitment prompt output
      (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))

variable (A E DK DP runK runP ds xs dec rK rP sB early salt K P)

set_option maxRecDepth 20000 in
/-- **(T2), for the family that is read off the hash through the coding.** -/
theorem tieT2D : TieT2D A E DK DP runK runP ds xs dec rK rP sB early salt K P :=
  fun T sT h hash commitment prompt output aux cm rcd copy fT e fB =>
  (fastD_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt
      T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
      (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build hash commitment prompt output aux cm rcd copy fT e fB).trans
    (congrArg (fun a : DeterministicAlgorithm Bool => a.evaluate hash)
      (tie_verify T sT h commitment prompt output aux cm rcd copy fT e fB))

set_option maxRecDepth 20000 in
/-- **(T2), for what runs**: under the premise `ReadsAs T.m.v O Ff`. -/
theorem tieT2F : TieT2F A E DK DP runK runP ds xs dec rK rP sB early salt K P :=
  fun T sT h O Ff hR commitment prompt output aux cm rcd copy fT e fB =>
  (fastF_reads_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt
      T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
      (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build O Ff hR commitment prompt output aux cm rcd copy fT e fB).trans
    (congrArg (fun a : DeterministicAlgorithm Bool => a.evaluate (hashOf O))
      (tie_verify T sT h commitment prompt output aux cm rcd copy fT e fB))

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tieT0
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tieT1
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tieT2D
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.tieT2F
