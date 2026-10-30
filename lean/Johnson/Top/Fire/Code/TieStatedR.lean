-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieStatedR.lean. A STATEMENT ALONE: ONE PROPOSITION, NOT PROVED HERE. The full
size.
  `TieT2R`: THE CHAIN FOR WHAT RUNS, THROUGH THE LINK AT THE SPARE ORACLE: `fastF` at a family Ff
  and the hash made of O is the evaluation of the
  verifier of `innerSystem (innerCompilerInputAtFullSize T)`, UNDER TWO PREMISES: `ReadsAs mR O Ff` (Ff is what a
  writing side mR reads out of the hash made of O) and
  `SameOffSpare mR T.m.v (fun _ => hashOf O)` (mR and the coding T.m's writing side read the same
  out of that hash at every oracle but `OracleName.other`).
Why it stands beside `TieT2F` (TieStated.lean). `TieT2F` asks `ReadsAs T.m.v O Ff`, at every oracle.
T.m is one to one and onto. The family that a run
calls reads a writing side with code which, by its makers' word, parts from every such coding that
is laid at the spare oracle: so at that family
`TieT2F`'s premise is not to be had. Here the run's writing side is a letter mR of its own.
LIMITS: THE EIGHT OF TieStated.lean's HEAD, but for the second, which now reads: 2. mR IS A LETTER:
that a run's writing side and family meet the two
premises at a T that is laid is owed by whoever lays them (at a run's values: TieAtValues.lean). TO
THE EIGHTH: beside the configuration's digest c, the seven digests dK · dP · pdL
stand inside a coding that is laid for T.m and are made at the fixed hash. AND: 9. WHAT A RUN CALLS
IS A TWIN OF `fastF` AT ANOTHER KIT, AT A FAMILY THAT IS BOUND ONCE: these two equations are not
here: `fastFT_eq` (Johnson/PV/KitWholeF.lean) and `LPFD.famBound_eq` := rfl (Vals/FastFull.lean:
`W4M.famPrepQ pr bk O …` is `PV.MFull.famFQ …`); the join: TieJoin.lean.
-/
import Johnson.Top.Fire.Code.TieStated
import Johnson.Top.Fire.Code.TmStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull)
  (sB : Params.LinBindingShape) (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers)

/-- (T2), FOR WHAT RUNS, THROUGH THE LINK AT THE SPARE ORACLE. -/
def TieT2R : Prop :=
  ∀ (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape), sT.logLeaves = T.depthReqT →
    ∀ (O : ByteArray → ByteArray)
      (mR : ImplV (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL)) 256)
      (Ff : Fam (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL))),
      ReadsAs mR O Ff → SameOffSpare mR T.m.v (fun _ => hashOf O) →
    ∀ (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
      (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
      fastF DK DP runK runP rK rP sT sB early ds xs dec K salt
          T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p Ff
          (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build (hashOf O) commitment prompt output aux cm rcd copy fT e fB =
        ((innerSystem (innerCompilerInputAtFullSize T)).verify commitment prompt output
          ((innerCompilerInputAtFullSize T).back
            (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))).evaluate (hashOf O)

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TieT2R
