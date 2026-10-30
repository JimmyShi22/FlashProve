-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TmStatement.lean: the link from the coding's writing side that a run lays to
another one that agrees with it off the spare oracle: THREE STATEMENTS, as propositions. Nothing is
proved here.

Why. What runs has a writing side with code (`ImplV`). The soundness theorem's input has a bijective
coding M : `OracleCoding`, of which `verifyV` reads `M.v`. By their makers' word the two have the same
blocks and the same reading of answers, and write the same strings at every oracle but the spare one
(`OracleName.other`): so they are not one record.
Main names. `NoSpare`: the verifier `VRAV` never asks the spare oracle: at every object, wire
record, seeds' record, key, instance and proof. `SameOffSpare m m' g`: what m and m' read out of the
hash function g is the same at every oracle but the spare one. `TmAtVRAV`: under `SameOffSpare` the
verifier's value over the one family is its value over the other. `TmAtDvE`: under `SameOffSpare` at
the hash function, the evaluation of `verifyV` at `DvE` with m is its evaluation at `DvE` with m',
at every commitment, prompt, output and proof (of any make).
How they are meant to be proved. `TmAtVRAV` from `NoSpare` and `det_congr_asksIn`
(OnBytes/TypedOracleCompiler/Run/PageRunLaws.lean; no third law of that kind is typed). `TmAtDvE` from `TmAtVRAV`
and `VerifyVDetIs` at both inputs.
Limits. No theorem. That a bijective M exists which agrees with the run's writing side off the spare
oracle is not said: it is the load, and it is empty where a stand-in shares strings. Not enough for
the fast form at a family that is not `readBlocksV` of a writing side. Nothing on soundness.

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

/-- The verifier never asks the spare oracle. -/
def NoSpare : Prop :=
  ∀ (Y : Type) (lam : ℕ) (L : LHV Y) (Bd : Type) (aT : RoundSplits L.test.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (carrierV L Bd aT aL))
    (S : SeedV lam W.K L Bd aT aL) (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec) (p : Params)
    (k : KeyRootV lam L) (x : Y) (π : PrfRootV lam L aT aL),
    (VRAV W S cA r₀ p k x π).AsksIn fun o _ => o ≠ TypedOracleCompiler.Compile.Batch.OracleName.other

/-- What two writing sides read out of a hash function is the same off the spare oracle. -/
def SameOffSpare {I Y : Type} {lam K' : ℕ} {L : BatchProtocolWithLeafBody I Y} (m m' : ImplV (typedOracleFamily lam K' L) lam)
    (g : Fam (rom lam)) : Prop :=
  ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName) (q : (typedOracleFamily lam K' L).Dom o),
    o ≠ TypedOracleCompiler.Compile.Batch.OracleName.other →
    readBlocksV m g o q = readBlocksV m' g o q

/-- **(Tm) at the verifier.** -/
def TmAtVRAV : Prop :=
  ∀ (Y : Type) (lam : ℕ) (L : LHV Y) (Bd : Type) (aT : RoundSplits L.test.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (carrierV L Bd aT aL))
    (S : SeedV lam W.K L Bd aT aL) (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec) (p : Params)
    (k : KeyRootV lam L) (x : Y) (π : PrfRootV lam L aT aL)
    (m m' : ImplV (typedOracleFamily lam W.K (carrierV L Bd aT aL)) lam) (g : Fam (rom lam)),
    SameOffSpare m m' g →
    (VRAV W S cA r₀ p k x π).det (readBlocksV m g) =
      (VRAV W S cA r₀ p k x π).det (readBlocksV m' g)

/-- **(Tm) at the sheet's input**, a proposition at the section's letters. -/
def TmAtDvE : Prop :=
  ∀ (t : Tag) (cfg : List (Dig 256)) (shape : Bits) (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m m' : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (hash : Hash) (commitment : Commitment) (prompt output : List Token)
    (proof : List Token × (KeyRootV 256 LV × PrfRootV 256 LV AT ALe)),
    SameOffSpare m m' (fun _ => hash) →
    (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        commitment prompt output proof).evaluate hash =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m' enc build)
        commitment prompt output proof).evaluate hash

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.NoSpare
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.SameOffSpare
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TmAtVRAV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TmAtDvE
