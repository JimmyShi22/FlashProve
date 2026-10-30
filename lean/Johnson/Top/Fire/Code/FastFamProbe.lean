-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/FastFamProbe.lean: a family of typed oracle functions that is made for a run
may stand in the fast form of `verifyV` (`fastF`, VerifyVFastD.lean | VerifyVFastDS.lean), and what
then runs is still the evaluation of `verifyV`. The like for `fastD`:
FastDProbe.lean.
Why. `fastD` is `fastF` over `readBlocksV m fun _ => hash`: there a block of an answer is a function
of its number and a digest a function of a bit's number: nothing that is read is kept, and every bit
that is read makes the block's string and its hash anew.
Main names. `hashOf O`: the hash function on bit strings that a function O from bytes to bytes makes
(`gOf`, OnBytes/TypedOracleCompiler/Run/PageRunFast.lean). `ReadsAs m O Ff`: at every oracle and query the family Ff
answers what the writing side m reads out of `gOf O`. `fastF_reads_is_verifyV` (at the full and at
the small size): under `ReadsAs m O Ff`, `fastF` over Ff at `hashOf O` is the evaluation, at `hashOf
O`, of `verifyV` at `DvE` with that m, and at `proofE`.
Limits. AT WHICH HASH FUNCTIONS: those of the form `hashOf O` alone: s ↦ the 256 bits of O at the
bytes of s. The format's own is one (`Run.oBits` is `gOf Fmt.oracle` by its text).
`fastD_is_verifyV` holds at every hash function; this law is narrower. AT WHICH m AND Ff: those that
meet `ReadsAs`: none is given here. As `fastD_is_verifyV`: it speaks of a proof of `proofE`'s make
alone, and the parser stands outside the equation, on both sides. Nothing on time or memory: that a
family keeps what it has read is the family's matter. It has not been run. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.FastDProbe
import Johnson.Top.Fire.Code.FastDProbeS
import OnBytes.TypedOracleCompiler.Run.PageRunFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom

/-- The hash function on bit strings that a function from bytes to bytes makes. -/
def hashOf (O : ByteArray → ByteArray) : Hash := fun s => TypedOracleCompiler.Run.PageRun.gOf O () s

/-- The family Ff answers, at every oracle and query, what m reads out of `gOf O`. -/
def ReadsAs {S : OSpec} (m : ImplV S 256) (O : ByteArray → ByteArray) (Ff : Fam S) : Prop :=
  ∀ o q, Ff o q = (m.rng o).symm fun j => TypedOracleCompiler.Run.PageRun.gOf O () (m.code o q j)

end VerifiableInference.OnPublicFiles

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

/-- **The fast form over a family made for a run is the evaluation of `verifyV`**: at every m, every
O and every family Ff that answers what m reads out of `gOf O`; at the hash function `hashOf O`; at
all further letters and all that a parser can hand over. -/
theorem fastF_reads_is_verifyV (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (O : ByteArray → ByteArray) (Ff : Fam (typedOracleFamily 256 (K + 1) CV)) (hR : ReadsAs m O Ff)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastF DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p Ff
        enc build (hashOf O) commitment prompt output aux cm rcd copy fT e fB =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e
          fB)).evaluate (hashOf O) :=
  fastF_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed
    r₀ p m Ff enc build (hashOf O) commitment prompt output aux cm rcd copy fT e fB
    (funext fun o => funext fun q => hR o q)

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

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

/-- **The fast form over a family made for a run is the evaluation of `verifyV`**: at every m, every
O and every family Ff that answers what m reads out of `gOf O`; at the hash function `hashOf O`; at
all further letters and all that a parser can hand over. -/
theorem fastF_reads_is_verifyV (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
    (pl0 pl1 : PlainPart (shapeOf CV t) (annOf CV t))
    (num : ℕ → Plains (LV).bat.loc.shape → Bool) (seed : (Fin (K + 1) → Dig 256) → (LV).Seed)
    (r₀ : (LV).Rec) (p : Params) (m : ImplV (typedOracleFamily 256 (K + 1) CV) 256)
    (enc : KeyRootV 256 LV → Option ZKCP.Str)
    (build : List Token × List Token → List Token → Option X)
    (O : ByteArray → ByteArray) (Ff : Fam (typedOracleFamily 256 (K + 1) CV)) (hR : ReadsAs m O Ff)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecSmall) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastF DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p Ff
        enc build (hashOf O) commitment prompt output aux cm rcd copy fT e fB =
      (verifyV
        (DvE DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed r₀ p
          m enc build)
        commitment prompt output
        (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e
          fB)).evaluate (hashOf O) :=
  fastF_is_verifyV DK DP runK runP rK rP sT sB early ds xs dec K salt t cfg shape pl0 pl1 num seed
    r₀ p m Ff enc build (hashOf O) commitment prompt output aux cm rcd copy fT e fB
    (funext fun o => funext fun q => hR o q)

end VerifiableInference.OnPublicFiles.SlotsBehindCutDS

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.fastF_reads_is_verifyV
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutDS.fastF_reads_is_verifyV
