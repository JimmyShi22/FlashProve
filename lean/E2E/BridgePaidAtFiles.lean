-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgePaidAtFiles.lean: three hypotheses of `yesAt_of_debts` (E2E/BridgeLink.lean), the theorem
that concludes `YesAt` on the honest run, hold at three public files Z: hp (`planOk`), hD
(`DataFits`) and hdue (`Draws.due` at every verifier randomness). hD and hdue are proved here, at
the parameters at which `accAtTied_of_debts` (E2E/BridgeLinkAtFiles.lean) asks them; hp is a field
of `LaidAt`, so no theorem is stated for it. The three theorems are stated in scope
(`InScope Z = true`), where the IOP's own test on the public files accepts
(`protocolDataWellFormed (asDescriptionFiles Z) = true`), at a description (the IOP of the proof file as written in Lean:
`F0T OnBytes.secondHashFunction Zp Np cF`, Johnson/P5J/AtTerm.lean) of which `LaidAt`
(Johnson/P5J/LaidOpens.lean) holds at Z's files. Among the fields of `LaidAt` are `planOk` (the
description's tests on the plan accept) and `data` (the description's own `data` returns D).

  `dataFits_atFiles`: `DataFits` of the description and of the proof file's rounds' data in the
    library's object at Z, `(dataAtFiles flashProveData Z).DP.at frS.P.T.a`: these data are the description's,
    as far as the views read them. This is hD
  `due_atFiles`: at every verifier randomness ρ the lists of challenges `drawsAt`, at the challenge
    kit `ckP .two`, at the same data and at the fixed plain parts `front₀ z`, `join₀ z` and
    `ByteArray.empty`, where z is `(dataAtFiles flashProveData Z).G.z₀.2`, are such as the description's rounds
    can draw (`Draws.due` returns true). This is hdue. It has one more hypothesis, hz
  `data_atFiles`: the proof file's rounds' data in the library's object at Z are D, the data that
    the description's own `data` returns

By what. Honest/ is short for Johnson/Desc/ProofFile/Honest/. `data_atFiles`: both sides are the
library's written data `Johnson.G.writtenPFull`: the object's by `AtPublicFiles.Reads.proof_data`
(E2E/ReadsAtFiles.lean), D by `LPFD.Full.laidPOf_written` (Johnson/Desc/Laid/ProofFullScope.lean) at
`LaidAt.laidPOf` (Johnson/P5T/FenceAtMg.lean). The other two are proved at D and carried over by
`data_atFiles`. `dataFits_atFiles`: `ProofFile.Honest.dataFits_of_data` (Honest/Law/Data.lean) at the
fields `data` and `planOk`. `due_atFiles`: `ProofFile.Honest.due_typed` (Honest/Law/Due.lean). Of its
hypotheses, `kinds_of_data` (Honest/Law/DataKinds.lean) proves from the field `data` those on the
data's entries and kinds, chain by chain, and hs (the first chain's last declared round can draw the
empty challenge); `kit_two` (Honest/Law/KitTwo.lean) proves the three clauses on the challenge kit
at `ckP .two`; hz is passed on. Definitions: `DataFits`, `drawsAt` (Honest/Law/StratWords.lean);
`Draws.due` (Honest/Frame.lean); `front₀`, `join₀` (OnBytes/Flat/FilesAt.lean); `ckP`
(Run/PlanPull.lean).

Hypotheses. scope: `InScope Z = true`. live: `protocolDataWellFormed (asDescriptionFiles Z) = true`. L:
`LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF`, at some data D and some r. hz, of
`due_atFiles` only: no declared round of the description's three chains asks for more non-zero
elements than elements (`drawNZ ≤ drawE` in every round's entry). In scope, under `LaidAt`, hz is a
theorem: `nonZero_atFiles` (E2E/BridgeNonZero.lean, which imports this file by way of
E2E/BridgeJoinAtFiles.lean).

Limits. Equations and tests on the description and the rounds' data: nothing on any prover. hz is
not proved here. Whether any public files meet scope, live and `LaidAt` together is not shown here.
`due_atFiles` is pointwise in the verifier randomness: nothing on how the challenges are
distributed. No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.BridgeLinkAtFiles
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.Desc.ProofFile.Honest.Law.DataKinds
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.Desc.ProofFile.Honest.Law.KitTwo

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull silP front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Tied relAt DataFits halvedAll sealPlain drawsAt)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open OnBytes.Prover (HonFit Puts)
open TypedOracleCompiler.Compile.Batch.Cms (wBC)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- The proof file's rounds' data in the library's object at Z are D, the data that the
description's own `data` returns (the field `data` of `LaidAt`). -/
theorem data_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (dataAtFiles flashProveData Z).DP.at frS.P.T.a = D :=
  (AtPublicFiles.Reads.proof_data Z scope live).trans (LPFD.Full.laidPOf_written scope L.laidPOf).symm

/-- **`DataFits` of the description and of the proof file's rounds' data in the library's object at
Z.** This is the hypothesis hD of `yesAt_of_debts`. -/
theorem dataFits_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    DataFits (F0T OnBytes.secondHashFunction Zp Np cF) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) :=
  (data_atFiles Z Zp Np cF scope live L).symm ▸ ProofFile.Honest.dataFits_of_data L.data L.planOk

/-- **At every verifier randomness the lists of challenges `drawsAt` at Z pass `Draws.due` of the
description.** This is the hypothesis hdue of `yesAt_of_debts`. hz: no declared round asks for more
non-zero elements than elements. -/
theorem due_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hz : ∀ d ∈ (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.1 ++ (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE) :
    ∀ ρ, (drawsAt (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ).due
        (F0T OnBytes.secondHashFunction Zp Np cF) = true := by
  have k := ProofFile.Honest.kinds_of_data L.data
  have h : ∀ ρ, (drawsAt (ckP .two) D (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty ρ).due (F0T OnBytes.secondHashFunction Zp Np cF) =
        true :=
    fun ρ => ProofFile.Honest.due_typed (ckP .two) ProofFile.Honest.kit_two D _ _ _ k.1 k.2.1 k.2.2.1 hz
      k.2.2.2 ρ
  exact (data_atFiles Z Zp Np cF scope live L).symm ▸ h

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.data_atFiles
#print axioms AtPublicFiles.AtFiles.dataFits_atFiles
#print axioms AtPublicFiles.AtFiles.due_atFiles
