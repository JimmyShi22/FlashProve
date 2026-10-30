-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/AtNamedFiles.lean: zero knowledge of the protocol's honest provers at the named sets of public files: the stored full-size example and the same files with the other
acceptance policy. The premises on the files are theorems here. No value of any other premise is given here: this file proves zero knowledge of nothing.
-/
import AtFullSide.T3.OnlineThruAtTerm
import AtFullSide.E2E.AtWrittenFiles
import AtFullSide.K12.MakerReturnsAtLive
import Johnson.P5J.HeadOfLive

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides relAt AtHonest OnlineProverWithDescription Cells)
open ProofFile.Honest.Term (tableCoins matrixInput)
open VerifiableInference.Desc (Chain)
open Compile.Lifetime (SimOf)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles NamedFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) atNamedPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) atNamedValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) atNamedDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- The named files are in scope, with a live description. -/
theorem named_open (named : NamedFiles files) :
    InScope files = true ∧ protocolDataWellFormed (asDescriptionFiles files) = true := by
  rcases named with rfl | rfl
  · exact AtPublicFiles.AtWritten.open_zFull
  · exact AtPublicFiles.AtWritten.open_zGap

/-- The named files are read. -/
theorem named_read (named : NamedFiles files) : ∃ pp, readFiles files = .ok pp := by
  rcases named with rfl | rfl
  · obtain ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
    exact ⟨pp, hr⟩
  · obtain ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
    exact ⟨pp, hr⟩

/-- **Zero knowledge of the protocol's honest provers at the named files**: an implication. -/
theorem zeroKnowledgeOnServedRequests_atNamedFiles {zHid a : ℝ≥0∞} (named : NamedFiles files)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    (owns : G.owns = true)
    (hid : HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a) zHid)
    (parts : Parts files) (offlineSimulator : SimOf (protocolAtFiles files).offline)
    (offlineTable : ∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r)
    (offline : ExactOutsideStops (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
      offlineSimulator)
    (offlineStops : PrivateStopsAtMost (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline a) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) a 0 zHid :=
  zeroKnowledgeOnServedRequests_fromTheBase files (named_open named).1 (named_open named).2 hr hd debts
    owns hid parts offlineSimulator offlineTable offline offlineStops

/-- The maker returns at the base filling, where the head AtMgA holds. -/
theorem base_returns {Z : PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ A, ProofFile.Honest.onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFilling = .ok A ∧ A.Z = Zp := by
  obtain ⟨A, hA, e, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h hl matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref ProofFile.Honest.openHonest ProofFile.Honest.Term.range_matrixInput
  exact ⟨A, hA, e⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.named_open
#print axioms VerifiableInference.Compilation.named_read
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atNamedFiles
#print axioms VerifiableInference.Compilation.base_returns
