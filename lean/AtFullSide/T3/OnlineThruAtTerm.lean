-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/OnlineThruAtTerm.lean: zero knowledge of the protocol's honest provers from the base filling: the rows, the invariants and On at the filling that the
online prover reads through. Owed at the base; read through once; the committer's key and columns; the online clause at the term. No value of
any premise is given here: this file proves zero knowledge of nothing.
-/
import Johnson.T3.OnlineThru
import Johnson.T3.OnlineAtTheTerm
import Johnson.Desc.ProofFile.Honest.ThruAtPure
import Johnson.Flat.CodingCells
import AtFullSide.Honest.CommittedColumnsAtMaker
import E2E.CompleteAsIOPWorkBits
import Johnson.HonestTrace.Joint.TwoIndicesServeOneRequest

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides relAt AtHonest OnlineProverWithDescription OnlineProverParts Cells)
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open VerifiableInference.Desc (Chain)
open Compile.Lifetime (SimOf)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) onlineThruPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) onlineThruValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) onlineThruDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable (files : PublicFiles)

/-- **The filling that the online prover reads through**: the inner term of E2E/TheHonestProver.lean. -/
abbrev baseFilling : OnlineProverParts FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit :=
  ProofFile.Honest.onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest

/-- The named member of the range is in range. -/
theorem dummy_inRange : (baseFilling).inRange (id matrixInput.dummy) = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf (VerifiableInference.OnPublicFiles.Flat.matrixOf
          ProofFile.Honest.fullIn.dummy)).isSome = true
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf
  rw [dif_pos ⟨_, VerifiableInference.OnPublicFiles.Flat.holds_matrixOf _⟩]
  rfl

/-- **The base head's one further test**, as at the term. -/
def baseAsks (A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit) : List (String × Bool) :=
  [("a half stands at every sub-protocol that declares an item", ProofFile.Honest.halvedAll A.F A.H)]

/-- Two indices in range serve one request, for public files in scope. -/
theorem twoIndices_holds (scope : InScope files = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) : TwoIndicesServeOneRequest files hr :=
  OnBytes.HonestTrace.TwoIndicesServe.twoIndicesServeOneRequest files scope hr

/-- **Zero knowledge of the protocol's honest provers from the base**: an implication. -/
theorem zeroKnowledgeOnServedRequests_fromTheBase {zHid a : ℝ≥0∞}
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
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
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) a 0 zHid := by
  have made : onlineMaker files = .ok (A.thru id (tableCoins files) matrixInput.dummy) := by
    exact ProofFile.Honest.atPure_through id (tableCoins files) matrixInput.dummy hd.made dummy_inRange
  obtain ⟨Bs, base, O⟩ := hd.laid.opened
  have e := onlineProver_of_seat files made hd.laid.places (ToldDesc.pureChainAt_of_open O)
  unfold honestProvers
  rw [e] at hid ⊢
  exact zeroKnowledgeOnServedRequests_of_base files A.Z Np cF runValueBytes runValueBytes id
    (tableCoins files) matrixInput.dummy scope live hr hd debts
    (ProofFile.Honest.range_alike id matrixInput.dummy hd.made dummy_inRange) (ProofFile.Honest.imageRel_of id (tableCoins files)) (ProofFile.Honest.key_of_atPure hd.made).symm
    (fun w rc _ _ => ProofFile.Honest.Term.committedColumns_atFilling files scope OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref ProofFile.Honest.openHonest hd.made w rc) owns hid
    (workFaithful_atFiles files) (twoIndices_holds files scope hr) _ offlineSimulator offlineTable offline offlineStops

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.dummy_inRange
#print axioms VerifiableInference.Compilation.twoIndices_holds
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_fromTheBase
