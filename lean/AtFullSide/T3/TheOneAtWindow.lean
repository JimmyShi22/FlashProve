-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/TheOneAtWindow.lean: ZERO KNOWLEDGE ON SERVED REQUESTS WITH THE BOUND ON THE ONLINE PRIVATE STOPS GIVEN: AN IMPLICATION.

1.  The number 2^-174 comes from window_at_term.
2.  Read it beside completeness, at the same return and the same rows G. On is asked only at parts that a run has
    called, and Good at letters that never hold, so a prover whose early block is always refused would meet all
    later rows with nothing shown. Completeness at the same G is what rules that out; this file does not show it.
3.  _start and _whole are guards: no proof in this file uses them.
4.  The premises on the rows are listed in the statement: this file proves zero knowledge of nothing.
-/
import AtFullSide.T3.TheOneTheorem
import Johnson.P1K8R.WindowAtTerm

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides Owed relAt AtHonest OnlineProverWithDescription Cells)
open ProofFile.Honest.Term (tableCoins onlineMaker matrixInput)
open VerifiableInference.Desc (Chain)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) oneWindowPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) oneWindowValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) oneWindowDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- A lemma toward zeroKnowledgeOnServedRequests_ofSides: the statement with the online private stops
at 2^-174. -/
theorem zeroKnowledgeOnServedRequests_atTheWindow
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) :=
  have made : onlineMaker files = .ok (A.thru id (tableCoins files) matrixInput.dummy) :=
    ProofFile.Honest.atPure_through id (tableCoins files) matrixInput.dummy hd.made dummy_inRange
  zeroKnowledgeOnServedRequests_atTheNumber scope live hr hd debts
    (AtPublicFiles.AtFiles.HonestTerm.window_at_term scope hr live made) _start parts _whole

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheWindow
