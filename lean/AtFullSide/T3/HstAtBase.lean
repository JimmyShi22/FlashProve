-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/HstAtBase.lean: the fields hst and input of RowDebtsP at the base.

1.  hst_at_base: at an input of the base's relation every declared stored table has a column of its
    width at every position below its length: the columns are the committer's at item 0.
2.  input_at_base: the index is in range, from a premise that the request has a trace.
3.  traced_at_base: that premise, from traceWhereServed_at_servedRequest at the term; so input_at_base_whole has none.
4.  Nothing here says anything of a run.
-/
import AtFullSide.Honest.CommittedColumnsAtMaker
import E2E.BridgePaidAtFiles
import E2E.RoadPublicRows
import Johnson.T3.OwedThru
import AtFullSide.T3.OnlineThruAtTerm
import VerifiableInference.Final.ModelTieAtFiles
import Johnson.HonestTrace.Joint.JointMeetsTerm

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Bridge AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (AtHonest OnlineProverWithDescription Sides Cells relAt imageRel)
open ProofFile.Honest.Term (tableCoins matrixInput committedColumns_atFilling)
open AtPublicFiles.AtZero (itemsZero_of_data)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open VerifiableInference.Desc (Chain)
open P5J

local instance (priority := high) hstAtBasePad : Nonempty PadZ := pads_nonempty frS 402653181

variable (files : PublicFiles) {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place}
  {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}

/-- The base's relation at the served requests. -/
abbrev BaseRel (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop :=
  imageRel id (tableCoins files)
    (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)

/-- **The field hst of RowDebtsP at the base.** -/
theorem hst_at_base (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    ∀ w₀ rc xi, BaseRel files hr w₀ rc xi →
      ∀ d ∈ A.F.roundsDeclaredByBlocks.1 ++ A.F.roundsDeclaredByBlocks.2.1 ++ A.F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
        ∀ y, y < 2 ^ t.sh.a → ∃ u, A.H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W := by
  rintro w₀ rc xi ⟨w, ρ, -, rfl, rfl⟩ d hdd t ht y hy
  have L := hd.laid
  rw [hd.isTerm.2] at hdd
  have hI : t.item = 0 := itemsZero_of_data L.data d hdd t ht
  have hW : t.sh.W = 2 ^ frS.P.v := width_atFiles files A.Z Np cF scope L d hdd t ht
  have hF := dataFits_atFiles files A.Z Np cF scope live L
  have hA : t.sh.a = frS.P.T.a :=
    (((F0T OnBytes.secondHashFunction A.Z Np cF).planOk_ok).1 L.planOk).depth d hdd t ht |>.trans hF.depth.symm
  rw [hA] at hy
  have hc := committedColumns_atFilling files scope OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    ProofFile.Honest.openHonest hd.made w ρ t.item y
  refine ⟨(colF (AZ files) PadZ (holdZ files) w ρ ⟨y, hy⟩).map OnBytes.Slice.ofF, ?_, ?_⟩
  · refine hc.symm.trans ?_
    simp only [ProofFile.Honest.Committer.columnsAt, hI, beq_self_eq_true, if_true]
    show ((if h : y < 2 ^ frS.P.T.a then some (colF (AZ files) PadZ (holdZ files) w ρ ⟨y, h⟩)
      else none).map (List.map OnBytes.Slice.ofF)) = _
    rw [dif_pos hy]
    rfl
  · rw [hW, List.length_map]
    unfold colF
    rw [List.length_ofFn]

/-- Where a matrix is in the index's range, the prover's test on the range says yes. -/
theorem matrixInRange_of_flat {M : FullSizeMatrix} (h : VerifiableInference.OnPublicFiles.Flat.InRange M) :
    matrixInput.inRange M = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf M).isSome = true
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf
  simp [h]

/-- **The field input of RowDebtsP at the base.** The index is in range; the trace is a premise. -/
theorem input_at_base {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more)
    (traced : ∀ w₀ rc xi, BaseRel files hr w₀ rc xi → (A.H.trace w₀ xi).isSome = true) :
    ∀ w₀ rc xi, BaseRel files hr w₀ rc xi →
      A.H.inRange w₀ = true ∧ (A.H.trace w₀ xi).isSome = true := by
  intro w₀ rc xi h
  refine ⟨?_, traced w₀ rc xi h⟩
  obtain ⟨w, ρ, ⟨s, x', -, hs⟩, rfl, -⟩ := h
  have hin : A.H.inRange = baseFilling.inRange :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit => A₀.H.inRange)
      (ProofFile.Honest.eq_ofFill hd.made)
  rw [hin]
  exact matrixInRange_of_flat (Seam.served_inRange_gen files hr committerCoinCountLessOne _ _ hs)

/-- **The trace is there at every input of the base's relation.** traceWhereServed_at_servedRequest at the term's return,
read through: the term's trace at w is the base's at w. -/
theorem traced_at_base (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    ∀ w₀ rc xi, BaseRel files hr w₀ rc xi → (A.H.trace w₀ xi).isSome = true := by
  rintro w₀ rc xi ⟨w, ρ, ⟨s, x', rfl, hs⟩, rfl, -⟩
  have made : ProofFile.Honest.Term.onlineMaker files =
      .ok (A.thru id (tableCoins files) matrixInput.dummy) :=
    ProofFile.Honest.atPure_through id (tableCoins files) matrixInput.dummy hd.made dummy_inRange
  exact (HonestTraceRun.Meets.traceWhereServed_at_servedRequest scope hr live made w x' _ hs).2

/-- **The field input of RowDebtsP at the base, whole.** -/
theorem input_at_base_whole (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) :
    ∀ w₀ rc xi, BaseRel files hr w₀ rc xi →
      A.H.inRange w₀ = true ∧ (A.H.trace w₀ xi).isSome = true :=
  input_at_base files hr hd (traced_at_base files scope live hr hd)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.traced_at_base
#print axioms VerifiableInference.Compilation.input_at_base_whole
#print axioms VerifiableInference.Compilation.hst_at_base
#print axioms VerifiableInference.Compilation.matrixInRange_of_flat
#print axioms VerifiableInference.Compilation.input_at_base
