-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeetsD.lean

Nothing on hiding. No property of the protocol is claimed.
"laws_of_readyInput" (Johnson/HonestTrace/ReadyAtFullIn.lean) CARRIED FROM A FILLING
OVER Cm.Idx WHOSE TRACE IS fullIn's TO ANY FILLING OVER THE MATRICES (AtPublicFiles.AtFiles.FullSizeMatrix) WHOSE TRACE IS fullIn's READ
THROUGH THE INDEX THAT THE MATRIX HOLDS (indexOf): the premise hT is the field "trace" of "matrixInput"
(E2E/TheHonestProver.lean), to the letter, and the same as serves_at_plug's. The types of the randomness and of the two sides are letters.
What turns against the law at Cm.Idx: the index is no longer the input's own w₀ (that is a matrix): it is the
index that the matrix w₀ holds, said twice: "indexOf v.w₀ = some i" and "Holds v.w₀ i".
MAY HOLD EMPTILY, as the law at Cm.Idx: no input is shown here to meet ReadyInput, and that onlineProverFromPublicFiles returns at
such a filling is a premise. The trace reads the private input: no public fact, nothing that a simulator has.
The executable model's trace and the statements that tie it to the specification are not used:
not imported.
"To the letter" was held by reading, against the fields of "matrixInput" in
E2E/TheHonestProver.lean. This file does not import that file, so Lean does not guard it here; at
the term "onlineFilling_fields" (JointMeets.lean) does.
-/
import Johnson.HonestTrace.ReadyAtFullIn
import E2E.ObjectAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open OnBytes.HonestTrace
open Inst.Model
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Cells OnlineProverParts OnlineProverWithDescription onlineProverFromPublicFiles fullIn ReadyInput Local)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open VerifiableInference.OnPublicFiles.Flat (indexOf Holds)

/-- What "indexOf" returns is held. (Kin: "holds_of_indexOf", Johnson/Goal/Meaning/NextToken.lean.) -/
theorem holds_of_indexOf_some {M : FullSizeMatrix} {i : Cm.Idx} (h : indexOf M = some i) : Holds M i := by
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf at h
  split at h
  · rename_i hin
    obtain rfl := Option.some.inj h
    exact hin.choose_spec
  · cases h

section Ready
variable {Rc X₀ Xo : Type} {P : OnlineProverParts FullSizeMatrix Rc Cells X₀ Xo} {A : OnlineProverWithDescription FullSizeMatrix Rc Cells X₀ Xo}

/-- **The way out over the matrices, no scope**: "cells_of_readyInput" carried. At an input that meets
"ReadyInput" the matrix w₀ holds an index i, the input's bytes are read as an instance x that i serves, and
the input's trace is "theTrace" at i and x, read by "cellOf". It spends the third clause of "ReadyInput"
alone. -/
theorem cells_of_readyInput_over_matrices {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (hT : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {Fd : FileDescription ProofFile.Inst} {v : Local FullSizeMatrix Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), indexOf v.w₀ = some i ∧ Holds v.w₀ i ∧
      ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X i x ∧
      v.trace = ⟨cellOf A.Z.p.X (theTrace A.Z.p.X i x)⟩ := by
  have h : ((indexOf v.w₀).bind fun i => fullIn.trace A.Z i v.x) = some v.trace := by
    have e : A.H.trace v.w₀ v.x = some v.trace := hv.2.2
    rw [ProofFile.Honest.atPure_trace hA, hT] at e
    exact e
  obtain ⟨i, hi, ht⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, hx, hs, hc⟩ := ProofFile.Honest.fullIn_trace_some ht
  exact ⟨i, x, hi, holds_of_indexOf_some hi, hx, hs, hc⟩

/-- The set-up function's return, out of the return of "onlineProverFromPublicFiles": "pub_of_atPure" at the matrices. -/
theorem pub_of_atPure_over_matrices {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) : ProofFile.pureRoad.pub o pol lay KL = .ok A.Z := by
  exact (ProofFile.Honest.atPure_ok hA).1

variable {F : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy}

/-- **THE LAW THAT K8 ASKS FOR: "laws_of_readyInput" over the matrices, in scope.** Moreover, of that
trace: "MeetsAll" (among its fields: every entry is below 129 in absolute value), "BorrowedSame",
"NamesFit"; of the public part "PartsFit" and "PlanMarks". -/
theorem laws_of_readyInput_over_matrices (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A)
    {Fd : FileDescription ProofFile.Inst} {v : Local FullSizeMatrix Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), indexOf v.w₀ = some i ∧ Holds v.w₀ i ∧
      ProofFile.instOf v.x = some x ∧ ServesAt A.Z.p.X i x ∧
      v.trace = ⟨cellOf A.Z.p.X (theTrace A.Z.p.X i x)⟩ ∧
      MeetsAll A.Z.p.X i x (theTrace A.Z.p.X i x) ∧
      BorrowedSame A.Z.p.X (theTrace A.Z.p.X i x) ∧
      NamesFit A.Z.p.X (theTrace A.Z.p.X i x) ∧ PartsFit A.Z.p.X ∧ PlanMarks A.Z.p.X := by
  obtain ⟨i, x, hi, hh, hx, hs, hc⟩ := cells_of_readyInput_over_matrices hT hA hv
  have B := publicInScope_of_pub hC hF (pub_of_atPure_over_matrices hA)
  have M := meetsAll_theTrace B.scope B.reads B.pub hs
  exact ⟨i, x, hi, hh, hx, hs, hc, M, borrowedSame_of_meetsAll M,
    namesFit_theTrace B.scope B.reads B.pub hs, partsFit_in_scope B.scope B.reads B.pub,
    planMarks_in_scope B.scope B.reads B.pub⟩

/-- The same at the letters of an opening of the maker ("IM.Open"): "laws_of_readyInput_open" carried. -/
theorem laws_of_readyInput_open_over_matrices (hC : VerifierAndGoals.InScope F = true)
    (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hT : P.trace = fun Zq M ξ => (indexOf M).bind fun i => fullIn.trace Zq i ξ)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction F.pol F.lay F.KL P = .ok A)
    {Fo : FileDescription ProofFile.Inst} {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {As : ProofFile.SharedSeat} {Bsec : ProofFile.SecondSeat}
    (O : IM.Open OnBytes.secondHashFunction F.pol F.lay F.KL Fo Zp Bs base c As Bsec)
    {Fd : FileDescription ProofFile.Inst} {v : Local FullSizeMatrix Rc ProofFile.Inst Cells} (hv : ReadyInput Fd A.H v) :
    ∃ (i : Cm.Idx) (x : Instance ppref), indexOf v.w₀ = some i ∧ Holds v.w₀ i ∧
      ProofFile.instOf v.x = some x ∧ ServesAt Zp.p.X i x ∧
      v.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ∧
      MeetsAll Zp.p.X i x (theTrace Zp.p.X i x) ∧
      BorrowedSame Zp.p.X (theTrace Zp.p.X i x) ∧
      NamesFit Zp.p.X (theTrace Zp.p.X i x) ∧ PartsFit Zp.p.X ∧ PlanMarks Zp.p.X ∧
      Bs.G₀.W = Zp.p.X := by
  obtain rfl : A.Z = Zp := Except.ok.inj ((ProofFile.Honest.atPure_ok hA).1.symm.trans O.pub)
  have hW : Bs.G₀.W = A.Z.p.X := O.W
  obtain ⟨i, x, hi, hh, hx, hs, hc, M, Bo, N, Pf, Pm⟩ :=
    laws_of_readyInput_over_matrices hC hF hT hA hv
  exact ⟨i, x, hi, hh, hx, hs, hc, M, Bo, N, Pf, Pm, hW⟩

end Ready

end HonestTraceRun.Meets

#print axioms HonestTraceRun.Meets.holds_of_indexOf_some
#print axioms HonestTraceRun.Meets.cells_of_readyInput_over_matrices
#print axioms HonestTraceRun.Meets.pub_of_atPure_over_matrices
#print axioms HonestTraceRun.Meets.laws_of_readyInput_over_matrices
#print axioms HonestTraceRun.Meets.laws_of_readyInput_open_over_matrices
