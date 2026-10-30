-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ProverThrough.lean: the proofs of the twenty-one statements of
Johnson/FrontRoad/ProverThroughSpec.lean: a prover of the frame read through a partial map on its
index and a map on its randomness; the pinned part is its own image; the pin's clauses on the
halves, and the pin, go over to the images; a condition on the elder prover's trace function,
TraceCellsAt, gives CellsOwnAt of the image.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The twenty-one proofs   lift_quietStop, smallStop_through, pinned_part_through, find_through,
      halves_through, pin_through, through_at_some, ixOr_at_some, through_at_none,
      tests_refuse_at_none, readyShared_refuses_at_none, ready_refuses_at_none,
      traceCells_of_answers, cellsOwn_through, model_traceCells, const_not_traceCells,
      through_trace_modelAt, through_trace_viaIndex, matrixOf_in_range, index_stop_moves,
      default_is_read.

How it fits. The first three hold by unfolding: the quiet part's one move says a constant and hands
on its own state, and smallStop reads its input through askOfInput
(Johnson/Desc/ProofFile/Honest/K8/Part.lean), which reads the trace alone. tests_refuse_at_none goes
by the text of readyTests; ready_refuses_at_none by it and ready_ok
(Johnson/Desc/ProofFile/Honest/Law/Run.lean). cellsOwn_through: a matrix that holds an index has it
as indexOf's answer (indexOf_eq, sealed), and the written instance of a typed request reads as that
request's own instance (ProofFile.instOf_at_frame). All limits: the head of
Johnson/FrontRoad/ProverThroughSpec.lean. Not one of the release's goal statements.
-/
import Johnson.FrontRoad.ProverThroughSpec
import Johnson.FrontRoad.PinPublic
import Johnson.FrontRoad.CellsOwnAt
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC matsOf cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Common Cells State)
open ProofFile.Honest.K8 (smallStop)
open ProofFile.Honest.K9 (quietStop)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_proverThrough : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_proverThrough {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

theorem lift_quietStop : Spec.lift_quietStop := by
  intro V V' W W' X see wit h sh
  rfl

theorem smallStop_through : Spec.smallStop_through := by
  intro W₀ W₀' Rc Rc' Xi Tr' ix dflt rd cells P v
  rfl

theorem pinned_part_through : Spec.pinned_part_through := by
  intro W₀ W₀' Rc Rc' Xi Tr' X ix dflt rd cells P sh
  rfl

theorem find_through : Spec.find_through := by
  intro W₀ W₀' Rc Rc' Xi Tr' X ix dflt rd hs a
  rw [List.find?_map]
  rfl

theorem halves_through : Spec.halves_through := by
  intro S Cl W₀ W₀' Rc Rc' Xi Tr' X ix dflt rd par cells hs bs h b hb
  have h' := h b hb
  cases hq : par b.place with
  | none =>
    rw [hq] at h'
    intro g hg p hp
    rw [find_through] at hg
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hg
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.1 hp
    have h2 := h' g0 hg0 p0 hp0
    exact ⟨fun u l o => h2.1 (localThrough ix dflt rd u) l o, h2.2⟩
  | some P =>
    rw [hq] at h'
    obtain ⟨g, hg, hparts⟩ := h'
    refine ⟨halfThrough ix dflt rd g, ?_, ?_⟩
    · rw [find_through, hg]
      rfl
    · show g.parts.map (partThrough ix dflt rd) = _
      rw [hparts]
      rfl

theorem pin_through : Spec.pin_through := by
  intro S Cl W₀ W₀' Rc Rc' Xi Tr' X ix dflt rd par cells hs bs h
  have h2 := (pin_iff par cells hs bs).1 h
  exact (pin_iff par cells _ bs).2 ⟨h2.1, halves_through ix dflt rd par cells hs bs h2.2⟩

theorem through_at_some : Spec.through_at_some := by
  intro W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X ix dflt rd d H' w i h
  refine ⟨fun rc a b => ?_, fun ξ => ?_, ?_⟩
  · show ((ix w).bind fun i => H'.stored i (rd rc) a b) = _
    rw [h]
    rfl
  · show ((ix w).bind fun i => H'.trace i ξ) = _
    rw [h]
    rfl
  · show ((ix w).map H'.inRange).getD false = _
    rw [h]
    rfl

theorem through_at_none : Spec.through_at_none := by
  intro W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X ix dflt rd d H' w h
  refine ⟨fun rc a b => ?_, fun ξ => ?_, ?_⟩
  · show ((ix w).bind fun i => H'.stored i (rd rc) a b) = _
    rw [h]
    rfl
  · show ((ix w).bind fun i => H'.trace i ξ) = _
    rw [h]
    rfl
  · show ((ix w).map H'.inRange).getD false = _
    rw [h]
    rfl

theorem ixOr_at_some : Spec.ixOr_at_some := by
  intro W₀ W₀' ix dflt w i h
  unfold ixOr
  rw [h]
  rfl

theorem tests_refuse_at_none : Spec.tests_refuse_at_none := by
  intro W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X ix dflt rd d H' F B w h ht
  have hf := (through_at_none ix dflt rd d H' w h).2.2
  unfold ProofFile.Honest.readyTests at ht
  split at ht
  · cases ht
  split at ht
  · cases ht
  split at ht
  · cases ht
  split at ht
  · cases ht
  split at ht
  · cases ht
  rename_i h5
  rw [hf] at h5
  exact h5 rfl

theorem readyShared_refuses_at_none : Spec.readyShared_refuses_at_none := by
  intro W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X ix dflt rd d H' F B w rc ky c₀ h l hl
  unfold ProofFile.Honest.readyShared at hl
  cases ht : ProofFile.Honest.readyTests F B (proverThrough ix dflt rd d H') w with
  | error e =>
    rw [ht] at hl
    cases hl
  | ok u => exact tests_refuse_at_none ix dflt rd d H' F B w h ht

theorem ready_refuses_at_none : Spec.ready_refuses_at_none := by
  intro W₀ W₀' Rc Rc' Xi Ky Tr' X₀ X ix dflt rd d H' F B w rc x c h R hR
  exact tests_refuse_at_none ix dflt rd d H' F B w h (ProofFile.Honest.ready_ok hR).1

theorem traceCells_of_answers : Spec.traceCells_of_answers := by
  intro Tr' X cells' trace h i ξ tr x ht hx _
  obtain ⟨x1, hx1, -, hc⟩ := h i ξ tr ht
  rw [hx] at hx1
  obtain rfl := Option.some.inj hx1
  exact hc

theorem cellsOwn_through : Spec.cellsOwn_through := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Rc' Tr' X₀ Xh B G H' Yes dflt rd d cells' hc n w a _ tr
    htr s x' i e' _ hi T
  have hix : VerifiableInference.OnPublicFiles.Flat.indexOf w.1 = some i :=
    VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl hi
  have h2 : ((VerifiableInference.OnPublicFiles.Flat.indexOf w.1).bind fun i =>
      H'.trace i (LPFD.Full.instanceAsPlainRecord a)) = some tr := htr
  rw [hix] at h2
  exact hc i _ tr x'.val h2 (by rw [e', ProofFile.instOf_at_frame]) T

theorem model_traceCells : Spec.model_traceCells := by
  intro Tr' X cells' e hE i ξ tr x ht hx _
  obtain ⟨T0, hT0, rfl⟩ := Option.map_eq_some_iff.1 ht
  obtain ⟨x1, hx1, -, rfl⟩ := hinge_modelTrace X i ξ T0 hT0
  rw [hx] at hx1
  obtain rfl := Option.some.inj hx1
  exact hE _

theorem const_not_traceCells : Spec.const_not_traceCells := by
  intro Z Zp Np cF scope pp hr live D r L Tr' cells' t₀ h₀ h
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have hX := publicOf_laid Z Zp Np cF L
  have e1 := h i
    (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) t₀
    x'.val rfl (ProofFile.instOf_at_frame _) T
  exact cells129_ne (OnBytes.HonestTrace.partsFit_in_scope scope hr hX) _
    (meetsAll_theTrace scope hr hX T).small (h₀.symm.trans e1)

theorem through_trace_modelAt : Spec.through_trace_modelAt := by
  intro Rc Rc' Ky Tr' X₀ X Xp e H₀ dflt rd d
  funext m ξ
  show ((VerifiableInference.OnPublicFiles.Flat.indexOf m).bind fun i => (modelTrace Xp i ξ).map e) =
    ((VerifiableInference.OnPublicFiles.Flat.indexOf m).bind fun i => modelTrace Xp i ξ).map e
  cases VerifiableInference.OnPublicFiles.Flat.indexOf m <;> rfl

theorem through_trace_viaIndex : Spec.through_trace_viaIndex := by
  intro Rc Rc' Xi Ky X₀ X H' dflt rd d
  rfl

theorem matrixOf_in_range : Spec.matrixOf_in_range := by
  intro Rc Rc' Xi Ky Tr' X₀ X H' dflt rd j
  exact (through_at_some VerifiableInference.OnPublicFiles.Flat.indexOf dflt rd _ H' _ j
    (VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
      (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf j))).2.2

theorem index_stop_moves : Spec.index_stop_moves := by
  intro Rc Xi Tr' X sh rc x tr e
  have e2 := congrArg (fun q : ProofFile.Honest.Part (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X =>
    q.hid ⟨true, rc, x, tr⟩ [] []) e
  have e3 : (none : Option String) = some "" := e2
  cases e3

theorem default_is_read : Spec.default_is_read := by
  intro Rc Xi Tr' X sh rc x tr
  rfl

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_proverThrough
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_proverThrough
#print axioms OnBytes.FrontRoad.lift_quietStop
#print axioms OnBytes.FrontRoad.smallStop_through
#print axioms OnBytes.FrontRoad.pinned_part_through
#print axioms OnBytes.FrontRoad.find_through
#print axioms OnBytes.FrontRoad.halves_through
#print axioms OnBytes.FrontRoad.pin_through
#print axioms OnBytes.FrontRoad.through_at_some
#print axioms OnBytes.FrontRoad.through_at_none
#print axioms OnBytes.FrontRoad.ready_refuses_at_none
#print axioms OnBytes.FrontRoad.cellsOwn_through
#print axioms OnBytes.FrontRoad.index_stop_moves
#print axioms OnBytes.FrontRoad.ixOr_at_some
#print axioms OnBytes.FrontRoad.tests_refuse_at_none
#print axioms OnBytes.FrontRoad.readyShared_refuses_at_none
#print axioms OnBytes.FrontRoad.traceCells_of_answers
#print axioms OnBytes.FrontRoad.model_traceCells
#print axioms OnBytes.FrontRoad.const_not_traceCells
#print axioms OnBytes.FrontRoad.through_trace_modelAt
#print axioms OnBytes.FrontRoad.through_trace_viaIndex
#print axioms OnBytes.FrontRoad.matrixOf_in_range
#print axioms OnBytes.FrontRoad.default_is_read
