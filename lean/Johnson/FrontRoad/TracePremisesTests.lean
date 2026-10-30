-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TracePremisesTests.lean: controls and negative tests for the premises on the trace
of Johnson/FrontRoad/TracePremises.lean. They count as no goal of the release: none is one of the
release's goal statements.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  constTrace, const_not_small, no_served_const   a negative test: not every entry of the constant
      trace 129 is below 129 in absolute value; and at public files in scope that can be read and
      pass protocolDataWellFormed, under LaidAt, no index and instance that it serves has that trace as its
      theTrace Zp.p.X i x (meetsAll_theTrace, Johnson/Goal/HonestTrace/FullPlanesInScope.lean). So
      the conditions of TraceSmall, TraceServed and TracePlain can fail at a trace.
  hinge_of_none   a control: the trace function that never answers meets TraceHinge
      (Johnson/HonestTrace/TraceHinge.lean), at every X and every reader. So TraceHinge goes one
      way.
  oneRequestTrace, hinge_one_request   a control that a premise holds where one might wish it did
      not: at the reader that yields one instance at every input, the trace function that ignores
      the input's written instance meets TraceHinge. So TracePlain rd and sessionStops_of_hinge tie
      the instance to the input only as far as rd does.
  via_prover   a control: a prover (a value of the structure Prover) whose trace field is viaIndex
      trace (Johnson/FrontRoad/TracePremises.lean) meets the condition of TraceThrough trace at
      every input.
  holds_inRange, no_index_no_clause   on the clause on Holds: a matrix that holds an index is in
      range; and there is a matrix at which the condition of TraceThrough fails at every trace
      function, written instance and trace, because it holds no index (exists_not_inRange,
      Johnson/Flat/MatrixOfImage.lean). So the clause can fail at a matrix. At a tied request the
      matrix is in range already (the field rel of Tied); there the clause says which index
      (holds_one).
  valid_of_served   a control: at public files in scope that can be read and pass protocolDataWellFormed, under
      LaidAt: a typed request that an index serves is in the relation RyesZ Z at the matrix of that
      index. It is valid_of_holds (Johnson/FrontRoad/TracePremises.lean) at such matrices.
  not_all_valid   a negative test: at every typed request there is a matrix at which it is not in
      the relation RyesZ Z. So the premise hY of sessionStops_of_valid fails at Yes := everything,
      where a typed request exists.
  none_meets_ownRel, none_meets_ownYes   a control: a prover whose trace function never answers
      meets TraceOwnRel and TraceOwnYes. So both go one way.
  const_fails_ownRel, const_fails_ownYes   a negative test: at public files in scope that can be
      read and pass protocolDataWellFormed, under LaidAt: a prover whose trace function answers the constant trace
      129 at one typed request in the relation (of Yes), at a matrix that holds an index which
      serves it, does not meet TraceOwnRel (TraceOwnYes). So both can fail.
  ownYes_at_nothing   a control: at Yes := nothing every prover meets TraceOwnYes. With
      const_fails_ownRel: TraceOwnYes does not give TraceOwnRel, where a served typed request exists
      at which the trace function answers so.
  model_is_model, model_meets_ownRel, model_meets_own, model_answers   a control: a prover whose
      trace field is viaIndex (modelTrace Zp.p.X) (Johnson/FrontRoad/TracePremises.lean) meets
      TraceIsModel by definition, TraceOwnRel, and TraceOwn at all rows and every Yes; and at the
      matrix of an index and the written instance of a typed request that the index serves it
      answers theTrace there. So these premises can be met by a trace function that answers wherever
      an index serves a typed request.
  none_fails_model, const_fails_own   two negative tests. A prover whose trace function never
      answers does not meet TraceIsModel, where an index serves a typed request. At public files in
      scope that can be read and pass protocolDataWellFormed, under LaidAt: a prover whose trace function answers
      the constant trace 129 at one typed request of Yes and the input's own seed, at a matrix that
      holds an index which serves it, does not meet TraceOwn (by ownYes_of_own). So both can fail.

How it fits. The controls show that a premise or its condition can be met, the negative tests that
it can fail. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean.

Limits.
  Nothing here is said of any prover that runs. via_prover, model_meets_ownRel and the like are
      structure updates at a variable prover: each proves one premise or condition alone, not that
      premise together with the other premises of an implication of
      Johnson/FrontRoad/SessionStopsOfTrace.lean. modelTrace, viaIndex and oneRequestTrace are
      noncomputable. That acceptance, or any other premise of the implication on index privacy,
      holds at a prover with the trace field viaIndex (modelTrace Zp.p.X) is not proved.
  That a served typed request exists is not proved here; it is servedTyped_exists
      (Johnson/FrontRoad/ServedExists.lean), which has a twin of each of these tests without that
      condition. valid_of_served, the three tests const_fails, none_fails_model and model_answers
      say something only where one exists; not_all_valid only where a typed request exists.
  A prover whose trace function never answers does not meet the premise hR of these implications
      (ready refuses where the request has no trace, Johnson/Desc/ProofFile/Honest/Frame.lean; by
      inspection, not proved).
  That a premise on the trace cannot be dropped from these implications is not proved: it would need
      a lower bound over written verifier messages (Johnson/FrontRoad/SessionStopsPinnedTests.lean,
      Limits).
  No test here proves that TraceSmall does not give TraceServed, or that TraceServed does not give
      TraceOwn. Of the five premises under AtTied, TraceOwn alone is stated as a whole in a control
      and a negative test; of the others the tests are on their conditions at a trace.
  The full size alone. theTrace and indexOf are noncomputable.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.TracePremises
import Johnson.Flat.MatrixOfImage

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
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_tracePremisesTests : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_tracePremisesTests {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- The trace whose entries are all 129. -/
def constTrace : Tr := fun _ _ _ _ => 129

/-- A negative test; it counts as no goal. Not every entry of the constant trace 129 is below 129 in
absolute value. -/
theorem const_not_small : ¬ ∀ k m r c, |constTrace k m r c| < 129 := fun h =>
  absurd (h 0 0 0 0) (by unfold constTrace; norm_num)

/-- A control; it counts as no goal. The trace function that never answers meets TraceHinge. -/
theorem hinge_of_none {Xi : Type} (X : OnBytes.Model.Verify.Public)
    (rd : Xi → Option (Instance ppref)) : TraceHinge X (fun _ _ => none) rd :=
  fun _ _ _ h => by cases h

/-- The trace function that ignores its input's written instance: at every input, the trace of one
instance x₀ where the index serves it. -/
def oneRequestTrace {Xi : Type} (X : OnBytes.Model.Verify.Public) (x₀ : Instance ppref) (i : Cm.Idx)
    (_ : Xi) : Option Tr :=
  open Classical in if ServesAt X i x₀ then some (theTrace X i x₀) else none

/-- A control; it counts as no goal. **At the reader that yields one instance x₀ at every input, the
trace function that ignores the input's written instance meets TraceHinge.** So TraceHinge ties the
instance to the input only as far as the reader does. -/
theorem hinge_one_request {Xi : Type} (X : OnBytes.Model.Verify.Public) (x₀ : Instance ppref) :
    TraceHinge X (oneRequestTrace (Xi := Xi) X x₀) (fun _ => some x₀) := by
  classical
  intro i ξ ω h
  have h' : (if ServesAt X i x₀ then some (theTrace X i x₀) else none) = some ω := h
  by_cases hs : ServesAt X i x₀
  · rw [if_pos hs] at h'
    exact ⟨x₀, rfl, hs, (Option.some.inj h').symm⟩
  · rw [if_neg hs] at h'
    cases h'

/-- A control; it counts as no goal. A prover whose trace field is viaIndex trace meets the
condition of TraceThrough trace at every input (viaIndex_holds,
Johnson/FrontRoad/TracePremises.lean). -/
theorem via_prover {Rc Ky X₀ Xh : Type} (H₀ : Prover FullSizeMatrix Rc ProofFile.Inst Ky Tr X₀ Xh)
    (trace : Cm.Idx → ProofFile.Inst → Option Tr) (m : FullSizeMatrix) (ξ : ProofFile.Inst) (tr : Tr)
    (h : ({ H₀ with trace := viaIndex trace } : Prover FullSizeMatrix Rc ProofFile.Inst Ky Tr X₀ Xh).trace m ξ =
      some tr) :
    ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds m i ∧ trace i ξ = some tr :=
  viaIndex_holds trace h

/-- A lemma; it counts as no goal. A matrix that holds an index is in range. -/
theorem holds_inRange {m : FullSizeMatrix} {i : Cm.Idx} (h : VerifiableInference.OnPublicFiles.Flat.Holds m i) :
    inRange m := ⟨i, h⟩

/-- A negative test; it counts as no goal. **There is a matrix at which the condition of
TraceThrough fails at every trace function, written instance and trace: it holds no index.** -/
theorem no_index_no_clause : ∃ m : FullSizeMatrix, ∀ (trace : Cm.Idx → ProofFile.Inst → Option Tr) (ξ : ProofFile.Inst)
    (tr : Tr), ¬ ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds m i ∧ trace i ξ = some tr := by
  obtain ⟨m, hm⟩ := VerifiableInference.OnPublicFiles.Flat.exists_not_inRange
  exact ⟨m, fun _ _ _ ⟨i, hi, _⟩ => hm ⟨i, hi⟩⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: no index and instance that it serves has the constant trace 129 as its
theTrace.** -/
theorem no_served_const (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ¬ ∃ (i : Cm.Idx) (x : Instance ppref),
      ServesAt Zp.p.X i x ∧ constTrace = theTrace Zp.p.X i x := by
  rintro ⟨i, x, T, e⟩
  refine const_not_small ?_
  rw [e]
  exact (meetsAll_theTrace scope hr (publicAt Z Zp Np cF scope hr live L) T).small

/-- A control; it counts as no goal. **At public files in scope that can be read and pass protocolDataWellFormed,
under LaidAt: a typed request that an index serves is in the relation RyesZ Z at the matrix of that
index.** -/
theorem valid_of_served (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (i : Cm.Idx) (x' : XF) (T : ServesAt Zp.p.X i x'.val) :
    RyesZ Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) x' :=
  valid_of_holds Z Zp Np cF scope hr live L _ i x'
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i) T

/-- A negative test; it counts as no goal. **At every typed request there is a matrix at which it is
not in the relation RyesZ Z.** -/
theorem not_all_valid (x' : XF) : ¬ ∀ m : FullSizeMatrix, RyesZ Z m x' := by
  obtain ⟨m, hm⟩ := VerifiableInference.OnPublicFiles.Flat.exists_not_inRange
  exact fun h => hm ((ryesZ_iff Z m x').1 (h m)).1

variable {X₀ Xh : Type}

/-- The type of the provers at Z. -/
abbrev ProverZ (Z : PublicFiles) (X₀ Xh : Type) : Type := Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh

/-- A control; it counts as no goal. A prover whose trace function never answers meets TraceOwnRel.
-/
theorem none_meets_ownRel (H₀ : ProverZ Z X₀ Xh) :
    TraceOwnRel Z Zp ({ H₀ with trace := fun _ _ => none } : ProverZ Z X₀ Xh) :=
  fun _ _ _ _ _ _ _ _ h => by cases h

/-- A control; it counts as no goal. A prover whose trace function never answers meets TraceOwnYes.
-/
theorem none_meets_ownYes (H₀ : ProverZ Z X₀ Xh) (Yes : FullSizeMatrix → XF → Prop) :
    TraceOwnYes Z Zp ({ H₀ with trace := fun _ _ => none } : ProverZ Z X₀ Xh) Yes :=
  fun _ _ _ _ _ _ _ h => by cases h

/-- A control; it counts as no goal. At Yes := nothing every prover meets TraceOwnYes. -/
theorem ownYes_at_nothing (H : ProverZ Z X₀ Xh) : TraceOwnYes Z Zp H fun _ _ => False :=
  fun _ _ _ _ hy => hy.elim

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: a prover whose trace function answers the constant trace 129 at one typed
request in the relation, at a matrix that holds an index which serves it, does not meet
TraceOwnRel.** -/
theorem const_fails_ownRel (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H : ProverZ Z X₀ Xh) (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (i : Cm.Idx)
    (hx : RyesZ Z w.1 x')
    (hi : VerifiableInference.OnPublicFiles.Flat.Holds w.1 i) (T : ServesAt Zp.p.X i x'.val)
    (ha : H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) =
      some constTrace) :
    ¬ TraceOwnRel Z Zp H :=
  fun hV => no_served_const Z Zp Np cF scope hr live L ⟨i, x'.val, T, hV w x' s i _ hx hi T ha⟩

/-- A negative test; it counts as no goal. **The like of TraceOwnYes, at one typed request of Yes
and the input's own seed.** -/
theorem const_fails_ownYes (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H : ProverZ Z X₀ Xh) (Yes : FullSizeMatrix → XF → Prop) (w : WZ Z) (x' : XF) (i : Cm.Idx)
    (hy : Yes w.1 x')
    (hi : VerifiableInference.OnPublicFiles.Flat.Holds w.1 i) (T : ServesAt Zp.p.X i x'.val)
    (ha : H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) = some constTrace) :
    ¬ TraceOwnYes Z Zp H Yes :=
  fun hV => no_served_const Z Zp Np cF scope hr live L ⟨i, x'.val, T, hV w x' i _ hy hi T ha⟩

/-- A control; it counts as no goal. **A prover whose trace field is viaIndex (modelTrace Zp.p.X)
meets TraceOwnRel.** -/
theorem model_meets_ownRel (H₀ : ProverZ Z X₀ Xh) :
    TraceOwnRel Z Zp ({ H₀ with trace := viaIndex (modelTrace Zp.p.X) } : ProverZ Z X₀ Xh) :=
  ownRel_of_through Z Zp _ (modelTrace Zp.p.X) (hinge_modelTrace Zp.p.X)
    fun _ _ _ _ _ h => viaIndex_holds (modelTrace Zp.p.X) h

/-- A control; it counts as no goal. And it answers: at the matrix of an index and the written
instance of a typed request that the index serves. -/
theorem model_answers (H₀ : ProverZ Z X₀ Xh) (i : Cm.Idx)
    (z : XF × RecFull) (T : ServesAt Zp.p.X i z.1.val) :
    ({ H₀ with trace := viaIndex (modelTrace Zp.p.X) } : ProverZ Z X₀ Xh).trace
        (VerifiableInference.OnPublicFiles.Flat.matrixOf i) (LPFD.Full.instanceAsPlainRecord z) =
      some (theTrace Zp.p.X i z.1.val) :=
  (viaIndex_matrixOf (modelTrace Zp.p.X) i _).trans (modelTrace_served Zp.p.X i z T)

/-- A control; it counts as no goal. A prover whose trace field is viaIndex (modelTrace Zp.p.X)
meets TraceIsModel: by definition. -/
theorem model_is_model (H₀ : ProverZ Z X₀ Xh) :
    TraceIsModel Z Zp ({ H₀ with trace := viaIndex (modelTrace Zp.p.X) } : ProverZ Z X₀ Xh) :=
  fun _ _ => rfl

/-- A negative test; it counts as no goal. A prover whose trace function never answers does not meet
TraceIsModel, where an index serves a typed request. -/
theorem none_fails_model (H₀ : ProverZ Z X₀ Xh) (i : Cm.Idx) (z : XF × RecFull)
    (T : ServesAt Zp.p.X i z.1.val) :
    ¬ TraceIsModel Z Zp ({ H₀ with trace := fun _ _ => none } : ProverZ Z X₀ Xh) := fun h => by
  have e := h (VerifiableInference.OnPublicFiles.Flat.matrixOf i) (LPFD.Full.instanceAsPlainRecord z)
  rw [viaIndex_matrixOf, modelTrace_served Zp.p.X i z T] at e
  cases e

variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)

/-- A control; it counts as no goal. **A prover whose trace field is viaIndex (modelTrace Zp.p.X)
meets TraceOwn, at all rows G and every Yes.** -/
theorem model_meets_own (H₀ : ProverZ Z X₀ Xh) (Yes : FullSizeMatrix → XF → Prop) :
    TraceOwn Z Zp Np cF run₂ run₃ B G
      ({ H₀ with trace := viaIndex (modelTrace Zp.p.X) } : ProverZ Z X₀ Xh) Yes :=
  own_of_ownRel Z Zp Np cF run₂ run₃ B G _ Yes (model_meets_ownRel Z Zp H₀)

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: a prover whose trace function answers the constant trace 129 at one typed
request of Yes and the input's own seed, at a matrix that holds an index which serves it, does not
meet TraceOwn.** -/
theorem const_fails_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H : ProverZ Z X₀ Xh) (Yes : FullSizeMatrix → XF → Prop) (w : WZ Z) (x' : XF) (i : Cm.Idx)
    (hy : Yes w.1 x')
    (hi : VerifiableInference.OnPublicFiles.Flat.Holds w.1 i) (T : ServesAt Zp.p.X i x'.val)
    (ha : H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) = some constTrace) :
    ¬ TraceOwn Z Zp Np cF run₂ run₃ B G H Yes :=
  fun h => const_fails_ownYes Z Zp Np cF scope hr live L H Yes w x' i hy hi T ha
    (ownYes_of_own Z Zp Np cF run₂ run₃ B G H Yes scope hr live L h)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_tracePremisesTests
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_tracePremisesTests
#print axioms OnBytes.FrontRoad.constTrace
#print axioms OnBytes.FrontRoad.const_not_small
#print axioms OnBytes.FrontRoad.hinge_of_none
#print axioms OnBytes.FrontRoad.oneRequestTrace
#print axioms OnBytes.FrontRoad.hinge_one_request
#print axioms OnBytes.FrontRoad.via_prover
#print axioms OnBytes.FrontRoad.holds_inRange
#print axioms OnBytes.FrontRoad.no_index_no_clause
#print axioms OnBytes.FrontRoad.no_served_const
#print axioms OnBytes.FrontRoad.valid_of_served
#print axioms OnBytes.FrontRoad.not_all_valid
#print axioms OnBytes.FrontRoad.ProverZ
#print axioms OnBytes.FrontRoad.none_meets_ownRel
#print axioms OnBytes.FrontRoad.none_meets_ownYes
#print axioms OnBytes.FrontRoad.ownYes_at_nothing
#print axioms OnBytes.FrontRoad.const_fails_ownRel
#print axioms OnBytes.FrontRoad.const_fails_ownYes
#print axioms OnBytes.FrontRoad.model_meets_ownRel
#print axioms OnBytes.FrontRoad.model_answers
#print axioms OnBytes.FrontRoad.model_is_model
#print axioms OnBytes.FrontRoad.none_fails_model
#print axioms OnBytes.FrontRoad.model_meets_own
#print axioms OnBytes.FrontRoad.const_fails_own
