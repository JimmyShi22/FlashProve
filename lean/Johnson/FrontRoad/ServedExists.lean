-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ServedExists.lean: at public files in scope that can be read and pass protocolDataWellFormed,
under LaidAt, there are an index and a typed request that the index serves (servedTyped_exists). So
the controls and negative tests of Johnson/FrontRoad/TracePremisesTests.lean that say something only
where a served typed request exists say something at all such public files: each has its twin below.
They count as no goal of the release: none is one of the release's goal statements.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  servedTyped_exists   an index i and a typed request x' with ServesAt Zp.p.X i x'.val
      (Johnson/HonestTrace/Full.lean). By ordsL_met_scope and under_of_scope
      (Johnson/Meaning/Scope.lean): the library's own member, a request with r = 1023 and e = 1024,
      which the programs' reader takes (WellFormed, Johnson/Flat/LedgerClaim.lean).
  valid_exists   so there are a matrix and a typed request in the relation RyesZ Z (by
      valid_of_served). proverZ_exists, a control: the type of the provers at Z, at X₀ := Xh :=
      Unit, has a value, one without rows: so the five statements below that speak of every prover
      speak of something. const_not_own speaks also of every book and all rows: that these two types
      have values (all lists empty) is by inspection, not proved here.
  none_not_model   a negative test: no prover whose trace function never answers meets TraceIsModel.
  model_answers_somewhere   a control: a prover whose trace field is viaIndex (modelTrace Zp.p.X)
      answers at some matrix and written instance.
  const_not_ownRel   a negative test: a prover whose trace function answers the constant trace 129
      everywhere does not meet TraceOwnRel; it meets TraceOwnYes at Yes := nothing
      (ownYes_at_nothing). const_not_ownYes, const_not_own: nor does it meet TraceOwnYes or, at any
      rows G, TraceOwn, at Yes := RyesZ Z. So TraceOwnYes at Yes := nothing does not give
      TraceOwnRel; at Yes := RyesZ Z it does (ownRel_of_ownYes,
      Johnson/FrontRoad/TracePremises.lean). No one theorem states the first of these two.

How it fits. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean.

Limits.
  The index and the request are the library's own member; nothing is said of any other. By
      inspection, not proved here (the lemmas that are used say "there are"): it is the index of the
      all-zero weights, with all tokens 0 and y = 0 (some_true, Policy/Rel/TrueGuards.lean;
      ordsL_met, Johnson/Road/Lane5TopLMet.lean). The request is "the next token after 1,024
      tokens": it covers the one position 1023 and has no counted position, so the policy's two
      clauses on costs hold for free. The tests at the constant trace are at the whole relation or
      at Yes := RyesZ Z: at Yes := nothing every prover meets TraceOwnYes and TraceOwn. Nothing here
      is said of any prover that runs, nor that the premises of an implication of
      Johnson/FrontRoad/SessionStopsOfTrace.lean hold together.
  The full size alone. That any public files meet the four public premises together is not proved
      here.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.TracePremisesTests

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
local instance (priority := high) nonemptyPadZ_servedExists : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_servedExists {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

open OnBytes.Road in
/-- **At public files in scope that can be read and pass protocolDataWellFormed, under LaidAt: there are an index
and a typed request that the index serves.** -/
theorem servedTyped_exists (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ (i : Cm.Idx) (x' : XF), ServesAt Zp.p.X i x'.val := by
  have hX := publicAt Z Zp Np cF scope hr live L
  have A := Hd.core_of_scope scope hr hX
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp (some Z.lay) Zp.p.X hr hX
  have tS' : Cm.Scales.of pp = VerifiableInference.OnPublicFiles.Flat.scalesAt Zp.p.X := tS (A.num 2)
  obtain ⟨i, x, Zm, ZA, er, ee, O⟩ := L5.ordsL_met_scope hX A hr tS' tP
  have hre : x.r < x.e := by rw [er, ee]; decide
  have V := L5.under_of_scope hX A hr tS' tP hre O
  have W : VerifiableInference.OnPublicFiles.Flat.WellFormed x :=
    ⟨hre, fun h => absurd h (by rw [ee]; decide)⟩
  exact ⟨i, ⟨x, W⟩, (servesAt_iff_in_scope scope hr hX i x).2 V⟩

/-- So there are a matrix and a typed request in the relation RyesZ Z. -/
theorem valid_exists (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ (m : FullSizeMatrix) (x' : XF), RyesZ Z m x' := by
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  exact ⟨_, x', valid_of_served Z Zp Np cF scope hr live L i x' T⟩

/-- A control; it counts as no goal. The type of the provers at Z, at X₀ := Xh := Unit, has a value:
one without rows. So the tests below, which speak of every prover, speak of something. -/
theorem proverZ_exists : Nonempty (ProverZ Z Unit Unit) :=
  ⟨{ stored := fun _ _ _ _ => none, trace := fun _ _ => none, key := ProofFile.Honest.pureKey
     inRange := fun _ => true, dummy := fun _ _ => 0, own₀ := (), ownShared₀ := ()
     first := [], shared := [], second := [], meet := fun _ _ => () }⟩

variable {X₀ Xh : Type}

/-- A negative test; it counts as no goal. **No prover whose trace function never answers meets
TraceIsModel**, at such public files. -/
theorem none_not_model (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H₀ : ProverZ Z X₀ Xh) :
    ¬ TraceIsModel Z Zp ({ H₀ with trace := fun _ _ => none } : ProverZ Z X₀ Xh) := by
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  exact none_fails_model Z Zp H₀ i
    (x', (s, ansAt (AZ Z) PadZ (holdZ Z) (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) T

/-- A control; it counts as no goal. **A prover whose trace field is viaIndex (modelTrace Zp.p.X)
answers at some matrix and written instance**, at such public files. -/
theorem model_answers_somewhere (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H₀ : ProverZ Z X₀ Xh) :
    ∃ m ξ tr, ({ H₀ with trace := viaIndex (modelTrace Zp.p.X) } : ProverZ Z X₀ Xh).trace m ξ =
      some tr := by
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  exact ⟨_, _, _, model_answers Z Zp H₀ i
    (x', (s, ansAt (AZ Z) PadZ (holdZ Z) (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) T⟩

/-- A negative test; it counts as no goal. **A prover whose trace function answers the constant
trace 129 everywhere does not meet TraceOwnRel**, at such public files. -/
theorem const_not_ownRel (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H₀ : ProverZ Z X₀ Xh) :
    ¬ TraceOwnRel Z Zp ({ H₀ with trace := fun _ _ => some constTrace } : ProverZ Z X₀ Xh) := by
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  exact const_fails_ownRel Z Zp Np cF scope hr live L _
    (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s) x' s i
    (valid_of_served Z Zp Np cF scope hr live L i x' T)
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i) T rfl

/-- A negative test; it counts as no goal. **A prover whose trace function answers the constant
trace 129 everywhere does not meet TraceOwnYes at Yes := RyesZ Z**, at such public files. -/
theorem const_not_ownYes (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H₀ : ProverZ Z X₀ Xh) :
    ¬ TraceOwnYes Z Zp ({ H₀ with trace := fun _ _ => some constTrace } : ProverZ Z X₀ Xh)
      (RyesZ Z) := by
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  exact const_fails_ownYes Z Zp Np cF scope hr live L _ (RyesZ Z)
    (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s) x' i
    (valid_of_served Z Zp Np cF scope hr live L i x' T)
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i) T rfl

variable {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)

/-- A negative test; it counts as no goal. **A prover whose trace function answers the constant
trace 129 everywhere does not meet TraceOwn at Yes := RyesZ Z**, at every book B and all rows G, at
such public files. -/
theorem const_not_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (H₀ : ProverZ Z X₀ Xh) :
    ¬ TraceOwn Z Zp Np cF run₂ run₃ B G
      ({ H₀ with trace := fun _ _ => some constTrace } : ProverZ Z X₀ Xh) (RyesZ Z) :=
  fun h => const_not_ownYes Z Zp Np cF scope hr live L H₀
    (ownYes_of_own Z Zp Np cF run₂ run₃ B G _ (RyesZ Z) scope hr live L h)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_servedExists
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_servedExists
#print axioms OnBytes.FrontRoad.servedTyped_exists
#print axioms OnBytes.FrontRoad.valid_exists
#print axioms OnBytes.FrontRoad.proverZ_exists
#print axioms OnBytes.FrontRoad.none_not_model
#print axioms OnBytes.FrontRoad.model_answers_somewhere
#print axioms OnBytes.FrontRoad.const_not_ownRel
#print axioms OnBytes.FrontRoad.const_not_ownYes
#print axioms OnBytes.FrontRoad.const_not_own
