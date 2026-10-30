-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TraceOwnAt.lean: the proofs of the ten statements of
Johnson/FrontRoad/TraceOwnAtSpec.lean: the premise TraceOwn and what stands on it, at any type of
traces, through a function e from the model's traces and a reader cells' that meet ReadsAs.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   plainAt: under the four public premises TraceOwnAt e gives, at every tied request of
      Yes with its trace tr, an index that the input's matrix holds and the instance read off its
      written instance, such that the index serves the instance and tr is e of the model's trace
      there; it is plain_of_own (Johnson/FrontRoad/TracePremises.lean) at the trace type Tr'.
      zero_cells: read through any list, the reader 0 yields 0. const_ne_zero: 129 is not 0 in the
      base field. cast129_ne: there 129 is not the image of an integer below 129 in absolute value.
  The ten proofs   readsAs_id, readsAs_cells, traceOwnAt_id, sessionStops_of_tiedOwn_at,
      cells_are_trace_at, model_meets_ownAt, ownAt_speaks, zero_reader_not_readsAs,
      const_fails_ownAt, const_not_ownAt.

How it fits. sessionStops_of_tiedOwn_at is sessionStops_of_pinned_files
(Johnson/FrontRoad/ParOwnChecks.lean), which is general in the type of traces and in the reader,
with its premise on the cells paid from plainAt, ReadsAs, the clause small of meetsAll_theTrace
(Johnson/Goal/HonestTrace/FullPlanesInScope.lean) and cellsSmall_cellOf
(Johnson/HonestTrace/DigitsAtTrace.lean). cells_are_trace_at goes by plainAt, ReadsAs and
reads_theTrace (Johnson/FrontRoad/CellsAreTrace.lean). All limits: the head of
Johnson/FrontRoad/TraceOwnAtSpec.lean. Not one of the release's goal statements.
-/
import Johnson.FrontRoad.TraceOwnAtSpec
import Johnson.FrontRoad.CellsAreTrace

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
local instance (priority := high) nonemptyPadZ_traceOwnAt : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_traceOwnAt {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## The steps -/

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)

/-- plain_of_own at the trace type Tr'. -/
theorem plainAt (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (e : Tr → Tr') (h : TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes e) :
    AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
      ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        ProofFile.instOf (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧
        tr = e (theTrace Zp.p.X i x) := by
  intro n w a ht tr htr
  obtain ⟨s, x', e', hx'⟩ := ht.2.rel
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx'
  exact ⟨i, x'.val, hi, by rw [e', ProofFile.instOf_at_frame], T, h n w a ht tr htr s x' i e' hx' hi T⟩

end

/-- Read through any list, the reader 0 yields 0. -/
theorem zero_cells (ms : List (ℕ × String × ℕ)) (mu r c : ℕ) :
    ProofFile.Honest.K8.cellsAtOf ⟨fun _ _ _ _ => 0⟩ ms mu r c = 0 := by
  unfold ProofFile.Honest.K8.cellsAtOf
  cases ms[mu]? with
  | none => rfl
  | some m => exact signedOf_zero

/-- 129 is not 0 in the base field. -/
theorem const_ne_zero : (129 : Cb.Gl.F) ≠ 0 := by
  intro h
  have h1 : (((128 : ℤ) : ℤ) : Cb.Gl.F) = (((-1 : ℤ) : ℤ) : Cb.Gl.F) := by
    push_cast
    linear_combination h
  have h2 := congrArg ProofFile.Honest.K8.signedOf h1
  rw [OnBytes.HonestTrace.signedOf_cast 128 (by norm_num),
    OnBytes.HonestTrace.signedOf_cast (-1) (by norm_num)] at h2
  norm_num at h2

/-- In the base field 129 is not the image of an integer below 129 in absolute value. -/
theorem cast129_ne (z : ℤ) (h : |z| < 129) : (((129 : ℤ) : ℤ) : Cb.Gl.F) ≠ ((z : ℤ) : Cb.Gl.F) := by
  intro e
  have hp : (Code.pGold : ℤ) = 18446744069414584321 := by rw [Code.pGold_eq]; rfl
  have h1 : (((((129 : ℤ) : ℤ) : Cb.Gl.F)).val : ℤ) = 129 % (Code.pGold : ℤ) := ZMod.val_intCast 129
  have h2 : ((((z : ℤ) : Cb.Gl.F)).val : ℤ) = z % (Code.pGold : ℤ) := ZMod.val_intCast z
  rw [e, h2, hp] at h1
  obtain ⟨ha, hb⟩ := abs_lt.1 h
  omega

/-! ## The ten -/

theorem readsAs_id : Spec.readsAs_id := fun _ _ => rfl

theorem readsAs_cells : Spec.readsAs_cells := fun _ _ => rfl

theorem traceOwnAt_id : Spec.traceOwnAt_id := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H Yes
  exact Iff.rfl

theorem sessionStops_of_tiedOwn_at : Spec.sessionStops_of_tiedOwn_at := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H scope pp hr live D r L w₀ rc x₀ k₀ R hR
    hn Yes mats cells' e hE h₁ h₃ hO ok Gs
  refine sessionStops_of_pinned_files Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes mats
    cells' h₁ h₃ (fun n w a ht tr htr => ?_) ok Gs
  obtain ⟨i, x, -, -, S, rfl⟩ :=
    plainAt Z Zp Np cF run₂ run₃ B G H Yes scope hr live L e hO n w a ht tr htr
  intro b _ P _
  have key := cellsSmall_cellOf (X := Zp.p.X)
    (meetsAll_theTrace scope hr (publicOf_laid Z Zp Np cF L) S).small P.1 P.2
  rw [← hE] at key
  exact key

theorem cells_are_trace_at : Spec.cells_are_trace_at := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H Yes scope pp hr live D r L cells' e hE hO
    n w a ht tr htr
  obtain ⟨i, x, hi, hx, S, rfl⟩ :=
    plainAt Z Zp Np cF run₂ run₃ B G H Yes scope hr live L e hO n w a ht tr htr
  refine ⟨i, x, hi, hx, S, fun l hl mu r' c => ?_⟩
  rw [hE]
  exact reads_theTrace Z Zp Np cF scope hr L i x S l hl mu r' c

theorem model_meets_ownAt : Spec.model_meets_ownAt := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H₀ Yes e n w a _ tr htr s x' i e' _ hi T
  have h : (viaIndex (modelTrace Zp.p.X) w.1 (LPFD.Full.instanceAsPlainRecord a)).map e = some tr := htr
  rw [e', viaIndex_of_holds (modelTrace Zp.p.X) hi,
    modelTrace_served Zp.p.X i (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s)) T] at h
  exact (Option.some.inj h).symm

theorem ownAt_speaks : Spec.ownAt_speaks := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H₀ e scope pp hr live D r L
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have hi : VerifiableInference.OnPublicFiles.Flat.Holds
      (VerifiableInference.OnPublicFiles.Flat.matrixOf i) i :=
    VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i
  have hx : RyesZ Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) x' :=
    valid_of_holds Z Zp Np cF scope hr live L _ i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X e }
      (RyesZ Z) 0 (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s)
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) :=
    ⟨⟨x', hx, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G _
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 _ rc s x' trivial trivial hx⟩
  refine ⟨0, _, _, e (theTrace Zp.p.X i x'.val), ht, ?_⟩
  unfold modelAt
  rw [viaIndex_matrixOf, modelTrace_served Zp.p.X i
    (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s) T]
  rfl

theorem zero_reader_not_readsAs : Spec.zero_reader_not_readsAs := by
  intro Z Zp Np cF scope pp hr D r L h
  have hP := OnBytes.HonestTrace.partsFit_in_scope scope hr (publicOf_laid Z Zp Np cF L)
  have hn : 0 < (matsOf Zp.p.X 24).length := by
    rw [OnBytes.HonestTrace.matsOf_length hP (by norm_num)]
    norm_num
  have h1 := matsOf_reads_ones Z Zp Np cF scope hr L 24 (by norm_num) 0 hn 0 0
  have e : (⟨fun _ _ _ _ => 0⟩ : ProofFile.Honest.Cells) = cellsC Zp.p.X fun _ _ _ _ => 1 :=
    h fun _ _ _ _ => 1
  rw [← e, zero_cells] at h1
  norm_num at h1

theorem const_fails_ownAt : Spec.const_fails_ownAt := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H Yes scope pp hr live D r L w x' i hy hi T
    ha h
  have hx : RyesZ Z w.1 x' := valid_of_holds Z Zp Np cF scope hr live L w.1 i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G H Yes 0 w
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) :=
    ⟨⟨x', hy, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G H
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 w.1 w.2.1 w.2.2 x' trivial trivial hx⟩
  have e := h 0 w (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2) ht _ ha w.2.2 x' i
    (congrArg (fun ρ => LPFD.Full.instanceAsPlainRecord (x', ρ)) (recOf_at Z w.1 w.2.1 w.2.2)) hx hi T
  have e2 : (129 : Cb.Gl.F) =
      OnBytes.HonestTrace.cellOf Zp.p.X (theTrace Zp.p.X i x'.val) 25 "" 0 0 :=
    congrArg (fun C : ProofFile.Honest.Cells => C.cell 25 "" 0 0) e
  exact const_ne_zero e2

theorem const_not_ownAt : Spec.const_not_ownAt := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H₀ scope pp hr live D r L cells' e hE h
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have hX := publicOf_laid Z Zp Np cF L
  have hP := OnBytes.HonestTrace.partsFit_in_scope scope hr hX
  have hi : VerifiableInference.OnPublicFiles.Flat.Holds
      (VerifiableInference.OnPublicFiles.Flat.matrixOf i) i :=
    VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i
  have hx : RyesZ Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) x' :=
    valid_of_holds Z Zp Np cF scope hr live L _ i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G
      { H₀ with trace := fun _ _ => some (e fun _ _ _ _ => 129) }
      (RyesZ Z) 0 (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s)
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) :=
    ⟨⟨x', hx, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G _
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 _ rc s x' trivial trivial hx⟩
  have e1 : (e fun _ _ _ _ => 129) = e (theTrace Zp.p.X i x'.val) :=
    h 0 _ (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s) ht _ rfl s x' i
      (congrArg (fun ρ => LPFD.Full.instanceAsPlainRecord (x', ρ))
        (recOf_at Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) hx hi T
  have e2 : cellsC Zp.p.X (fun _ _ _ _ => 129) = cellsC Zp.p.X (theTrace Zp.p.X i x'.val) := by
    rw [← hE, ← hE, e1]
  have hσ : (OnBytes.HonestTrace.Seg.ff 0).Below 12 := by
    show 0 < 12
    norm_num
  have c1 := OnBytes.HonestTrace.cellOf_label hP (fun _ _ _ _ => 129) hσ
    (μ := OnBytes.HonestTrace.MatName.ar) (a := 4) rfl 0 0
  have c2 := OnBytes.HonestTrace.cellOf_label hP (theTrace Zp.p.X i x'.val) hσ
    (μ := OnBytes.HonestTrace.MatName.ar) (a := 4) rfl 0 0
  have e3 := congrArg (fun C : ProofFile.Honest.Cells =>
    C.cell ((OnBytes.HonestTrace.Seg.ff 0).no 12) OnBytes.HonestTrace.MatName.ar.label 0 0) e2
  exact cast129_ne _ ((meetsAll_theTrace scope hr hX T).small _ _ _ _)
    (c1.symm.trans (e3.trans c2))

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_traceOwnAt
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_traceOwnAt
#print axioms OnBytes.FrontRoad.plainAt
#print axioms OnBytes.FrontRoad.zero_cells
#print axioms OnBytes.FrontRoad.const_ne_zero
#print axioms OnBytes.FrontRoad.readsAs_id
#print axioms OnBytes.FrontRoad.readsAs_cells
#print axioms OnBytes.FrontRoad.traceOwnAt_id
#print axioms OnBytes.FrontRoad.sessionStops_of_tiedOwn_at
#print axioms OnBytes.FrontRoad.cells_are_trace_at
#print axioms OnBytes.FrontRoad.model_meets_ownAt
#print axioms OnBytes.FrontRoad.ownAt_speaks
#print axioms OnBytes.FrontRoad.zero_reader_not_readsAs
#print axioms OnBytes.FrontRoad.const_fails_ownAt
#print axioms OnBytes.FrontRoad.cast129_ne
#print axioms OnBytes.FrontRoad.const_not_ownAt
