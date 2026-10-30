-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CellsOwnAt.lean: the proofs of the nine statements of
Johnson/FrontRoad/CellsOwnAtSpec.lean: the premise CellsOwnAt cells', which TraceOwnAt e with
ReadsAs gives, and the two implications from it.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The steps   plainCells: under the four public premises CellsOwnAt cells' gives, at every tied
      request of Yes with its trace tr, an index that the input's matrix holds and the instance read
      off its written instance, such that the index serves the instance and cells' tr is cellsC
      Zp.p.X of the model's trace there. cells129_ne: under PartsFit, cellsC X of the constant trace
      129 is not cellsC X of a trace whose entries are below 129 in absolute value. byName_bend,
      cellOf_bend: the readings by names and by labels do not see 1 added at the number 25.
  The nine proofs   cellsOwn_of_ownAt, cellsOwn_of_own, sessionStops_of_cellsOwn,
      cells_are_trace_of_cellsOwn, cellsOwn_speaks, const_not_cellsOwn, cellsOwn_id, readsAs_bend,
      cellsOwn_not_own.

How it fits. sessionStops_of_cellsOwn is sessionStops_of_pinned_files
(Johnson/FrontRoad/ParOwnChecks.lean) with its premise on the cells paid from plainCells, the clause
small of meetsAll_theTrace (Johnson/Goal/HonestTrace/FullPlanesInScope.lean) and cellsSmall_cellOf
(Johnson/HonestTrace/DigitsAtTrace.lean). cells_are_trace_of_cellsOwn goes by plainCells and
reads_theTrace (Johnson/FrontRoad/CellsAreTrace.lean). The first half of cellsOwn_not_own is
cellsOwn_speaks at e := bendAt25; the second takes the tied request of ownAt_speaks, whose trace is
the bent one by model_meets_ownAt, and reads it at the entry 25 0 0 0. With cellsOwn_of_ownAt,
sessionStops_of_cellsOwn gives sessionStops_of_tiedOwn_at (Johnson/FrontRoad/TraceOwnAt.lean), which
is proved there by its own lines. All limits: the head of Johnson/FrontRoad/CellsOwnAtSpec.lean. Not
one of the release's goal statements.
-/
import Johnson.FrontRoad.CellsOwnAtSpec
import Johnson.FrontRoad.TraceOwnAt

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
local instance (priority := high) nonemptyPadZ_cellsOwnAt : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_cellsOwnAt {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## The steps -/

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)

/-- plainAt (Johnson/FrontRoad/TraceOwnAt.lean) from CellsOwnAt: of the trace it has what cells'
reads. -/
theorem plainCells (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (cells' : Tr' → ProofFile.Honest.Cells)
    (h : CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes cells') :
    AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
      ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        ProofFile.instOf (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧
        cells' tr = cellsC Zp.p.X (theTrace Zp.p.X i x) := by
  intro n w a ht tr htr
  obtain ⟨s, x', e', hx'⟩ := ht.2.rel
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx'
  exact ⟨i, x'.val, hi, by rw [e', ProofFile.instOf_at_frame], T, h n w a ht tr htr s x' i e' hx' hi T⟩

end

/-- Under PartsFit: cellsC X of the constant trace 129 is not cellsC X of a trace whose entries are
below 129 in absolute value. -/
theorem cells129_ne {X : OnBytes.Model.Verify.Public} (hP : OnBytes.HonestTrace.PartsFit X)
    (T : Tr) (hs : ∀ k a r c, |T k a r c| < 129) :
    cellsC X (fun _ _ _ _ => 129) ≠ cellsC X T := by
  intro e2
  have hσ : (OnBytes.HonestTrace.Seg.ff 0).Below 12 := by
    show 0 < 12
    norm_num
  have c1 := OnBytes.HonestTrace.cellOf_label hP (fun _ _ _ _ => 129) hσ
    (μ := OnBytes.HonestTrace.MatName.ar) (a := 4) rfl 0 0
  have c2 := OnBytes.HonestTrace.cellOf_label hP T hσ
    (μ := OnBytes.HonestTrace.MatName.ar) (a := 4) rfl 0 0
  have e3 := congrArg (fun C : ProofFile.Honest.Cells =>
    C.cell ((OnBytes.HonestTrace.Seg.ff 0).no 12) OnBytes.HonestTrace.MatName.ar.label 0 0) e2
  exact cast129_ne _ (hs _ _ _ _) (c1.symm.trans (e3.trans c2))

/-- The reading by names does not see the bend, at a segment of the proof. -/
theorem byName_bend (X : OnBytes.Model.Verify.Public) (T : Tr) (σ : OnBytes.HonestTrace.Seg)
    (μ : OnBytes.HonestTrace.MatName) (r c : ℕ) (hb : σ.Below 12) :
    OnBytes.HonestTrace.byName X (bendAt25 T) σ μ r c = OnBytes.HonestTrace.byName X T σ μ r c := by
  have hne : σ.no 12 ≠ 25 := by
    cases σ with
    | ff g =>
      have hg : g < 12 := hb
      show 2 * g ≠ 25
      omega
    | att g =>
      have hg : g < 12 := hb
      show 2 * g + 1 ≠ 25
      omega
    | head =>
      show 2 * 12 ≠ 25
      norm_num
  unfold OnBytes.HonestTrace.byName
  by_cases h : OnBytes.HonestTrace.Seg.ofNo 12 (σ.no 12) = some σ
  · simp only [if_pos h]
    cases OnBytes.HonestTrace.noAt X σ μ with
    | none => rfl
    | some a =>
      show bendAt25 T (σ.no 12) a r c = T (σ.no 12) a r c
      unfold bendAt25
      rw [if_neg hne]
  · simp only [if_neg h]

/-- The reader by labels does not see the bend. -/
theorem cellOf_bend (X : OnBytes.Model.Verify.Public) (T : Tr) (k : ℕ) (s : String) (r c : ℕ) :
    OnBytes.HonestTrace.cellOf X (bendAt25 T) k s r c = OnBytes.HonestTrace.cellOf X T k s r c := by
  unfold OnBytes.HonestTrace.cellOf
  cases hσ : OnBytes.HonestTrace.Seg.ofNo 12 k with
  | none => rfl
  | some σ =>
    simp only
    split
    · rw [byName_bend X T σ _ r c (OnBytes.HonestTrace.Seg.of_ofNo hσ).1]
    · rfl

/-! ## The nine -/

theorem cellsOwn_of_ownAt : Spec.cellsOwn_of_ownAt := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H Yes cells' e hE h n w a ht tr htr s x' i
    e' hx hi T
  rw [h n w a ht tr htr s x' i e' hx hi T]
  exact hE _

theorem cellsOwn_of_own : Spec.cellsOwn_of_own := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H Yes h
  exact cellsOwn_of_ownAt Z Zp Np cF run₂ run₃ B G H Yes (cellsC Zp.p.X) id (readsAs_id Zp.p.X)
    ((traceOwnAt_id Z Zp Np cF run₂ run₃ B G H Yes).2 h)

theorem sessionStops_of_cellsOwn : Spec.sessionStops_of_cellsOwn := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H scope pp hr live D r L w₀ rc x₀ k₀ R hR
    hn Yes mats cells' h₁ h₃ hO ok Gs
  refine sessionStops_of_pinned_files Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes mats
    cells' h₁ h₃ (fun n w a ht tr htr => ?_) ok Gs
  obtain ⟨i, x, -, -, S, hc⟩ :=
    plainCells Z Zp Np cF run₂ run₃ B G H Yes scope hr live L cells' hO n w a ht tr htr
  intro b _ P _
  have key := cellsSmall_cellOf (X := Zp.p.X)
    (meetsAll_theTrace scope hr (publicOf_laid Z Zp Np cF L) S).small P.1 P.2
  rw [← hc] at key
  exact key

theorem cells_are_trace_of_cellsOwn : Spec.cells_are_trace_of_cellsOwn := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H Yes scope pp hr live D r L cells' hO
    n w a ht tr htr
  obtain ⟨i, x, hi, hx, S, hc⟩ :=
    plainCells Z Zp Np cF run₂ run₃ B G H Yes scope hr live L cells' hO n w a ht tr htr
  refine ⟨i, x, hi, hx, S, fun l hl mu r' c => ?_⟩
  rw [hc]
  exact reads_theTrace Z Zp Np cF scope hr L i x S l hl mu r' c

theorem cellsOwn_speaks : Spec.cellsOwn_speaks := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H₀ Yes cells' e hE
  exact cellsOwn_of_ownAt Z Zp Np cF run₂ run₃ B G _ Yes cells' e hE
    (model_meets_ownAt Z Zp Np cF run₂ run₃ B G H₀ Yes e)

theorem const_not_cellsOwn : Spec.const_not_cellsOwn := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H₀ scope pp hr live D r L cells' t₀ h₀ h
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have hX := publicOf_laid Z Zp Np cF L
  have hi : VerifiableInference.OnPublicFiles.Flat.Holds
      (VerifiableInference.OnPublicFiles.Flat.matrixOf i) i :=
    VerifiableInference.OnPublicFiles.Flat.holds_matrixOf i
  have hx : RyesZ Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) x' :=
    valid_of_holds Z Zp Np cF scope hr live L _ i x' hi T
  have ht : TiedYes Z Zp Np cF run₂ run₃ B G { H₀ with trace := fun _ _ => some t₀ }
      (RyesZ Z) 0 (VerifiableInference.OnPublicFiles.Flat.matrixOf i, rc, s)
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) :=
    ⟨⟨x', hx, rfl⟩, validTiedG_atFiles Z Zp Np cF run₂ run₃ B G _
      (AtPublicFiles.AtZero.itemsZero_of_data L.data) 0 _ rc s x' trivial trivial hx⟩
  have e1 : cells' t₀ = cellsC Zp.p.X (theTrace Zp.p.X i x'.val) :=
    h 0 _ (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s) ht _ rfl s x' i
      (congrArg (fun ρ => LPFD.Full.instanceAsPlainRecord (x', ρ))
        (recOf_at Z (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) hx hi T
  exact cells129_ne (OnBytes.HonestTrace.partsFit_in_scope scope hr hX) _
    (meetsAll_theTrace scope hr hX T).small (h₀.symm.trans e1)

theorem cellsOwn_id : Spec.cellsOwn_id := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H Yes
  exact Iff.rfl

theorem readsAs_bend : Spec.readsAs_bend := by
  intro X T
  show (⟨OnBytes.HonestTrace.cellOf X (bendAt25 T)⟩ : ProofFile.Honest.Cells) =
    ⟨OnBytes.HonestTrace.cellOf X T⟩
  congr 1
  funext k s r c
  exact cellOf_bend X T k s r c

theorem cellsOwn_not_own : Spec.cellsOwn_not_own := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H₀ scope pp hr live D r L
  refine ⟨cellsOwn_speaks Z Zp Np cF run₂ run₃ B G H₀ (RyesZ Z) (cellsC Zp.p.X) bendAt25
    (readsAs_bend Zp.p.X), fun h => ?_⟩
  obtain ⟨n, w, a, tr, ht, htr⟩ :=
    ownAt_speaks Z Zp Np cF run₂ run₃ B G H₀ bendAt25 scope hr live L
  obtain ⟨s, x', e', hx'⟩ := ht.2.rel
  obtain ⟨i, hi, T⟩ := served_of_valid Z Zp Np cF scope hr live L w.1 x' hx'
  have e1 : tr = theTrace Zp.p.X i x'.val := h n w a ht tr htr s x' i e' hx' hi T
  have e2 : tr = bendAt25 (theTrace Zp.p.X i x'.val) :=
    model_meets_ownAt Z Zp Np cF run₂ run₃ B G H₀ (RyesZ Z) bendAt25 n w a ht tr htr s x' i e' hx'
      hi T
  have e3 := congrFun (congrFun (congrFun (congrFun (e1.symm.trans e2) 25) 0) 0) 0
  have e4 : theTrace Zp.p.X i x'.val 25 0 0 0 = theTrace Zp.p.X i x'.val 25 0 0 0 + 1 := e3
  omega

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_cellsOwnAt
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_cellsOwnAt
#print axioms OnBytes.FrontRoad.plainCells
#print axioms OnBytes.FrontRoad.cells129_ne
#print axioms OnBytes.FrontRoad.cellsOwn_of_ownAt
#print axioms OnBytes.FrontRoad.cellsOwn_of_own
#print axioms OnBytes.FrontRoad.sessionStops_of_cellsOwn
#print axioms OnBytes.FrontRoad.cells_are_trace_of_cellsOwn
#print axioms OnBytes.FrontRoad.cellsOwn_speaks
#print axioms OnBytes.FrontRoad.const_not_cellsOwn
#print axioms OnBytes.FrontRoad.byName_bend
#print axioms OnBytes.FrontRoad.cellOf_bend
#print axioms OnBytes.FrontRoad.cellsOwn_id
#print axioms OnBytes.FrontRoad.readsAs_bend
#print axioms OnBytes.FrontRoad.cellsOwn_not_own
