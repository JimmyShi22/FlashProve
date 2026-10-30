-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CellsOwnAtSpec.lean: definitions and statements only. CellsOwnAt cells' is a
premise on the prover's trace function that says what the proofs of the two implications of
Johnson/FrontRoad/TraceOwnAtSpec.lean take from TraceOwnAt e and ReadsAs together: at every tied
request of Yes at which the trace function answers a trace tr, what the reader cells' yields of tr
is cellsC Zp.p.X of the model's trace. It names no function e and asks no ReadsAs. TraceOwnAt e with
ReadsAs gives it; so TraceOwn gives it at the reader cellsC Zp.p.X. The two implications are stated
from it. Proved in Johnson/FrontRoad/CellsOwnAt.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  CellsOwnAt cells'   TraceOwnAt's text (Johnson/FrontRoad/TraceOwnAtSpec.lean) with the last line
      cells' tr = cellsC Zp.p.X (theTrace Zp.p.X i x'.val) for tr = e (theTrace Zp.p.X i x'.val).
  Spec.cellsOwn_of_ownAt, Spec.cellsOwn_of_own   under ReadsAs Zp.p.X cells' e, TraceOwnAt e gives
      CellsOwnAt cells'. So, at the trace type Tr, TraceOwn gives CellsOwnAt (cellsC Zp.p.X).
  Spec.sessionStops_of_cellsOwn   Spec.sessionStops_of_tiedOwn_at with CellsOwnAt cells' in the
      place of e, ReadsAs and TraceOwnAt e. mats is free, so matsOf Zp.p.X is among its values. For
      the field sessionStops of PremWDebts (E2E/BridgeDebts.lean) this is the implication to name,
      at mats := matsOf Zp.p.X, and the line on its premise reads: «CellsOwnAt cells′, cells′ the
      pins' reader: at every tied request at which the prover's trace function answers, the cells
      that the private stop reads are the model's cells at an index that the input's matrix holds
      and at the input's own request (TraceOwn gives it; at ProofFile's reader it is TraceOwnAt (cellsC
      X))».
  Spec.cells_are_trace_of_cellsOwn   Spec.cells_are_trace_at from the same premise.
  Spec.cellsOwn_speaks   a control: at every e and cells' that meet ReadsAs, a prover whose trace
      field is modelAt Zp.p.X e meets CellsOwnAt cells', at all rows G and every Yes. That some tied
      request of Yes := RyesZ Z has a trace there, under the four public premises, is
      Spec.ownAt_speaks.
  Spec.const_not_cellsOwn   a negative test: under the four public premises, a prover whose trace
      function answers everywhere one trace t₀ of which cells' yields cellsC Zp.p.X of the constant
      trace 129 does not meet CellsOwnAt cells' at Yes := RyesZ Z.
  Spec.cellsOwn_id   at the trace type Cells and the reader id, CellsOwnAt id is TraceOwnAt (cellsC
      Zp.p.X): nothing is lost there.
  bendAt25, Spec.readsAs_bend, Spec.cellsOwn_not_own   a control that parts the two premises at the
      trace type Tr: the reader cellsC X does not see 1 added at the number 25; under the four
      public premises, a prover whose trace field is the model's trace bent so meets CellsOwnAt
      (cellsC Zp.p.X) and does not meet TraceOwn, at Yes := RyesZ Z.

How it fits. A weaker premise makes a stronger implication. Spec.sessionStops_of_pinned_files
(Johnson/FrontRoad/ParOwnChecksSpec.lean) is stronger still: of these cells it asks only that they
are small. At the trace type Cells and the reader id, CellsOwnAt id says that the trace is cellsC
Zp.p.X of the model's trace: by their author's account, not read here
(Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean and AtPureFullIn.lean, files which this library
may not hold), that is the reader at which the library's honest rows for the whole description lay
the smallness test's part, and the trace of a written choice of fields. At the trace type Tr and the
reader cellsC Zp.p.X it asks of the trace only what cellOf reads of it, which is less than TraceOwn
asks (Spec.cellsOwn_not_own; by inspection, beyond that control: cellOf reads no entry at a number
from 25 on, none at a number in a list that no name of the segment has, and each entry only up to a
multiple of the field's prime). Words (member, half, part, public and private abort test, stated
share): Johnson/FrontRoad/SessionStopsPinned.lean. Not one of the release's goal statements.

Limits.
  No whole prover is named: the controls and the negative test name a trace field alone. The pin, hR
      and CellsOwnAt cells' stay premises of the implication; no book, rows and prover are known at
      which they hold together. No value is given for the bound.
  CellsOwnAt cells' binds and reads the hidden index, as TraceOwn does. It holds of no more than the
      cells: what the trace bears beyond what cells' reads is not held. Whoever wants the whole
      trace wants TraceOwnAt. A part of G that reads the trace otherwise than through cells' reads
      what this premise does not hold. cells' is free, and the premise binds the trace through
      cells' alone. At a constant cells', so at a type Tr' with one member, it asks nothing of which
      trace the trace function answers: it says that the constant is the model's cells at every tied
      request of Yes that has a trace, and at a Yes with one matrix and one request there is such a
      constant (by inspection, not proved). ReadsAs shut that out wherever cellsC Zp.p.X is not
      constant; here only the pins, which stand at the same cells', tie the reader to the rows. A
      trace function that never answers meets CellsOwnAt cells' at every cells'; it does not meet
      hR.
  At the reader cellsC Zp.p.X TraceOwn is not CellsOwnAt: it only gives it (Spec.cellsOwn_of_own,
      Spec.cellsOwn_not_own). Of other readers at the type Tr nothing is said. Named for the field
      sessionStops, cells' is no free letter: it is the reader at which the two pins stand, and
      CellsOwnAt is not to be cited without the pins. That under the two pins every private abort
      test of the rows reads the trace through cells' alone is by inspection (askOfInput,
      Johnson/Desc/ProofFile/Honest/K8/Part.lean; smallStop,
      Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean), not proved here. CellsOwnAt is a premise for
      that field alone: it does not say that the prover's trace is the model's.
  The type of traces and the reader are letters: one statement is read at both pairs. No prover and
      no rows at the one type are carried to the other. The prover here has the index type FullSizeMatrix and
      the randomness type (protocolAtFiles Z).EncodingRandomness. By the same account the rows and the choice of fields named
      under "How it fits" stand at another index type and another randomness type: they are no value
      of G and H here, and nothing here carries a prover from those types to these.
  The three limits of Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean that the head of
      Johnson/FrontRoad/TraceOwnAtSpec.lean quotes hold of the premise in the last line of AtTiedAt
      here too. Spec.cells_are_trace_of_cellsOwn holds idly where no tied request of Yes has a
      trace. Whether theTrace has an entry that is not 0 at any served instance is not said.
  At public files that do not meet scope, the reading, protocolDataWellFormed and LaidAt every statement here that
      has them as premises holds idly. That these are met together is proved of one stored set of
      files, VerifierAndGoals.storedPublicFiles, in the side library (premises_met_at_full,
      AtFullSide/Top/LaidAtFull.lean).
  The full size alone.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.TraceOwnAtSpec

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
local instance (priority := high) nonemptyPadZ_cellsOwnAtSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_cellsOwnAtSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)

/-- **A premise's form: the cells that cells' reads of the prover's trace are the model's.** At
every tied request of Yes, of whichever typed request x' in the relation RyesZ Z the input's
instance is written, with the OOD sample at whichever seed s: of the trace tr that H.trace returns
the reader cells' yields cellsC Zp.p.X (theTrace Zp.p.X i x'.val), at each index i that the matrix
holds and that serves x'. -/
def CellsOwnAt (cells' : Tr' → ProofFile.Honest.Cells) : Prop :=
  AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
    ∀ (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) (i : Cm.Idx),
      LPFD.Full.instanceAsPlainRecord a = LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s)) →
      RyesZ Z w.1 x' → VerifiableInference.OnPublicFiles.Flat.Holds w.1 i → ServesAt Zp.p.X i x'.val →
      cells' tr = cellsC Zp.p.X (theTrace Zp.p.X i x'.val)

end

/-- **Under ReadsAs, TraceOwnAt e gives CellsOwnAt cells'.** -/
def Spec.cellsOwn_of_ownAt : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (cells' : Tr' → ProofFile.Honest.Cells) (e : Tr → Tr'),
    ReadsAs Zp.p.X cells' e → TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes e →
      CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes cells'

/-- **TraceOwn gives CellsOwnAt at the reader cellsC Zp.p.X.** -/
def Spec.cellsOwn_of_own : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (Yes : FullSizeMatrix → XF → Prop),
    TraceOwn Z Zp Np cF run₂ run₃ B G H Yes →
      CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes (cellsC Zp.p.X)

/-- **sessionStops_of_tiedOwn_at from the weaker premise.** The reader of cells is cells'; the
parameters are the description's own; the planner's four arguments are its own; the premise on the
trace is CellsOwnAt cells'. mats is free. All else that the docstring of sessionStops_of_tiedOwn
says holds here too, with CellsOwnAt cells' for TraceOwn, Spec.cellsOwn_speaks for the prover of
which it is proved, and Spec.const_not_cellsOwn for const_not_own: that it can fail is said only at
a reader that yields cellsC Zp.p.X of the constant trace 129 of some trace. -/
def Spec.sessionStops_of_cellsOwn : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (mats : ℕ → List (ℕ × String × ℕ))
    (cells' : Tr' → ProofFile.Honest.Cells)
    (_h₁ : RowsPinned (parOwn Zp mats) cells' (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) cells' (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (_hO : CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes cells')
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

/-- **Under CellsOwnAt cells', at every tied request of Yes at which H.trace answers, the cells that
the pinned part reads at matsOf are the entries of the model's trace**, at an index that the input's
matrix holds and the instance that is read off the input's written instance. -/
def Spec.cells_are_trace_of_cellsOwn : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (cells' : Tr' → ProofFile.Honest.Cells)
    (_hO : CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes cells'),
    AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
      ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        ProofFile.instOf (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧
        ∀ l < 25, ∀ mu r c,
          ProofFile.Honest.K8.cellsAtOf (cells' tr) (matsOf Zp.p.X l) mu r c =
            theTrace Zp.p.X i x l mu r c

/-- A control; it counts as no goal. **At every e and cells' that meet ReadsAs, a prover whose trace
field is modelAt Zp.p.X e meets CellsOwnAt cells', at all rows G and every Yes.** Nothing is said of
that prover's rows. -/
def Spec.cellsOwn_speaks : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (cells' : Tr' → ProofFile.Honest.Cells) (e : Tr → Tr'),
    ReadsAs Zp.p.X cells' e →
      CellsOwnAt Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X e } Yes cells'

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: a prover whose trace function answers everywhere one trace t₀ of which cells'
yields cellsC Zp.p.X of the constant trace 129 does not meet CellsOwnAt cells' at Yes := RyesZ Z.**
The constant trace 129 is no trace of the model, whose entries are below 129 in absolute value. Such
a t₀ is had at the reader cellsC Zp.p.X (that trace), at the reader id (cellsC Zp.p.X of it), and at
every e and cells' that meet ReadsAs (e of it): so with Spec.cellsOwn_of_ownAt this test gives
Spec.const_not_ownAt. -/
def Spec.const_not_cellsOwn : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (cells' : Tr' → ProofFile.Honest.Cells) (t₀ : Tr')
    (_h₀ : cells' t₀ = cellsC Zp.p.X fun _ _ _ _ => 129),
    ¬ CellsOwnAt Z Zp Np cF run₂ run₃ B G { H₀ with trace := fun _ _ => some t₀ } (RyesZ Z) cells'

/-- At the trace type Cells and the reader id nothing is lost: CellsOwnAt id is TraceOwnAt
(cellsC Zp.p.X). -/
def Spec.cellsOwn_id : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey ProofFile.Honest.Cells X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey ProofFile.Honest.Cells X₀ Xh) (Yes : FullSizeMatrix → XF → Prop),
    CellsOwnAt Z Zp Np cF run₂ run₃ B G H Yes id ↔
      TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes (cellsC Zp.p.X)

/-- For a control: the trace T with 1 added to every entry at the number 25, which is past the last
sub-proof's number, 24: no sub-proof has these entries. -/
def bendAt25 (T : Tr) : Tr := fun k a r c => if k = 25 then T k a r c + 1 else T k a r c

/-- A control; it counts as no goal. The reader cellsC X does not see the bend. -/
def Spec.readsAs_bend : Prop :=
  ∀ X : OnBytes.Model.Verify.Public, ReadsAs X (cellsC X) bendAt25

/-- A control; it counts as no goal. **At public files in scope that can be read and pass protocolDataWellFormed,
under LaidAt: a prover whose trace field is the model's trace bent at the number 25 meets CellsOwnAt
(cellsC Zp.p.X) and does not meet TraceOwn, at Yes := RyesZ Z.** So CellsOwnAt (cellsC Zp.p.X) asks
less than TraceOwn. -/
def Spec.cellsOwn_not_own : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF),
    CellsOwnAt Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X bendAt25 } (RyesZ Z)
        (cellsC Zp.p.X) ∧
      ¬ TraceOwn Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X bendAt25 } (RyesZ Z)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_cellsOwnAtSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_cellsOwnAtSpec
#print axioms OnBytes.FrontRoad.CellsOwnAt
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_of_ownAt
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_of_own
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_cellsOwn
#print axioms OnBytes.FrontRoad.Spec.cells_are_trace_of_cellsOwn
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_speaks
#print axioms OnBytes.FrontRoad.Spec.const_not_cellsOwn
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_id
#print axioms OnBytes.FrontRoad.bendAt25
#print axioms OnBytes.FrontRoad.Spec.readsAs_bend
#print axioms OnBytes.FrontRoad.Spec.cellsOwn_not_own
