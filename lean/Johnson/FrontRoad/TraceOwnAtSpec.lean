-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/TraceOwnAtSpec.lean: definitions and statements only. The premise TraceOwn
(Johnson/FrontRoad/TracePremises.lean) and what stands on it, at any type Tr' of traces: with a
reader cells' of cells off Tr', and a function e from the model's traces (Tr,
Johnson/HonestTrace/Full.lean) into Tr' such that cells' (e T) is cellsC Zp.p.X T at every T. At Tr'
:= Tr, e := id, cells' := cellsC Zp.p.X the two implications are the statements that stand already,
by unfolding (Spec.traceOwnAt_id). At Tr' := Cells (Johnson/Desc/ProofFile/Honest/ForKinds.lean), e
:= cellsC Zp.p.X, cells' := id they speak of a prover whose trace is itself a reader of cells.
Proved in Johnson/FrontRoad/TraceOwnAt.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  ReadsAs X cells' e   a condition on the two letters: at every trace T of the model's type, cells'
      (e T) = cellsC X T.
  AtTiedAt, TraceOwnAt e   AtTied and TraceOwn (Johnson/FrontRoad/TracePremises.lean), word for
      word, at rows and a prover of the trace type Tr', with e (theTrace Zp.p.X i x'.val) where
      TraceOwn has theTrace Zp.p.X i x'.val. The premise in the last line of AtTiedAt, H.trace w.1
      (instanceAsPlainRecord a) = some tr, is the third clause of ReadyInput
      (Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean) at the prover H (provG has the same
      trace field) and the input with the fields w.1, w.2.1, instanceAsPlainRecord a, tr; that file is not
      imported, and its other two clauses are not asked.
  modelAt X e   a trace function on matrices: viaIndex (modelTrace X), with e laid on what it
      answers.
  Spec.readsAs_id, Spec.readsAs_cells, Spec.traceOwnAt_id   the two pairs of letters named above
      meet ReadsAs; at e := id TraceOwnAt is TraceOwn.
  Spec.sessionStops_of_tiedOwn_at   sessionStops_of_tiedOwn_files
      (Johnson/FrontRoad/ParOwnChecksSpec.lean) at these letters: the pins at the reader cells', the
      premise ReadsAs, and TraceOwnAt e for TraceOwn. mats is free, so matsOf Zp.p.X is among its
      values.
  Spec.cells_are_trace_at   cells_are_trace (Johnson/FrontRoad/CellsAreTraceSpec.lean) at these
      letters.
  Spec.model_meets_ownAt, Spec.ownAt_speaks   two controls, at every e: a prover whose trace field
      is modelAt Zp.p.X e meets TraceOwnAt e, at all rows G and every Yes; and at Yes := RyesZ Z
      some tied request of Yes has a trace there.
  Spec.zero_reader_not_readsAs, Spec.const_fails_ownAt, Spec.const_not_ownAt   negative tests. The
      function e that answers the reader 0 at every trace does not meet ReadsAs at cells' := id. A
      prover whose trace function answers the constant reader 129 at a typed request of Yes, at a
      matrix that holds an index which serves it, does not meet TraceOwnAt (cellsC Zp.p.X). At every
      e and cells' that meet ReadsAs, a prover whose trace function answers e of the constant trace
      129 everywhere does not meet TraceOwnAt e at Yes := RyesZ Z.

How it fits. sessionStops_of_pinned (Johnson/FrontRoad/SessionStopsOfPinned.lean) is general in the
type of traces and in the reader of cells. TraceOwn says of a trace that it is theTrace, so it types
at the one type Tr alone. By their author's account, not read here
(Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean and AtPureFullIn.lean, files which this library
may not hold), the library's honest rows for the whole description lay the smallness test's part at
the reader id, at the trace type Cells; and a choice of fields is written whose trace is the model's
trace read by cellOf, which is cellsC's text. These statements speak at both. Words (member, half,
part, public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Not
one of the release's goal statements.

Limits.
  No whole prover is named: the two controls name a trace field alone. The pin, hR and TraceOwnAt e
      stay premises of the implication; no book, rows and prover are known at which they hold
      together, at either pair of letters. No value is given for the bound.
  Only the type of traces and the reader are made letters: one statement is read at both. No prover
      and no rows at the one type are carried to the other. The prover here has the index type FullSizeMatrix
      and the randomness type (protocolAtFiles Z).EncodingRandomness. By the same account the rows named above stand at another
      index type and another randomness type. Nothing here carries a prover from these to those.
  e is free but for ReadsAs, which binds cells' after e alone: what e T holds beyond what cells'
      reads of it is not held. TraceOwnAt e taken alone can be empty: at a type Tr' with one member
      every prover meets it; ReadsAs shuts that out wherever cellsC Zp.p.X is not constant.
  Spec.cells_are_trace_at holds idly where no tied request of Yes has a trace. Whether theTrace has
      an entry that is not 0 at any served instance is not said.
  At public files that do not meet scope, the reading, protocolDataWellFormed and LaidAt every statement here that
      has them as premises holds idly. That these are met together is proved of one stored set of
      files, VerifierAndGoals.storedPublicFiles, in the side library (premises_met_at_full,
      AtFullSide/Top/LaidAtFull.lean).
  TraceOwnAt e binds and reads the hidden index, as TraceOwn does. The line H.trace w.1 (instanceAsPlainRecord a) =
      some tr of AtTiedAt is the third clause of ReadyInput taken alone, and three limits of that
      file hold of it, in that file's words: «The condition holds of no input at a request at which
      the prover's `trace` is `none`.» «It does not say that the trace is a correct run of a model:
      that depends on the prover's `trace`.» «It reads the private input: a value of the thread's
      `valid`, of the real world: never to be quoted as public, nor as what a simulator knows.»
  The full size alone.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.CellsAreTraceSpec

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
local instance (priority := high) nonemptyPadZ_traceOwnAtSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_traceOwnAtSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- **A condition on a reader of cells off Tr' and a function from the model's traces into Tr'**:
read by cells', what e makes of a trace T is cellsC X T. -/
def ReadsAs {Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells' : Tr' → ProofFile.Honest.Cells)
    (e : Tr → Tr') : Prop :=
  ∀ T, cells' (e T) = cellsC X T

/-- A trace function on matrices: viaIndex (modelTrace X), with e laid on what it answers. -/
def modelAt {Tr' : Type} (X : OnBytes.Model.Verify.Public) (e : Tr → Tr') (m : FullSizeMatrix) (ξ : ProofFile.Inst) :
    Option Tr' :=
  (viaIndex (modelTrace X) m ξ).map e

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)

/-- AtTied (Johnson/FrontRoad/TracePremises.lean) at the trace type Tr': at every tied request of
Yes, wherever H.trace answers a trace tr at the input's matrix and written instance, the condition φ
of the private input, the request and tr. -/
def AtTiedAt (φ : WZ Z → XF × RecFull → Tr' → Prop) : Prop :=
  ∀ (n : ℕ) (w : WZ Z) (a : XF × RecFull),
    TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
    ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr → φ w a tr

/-- **A premise's form: TraceOwn at the trace type Tr', through e.** At every tied request of Yes,
of whichever typed request x' in the relation RyesZ Z the input's instance is written, with the OOD
sample at whichever seed s: the trace that H.trace returns is e (theTrace Zp.p.X i x'.val) at each
index i that the matrix holds and that serves x'. -/
def TraceOwnAt (e : Tr → Tr') : Prop :=
  AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
    ∀ (s : (protocolAtFiles Z).OutOfDomainSeed) (x' : XF) (i : Cm.Idx),
      LPFD.Full.instanceAsPlainRecord a = LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s)) →
      RyesZ Z w.1 x' → VerifiableInference.OnPublicFiles.Flat.Holds w.1 i → ServesAt Zp.p.X i x'.val →
      tr = e (theTrace Zp.p.X i x'.val)

end

/-- At Tr' := Tr: the reader cellsC X and e := id meet ReadsAs. -/
def Spec.readsAs_id : Prop :=
  ∀ X : OnBytes.Model.Verify.Public, ReadsAs X (cellsC X) id

/-- At Tr' := Cells: the reader id and e := cellsC X meet ReadsAs. -/
def Spec.readsAs_cells : Prop :=
  ∀ X : OnBytes.Model.Verify.Public, ReadsAs X id (cellsC X)

/-- At Tr' := Tr and e := id TraceOwnAt is TraceOwn. -/
def Spec.traceOwnAt_id : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (Yes : FullSizeMatrix → XF → Prop),
    TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes id ↔ TraceOwn Z Zp Np cF run₂ run₃ B G H Yes

/-- **sessionStops_of_tiedOwn_files at any type of traces.** The reader of cells is cells'; e and
cells' meet ReadsAs at Zp.p.X; the parameters are the description's own; the planner's four
arguments are its own; the premise on the trace is TraceOwnAt e. mats is free. All else that the
docstring of sessionStops_of_tiedOwn says holds here too, with TraceOwnAt e for TraceOwn,
Spec.model_meets_ownAt for the prover of which it is proved, and Spec.const_not_ownAt for
const_not_own. -/
def Spec.sessionStops_of_tiedOwn_at : Prop :=
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
    (cells' : Tr' → ProofFile.Honest.Cells) (e : Tr → Tr') (_hE : ReadsAs Zp.p.X cells' e)
    (_h₁ : RowsPinned (parOwn Zp mats) cells' (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) cells' (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (_hO : TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes e)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

/-- **Under ReadsAs and TraceOwnAt e, at every tied request of Yes at which H.trace answers, the
cells that the pinned part reads at matsOf are the entries of the model's trace**, at an index that
the input's matrix holds and the instance that is read off the input's written instance. -/
def Spec.cells_are_trace_at : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (cells' : Tr' → ProofFile.Honest.Cells) (e : Tr → Tr') (_hE : ReadsAs Zp.p.X cells' e)
    (_hO : TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes e),
    AtTiedAt Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
      ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        ProofFile.instOf (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧
        ∀ l < 25, ∀ mu r c,
          ProofFile.Honest.K8.cellsAtOf (cells' tr) (matsOf Zp.p.X l) mu r c =
            theTrace Zp.p.X i x l mu r c

/-- A control; it counts as no goal. **A prover whose trace field is modelAt Zp.p.X e meets
TraceOwnAt e, at all rows G, every Yes and every e.** Nothing is said of that prover's rows. -/
def Spec.model_meets_ownAt : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (Yes : FullSizeMatrix → XF → Prop) (e : Tr → Tr'),
    TraceOwnAt Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X e } Yes e

/-- A control; it counts as no goal. **At public files in scope that can be read and pass protocolDataWellFormed,
under LaidAt: at that prover, at all rows G and Yes := RyesZ Z, some tied request of Yes has a
trace.** That prover meets TraceOwnAt e (Spec.model_meets_ownAt). So Spec.cells_are_trace_at does
not hold idly there at a reader cells' that meets ReadsAs with e: so at the two pairs of letters of
Spec.readsAs_id and Spec.readsAs_cells. At an e with which no reader meets ReadsAs it holds idly
there too. Nothing is said of that prover's rows. -/
def Spec.ownAt_speaks : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh) (e : Tr → Tr')
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF),
    ∃ (n : ℕ) (w : WZ Z) (a : XF × RecFull) (tr : Tr'),
      TiedYes Z Zp Np cF run₂ run₃ B G { H₀ with trace := modelAt Zp.p.X e } (RyesZ Z)
        n w (LPFD.Full.instanceAsPlainRecord a) ∧
      modelAt Zp.p.X e w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr

/-- A negative test; it counts as no goal. At public files in scope that can be read, under LaidAt:
the function that answers the reader 0 at every trace does not meet ReadsAs at the reader id. -/
def Spec.zero_reader_not_readsAs : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ¬ ReadsAs Zp.p.X id fun _ => (⟨fun _ _ _ _ => 0⟩ : ProofFile.Honest.Cells)

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt: a prover whose trace function answers the constant reader 129 at one typed
request of Yes and the input's own seed, at a matrix that holds an index which serves it, does not
meet TraceOwnAt (cellsC Zp.p.X).** The constant reader 129 is cellsC Zp.p.X T at no trace T (cellsC
yields 0 from the number 25 on), so this test does not tell TraceOwnAt from a premise that asks only
that the trace be cellsC Zp.p.X of some trace. Spec.const_not_ownAt does. -/
def Spec.const_fails_ownAt : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey ProofFile.Honest.Cells X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey ProofFile.Honest.Cells X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (w : WZ Z) (x' : XF) (i : Cm.Idx) (_hy : Yes w.1 x')
    (_hi : VerifiableInference.OnPublicFiles.Flat.Holds w.1 i) (_T : ServesAt Zp.p.X i x'.val)
    (_ha : H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) =
      some ⟨fun _ _ _ _ => 129⟩),
    ¬ TraceOwnAt Z Zp Np cF run₂ run₃ B G H Yes (cellsC Zp.p.X)

/-- A negative test; it counts as no goal. **At public files in scope that can be read and pass
protocolDataWellFormed, under LaidAt, at every e and cells' that meet ReadsAs: a prover whose trace function
answers e of the constant trace 129 everywhere does not meet TraceOwnAt e at Yes := RyesZ Z.** That
trace is among those that e is laid on; it is no trace of the model, whose entries are below 129 in
absolute value. -/
def Spec.const_not_ownAt : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (cells' : Tr' → ProofFile.Honest.Cells) (e : Tr → Tr') (_hE : ReadsAs Zp.p.X cells' e),
    ¬ TraceOwnAt Z Zp Np cF run₂ run₃ B G
      { H₀ with trace := fun _ _ => some (e fun _ _ _ _ => 129) } (RyesZ Z) e

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_traceOwnAtSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_traceOwnAtSpec
#print axioms OnBytes.FrontRoad.ReadsAs
#print axioms OnBytes.FrontRoad.modelAt
#print axioms OnBytes.FrontRoad.AtTiedAt
#print axioms OnBytes.FrontRoad.TraceOwnAt
#print axioms OnBytes.FrontRoad.Spec.readsAs_id
#print axioms OnBytes.FrontRoad.Spec.readsAs_cells
#print axioms OnBytes.FrontRoad.Spec.traceOwnAt_id
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_tiedOwn_at
#print axioms OnBytes.FrontRoad.Spec.cells_are_trace_at
#print axioms OnBytes.FrontRoad.Spec.model_meets_ownAt
#print axioms OnBytes.FrontRoad.Spec.ownAt_speaks
#print axioms OnBytes.FrontRoad.Spec.zero_reader_not_readsAs
#print axioms OnBytes.FrontRoad.Spec.const_fails_ownAt
#print axioms OnBytes.FrontRoad.Spec.const_not_ownAt
