-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/CellsAreTraceSpec.lean: statements only. Under TraceOwn, at every tied request of
Yes at which the prover's trace function answers, the cells that the pinned part of the smallness
test reads at the list of matrices matsOf Zp.p.X l (Johnson/HonestTrace/DigitsAtTrace.lean) are the
entries of the model's trace. So in the implication sessionStops_of_tiedOwn, at the description's
own parameters and this list, the pin speaks of a part whose private abort test reads that trace's
entries, and no longer of one that reads the zeros which a list of wrong names yields. Four
statements, two controls and two negative tests. Proved in Johnson/FrontRoad/CellsAreTrace.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  emptyNames   for a negative test: as many keys as matsOf X l has, each with the number l, the
      empty string and the first column 0.
  Spec.matsOf_fits   on public data. At each link l below 25 parOwn Zp (matsOf Zp.p.X) names, at the
      written place of the smallness test, the description's own parameters and matsOf Zp.p.X l, and
      the public test smallFits (Johnson/Desc/ProofFile/Honest/K8/Part.lean) passes there: the list
      is as long as the place has matrices, and the place has a number of rows for each.
  Spec.reads_theTrace   at every index i and instance x that i serves: read through matsOf Zp.p.X l,
      the reader cellsC Zp.p.X at the trace theTrace Zp.p.X i x yields that trace's own entry, at
      each link l below 25 and all numbers mu, r, c. It is cellsAtOf_matsOf
      (Johnson/HonestTrace/DigitsAtTrace.lean) at theTrace.
  Spec.cells_are_trace   under the four public premises and TraceOwn
      (Johnson/FrontRoad/TracePremises.lean): at every tied request of Yes at which H.trace answers
      a trace tr, there are an index i that the input's matrix holds and the instance x that
      ProofFile.instOf reads off the input's written instance, such that i serves x and, at each link
      below 25 and all mu, r, c, the cell cellsAtOf (cellsC Zp.p.X tr) (matsOf Zp.p.X l) mu r c is
      theTrace Zp.p.X i x l mu r c.
  Spec.sessionStops_of_tiedOwn_matsOf   sessionStops_of_tiedOwn_files
      (Johnson/FrontRoad/ParOwnChecksSpec.lean) at mats := matsOf Zp.p.X. No letter is left for the
      parameters, for the list, or for the planner's four arguments. So, of the implications that
      end in the condition of the field sessionStops (PremWDebts, E2E/BridgeDebts.lean), this is the
      one to name for that field. What is to be said of its premise TraceOwn stands in the Limits of
      Johnson/FrontRoad/TracePremises.lean.
  Spec.cells_are_trace_speaks   a control: at a prover whose trace field is viaIndex (modelTrace
      Zp.p.X), at all rows G and Yes := RyesZ Z, some tied request of Yes has a trace. So
      Spec.cells_are_trace does not hold idly there.
  Spec.matsOf_reads_ones   a control: at the constant trace 1 the reader yields 1 at every member of
      matsOf Zp.p.X l, at each link l below 25. That the list has a member is not in this statement:
      it has 9, 5 or 8 (matsOf_length, Johnson/HonestTrace/DigitsAtTrace.lean).
  Spec.empty_names_fit_and_read_zero   a negative test: at emptyNames the public test smallFits
      passes too, and the reader yields 0 at every trace and all numbers. So the one public test
      that the pin lays on the list passes at both lists; at the constant trace 1 the two lists give
      two readings (Spec.matsOf_reads_ones). That the pin at that list asks of the rows another part
      than the pin at matsOf does is by inspection, not proved: the part reads its cells through the
      window test alone (leaves, Johnson/Desc/K8/Honest/Window.lean), so it also wants a row, a
      column and a combination at the place. The equation of Spec.reads_theTrace fails at that list
      at every trace with an entry that is not 0 at a link below 25; that theTrace has such an entry
      at any served instance is not said here.
  Spec.short_names_do_not_fit   a negative test: at matsOf Zp.p.X l without its last member
      smallFits fails.

How it fits. The pinned part reads its cells as cellsAtOf (cells tr) P.2, and of the list P.2 the
pin holds the length alone (smallFits). In parOwn Zp mats the letter mats was free: at a list of the
right length whose strings are no labels the reader cellsC yields zeros, the pinned part's private
abort test reads zeros alone, and the implication bounds aborts of a part that says nothing of the
trace (sessionStops_of_tiedOwn has no premise on the cells: TraceOwn stands in its place, and is no
easier to meet at such a list). Spec.empty_names_fit_and_read_zero has such a list. Here mats is
matsOf Zp.p.X. Words (member, half, part, public and private abort test, stated share):
Johnson/FrontRoad/SessionStopsPinned.lean. Not one of the release's goal statements.

Limits.
  No whole prover is named: Spec.cells_are_trace_speaks names a trace field alone. The pin, hR and
      TraceOwn stay premises of the implication; no book, rows and prover are known at which they
      hold together. No value is given for the bound. At public files that do not meet scope, the
      reading and LaidAt (with protocolDataWellFormed, where it is a premise) every statement here holds idly, the
      two controls and the two negative tests among them. That these are met together is proved of
      one stored set of files, VerifierAndGoals.storedPublicFiles, in the side library (premises_met_at_full,
      AtFullSide/Top/LaidAtFull.lean).
  Spec.cells_are_trace holds idly where no tied request of Yes has a trace: so at a prover whose
      trace function never answers, which meets TraceOwn (none_meets_ownRel,
      Johnson/FrontRoad/TracePremisesTests.lean, with own_of_ownRel,
      Johnson/FrontRoad/TracePremises.lean; no one theorem states it). It does speak at a prover
      whose trace field is viaIndex (modelTrace Zp.p.X), at Yes := RyesZ Z
      (Spec.cells_are_trace_speaks); of that prover's rows nothing is known.
  The one served typed request that is known (servedTyped_exists,
      Johnson/FrontRoad/ServedExists.lean) is, by inspection, at the all-zero weights. What
      Spec.reads_theTrace says there is an equation between two readings of that trace; whether that
      trace has an entry that is not 0 is not said. That there is a trace at which the reader at
      matsOf yields something other than 0 is Spec.matsOf_reads_ones: the constant trace 1, which is
      no trace of the model. Of the model's trace it says nothing.
  Which list the library's honest rows for the whole description lay at the smallness test is not
      said here. By their author's account, not read here, they lay the list K3.matsOwn of the kind
      "lookup". By the head of Johnson/Desc/ProofFile/Honest/K3/Law/WitOwnerFull.lean (a file which
      this library may not hold) that list is matsOf at each link below 25 under two conditions on
      the public data, both of which are theorems in scope (planMarks_in_scope,
      Johnson/Goal/HonestTrace/PlanMarksInScope.lean; partsFit_in_scope,
      Johnson/Goal/HonestTrace/FromCellsInScope.lean). No theorem joins them yet, and none is stated
      here.
  The two readers are not bridged. By the same account these rows lay the part at the reader id, at
      a trace type that is the type of readers of cells itself; here the reader is cellsC Zp.p.X, at
      the type Tr of Johnson/HonestTrace/Full.lean. That one prover's rows are pinned at this reader
      and its trace function meets TraceOwn is not proved.
  The full size alone: cellsC and matsOf number the segments as a proof with twelve groups of layers
      does. That the rows and columns which the test walks at member mu (the ms and ks of k8Par) are
      those of matrix mu of theTrace at l is not stated here; Spec.matsOf_fits has the length alone.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.ParOwnChecksSpec

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
local instance (priority := high) nonemptyPadZ_cellsAreTraceSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_cellsAreTraceSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- For a negative test: as many keys as matsOf X l has, each with the number l, the empty string
and the first column 0. -/
def emptyNames (X : OnBytes.Model.Verify.Public) (l : ℕ) : List (ℕ × String × ℕ) :=
  List.replicate (matsOf X l).length (l, "", 0)

/-- **At each link below 25 parOwn Zp (matsOf Zp.p.X) names the description's own parameters and
matsOf Zp.p.X l, and the public test smallFits passes there.** -/
def Spec.matsOf_fits : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ l < 25, ∃ G₀ Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      parOwn Zp (matsOf Zp.p.X) (k8PlaceAt l) =
        some (ProofFile.k8Par Zp G₀ Xl l, matsOf Zp.p.X l) ∧
      ProofFile.Honest.K8.smallFits (ProofFile.k8Par Zp G₀ Xl l, matsOf Zp.p.X l) = true

/-- **Read through matsOf, the reader cellsC at the model's trace yields that trace's own entries**,
at every index and instance that the index serves. -/
def Spec.reads_theTrace : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ (i : Cm.Idx) (x : Instance ppref), ServesAt Zp.p.X i x → ∀ l < 25, ∀ mu r c,
      ProofFile.Honest.K8.cellsAtOf (cellsC Zp.p.X (theTrace Zp.p.X i x)) (matsOf Zp.p.X l) mu r c =
        theTrace Zp.p.X i x l mu r c

/-- **Under TraceOwn, at every tied request of Yes at which H.trace answers, the cells that the
pinned part reads at matsOf are the entries of the model's trace**, at an index that the input's
matrix holds and the instance that is read off the input's written instance. -/
def Spec.cells_are_trace : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (Yes : FullSizeMatrix → XF → Prop)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (_hO : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes),
    AtTied Z Zp Np cF run₂ run₃ B G H Yes fun w a tr =>
      ∃ (i : Cm.Idx) (x : Instance ppref), VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        ProofFile.instOf (LPFD.Full.instanceAsPlainRecord a) = some x ∧ ServesAt Zp.p.X i x ∧
        ∀ l < 25, ∀ mu r c,
          ProofFile.Honest.K8.cellsAtOf (cellsC Zp.p.X tr) (matsOf Zp.p.X l) mu r c =
            theTrace Zp.p.X i x l mu r c

/-- **sessionStops_of_tiedOwn_files at mats := matsOf Zp.p.X.** The reader of cells is cellsC
Zp.p.X; the parameters are the description's own; the list is matsOf Zp.p.X; the planner's four
arguments are its own; the premise on the trace is TraceOwn. All else that the docstring of
sessionStops_of_tiedOwn says holds here too. -/
def Spec.sessionStops_of_tiedOwn_matsOf : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop)
    (_h₁ : RowsPinned (parOwn Zp (matsOf Zp.p.X)) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (_hO : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

/-- A control; it counts as no goal. **At a prover whose trace field is viaIndex (modelTrace
Zp.p.X), at all rows G and Yes := RyesZ Z, some tied request of Yes has a trace.** Such a prover
meets TraceOwn (model_meets_own, Johnson/FrontRoad/TracePremisesTests.lean): so Spec.cells_are_trace
does not hold idly there. Nothing is said of that prover's rows: they are not known to be pinned. -/
def Spec.cells_are_trace_speaks : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF),
    ∃ (n : ℕ) (w : WZ Z) (a : XF × RecFull) (tr : Tr),
      TiedYes Z Zp Np cF run₂ run₃ B G { H₀ with trace := viaIndex (modelTrace Zp.p.X) } (RyesZ Z)
        n w (LPFD.Full.instanceAsPlainRecord a) ∧
      viaIndex (modelTrace Zp.p.X) w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr

/-- A control; it counts as no goal. **At the constant trace 1 the reader yields 1 at every member
of matsOf Zp.p.X l**, where it yields 0 at every member of emptyNames Zp.p.X l: the two lists give
two readings, since matsOf Zp.p.X l has a member: 9, 5 or 8 (matsOf_length,
Johnson/HonestTrace/DigitsAtTrace.lean; here it follows from Spec.matsOf_fits with
Spec.short_names_do_not_fit). That they give two parts is by inspection, not proved. The constant
trace is no trace of the model. -/
def Spec.matsOf_reads_ones : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ l < 25, ∀ mu < (matsOf Zp.p.X l).length, ∀ r c : ℕ,
      ProofFile.Honest.K8.cellsAtOf (cellsC Zp.p.X fun _ _ _ _ => 1) (matsOf Zp.p.X l) mu r c = 1

/-- A negative test; it counts as no goal. **At emptyNames the public test smallFits passes too, and
the reader yields 0 at every trace.** -/
def Spec.empty_names_fit_and_read_zero : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ l < 25, ∃ G₀ Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      ProofFile.Honest.K8.smallFits (ProofFile.k8Par Zp G₀ Xl l, emptyNames Zp.p.X l) = true ∧
      ∀ (T : Tr) (mu r c : ℕ),
        ProofFile.Honest.K8.cellsAtOf (cellsC Zp.p.X T) (emptyNames Zp.p.X l) mu r c = 0

/-- A negative test; it counts as no goal. At matsOf Zp.p.X l without its last member smallFits
fails. -/
def Spec.short_names_do_not_fit : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ l < 25, ∀ G₀ Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → G₀.built[l]? = some Xl →
      ProofFile.Honest.K8.smallFits (ProofFile.k8Par Zp G₀ Xl l, (matsOf Zp.p.X l).dropLast) = false

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_cellsAreTraceSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_cellsAreTraceSpec
#print axioms OnBytes.FrontRoad.emptyNames
#print axioms OnBytes.FrontRoad.Spec.matsOf_fits
#print axioms OnBytes.FrontRoad.Spec.reads_theTrace
#print axioms OnBytes.FrontRoad.Spec.cells_are_trace
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_tiedOwn_matsOf
#print axioms OnBytes.FrontRoad.Spec.empty_names_fit_and_read_zero
#print axioms OnBytes.FrontRoad.Spec.short_names_do_not_fit
#print axioms OnBytes.FrontRoad.Spec.cells_are_trace_speaks
#print axioms OnBytes.FrontRoad.Spec.matsOf_reads_ones
