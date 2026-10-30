-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsOfTrace.lean: ten implications, side by side, each with the conclusion
of sessionStops_of_pinned (Johnson/FrontRoad/SessionStopsOfPinned.lean): the condition HidSmall at
the family famG, at the planner's bound. The reader of cells is cellsC X, the reader of a trace of
the integer model (Johnson/HonestTrace/DigitsAtTrace.lean). The premise on the cells is gone; in its
place stands one of the premises on the trace of Johnson/FrontRoad/TracePremises.lean. In nine of
them that premise says something of the traces at requests: the debt has moved, not shrunk. In the
tenth it is an equation on the prover's trace field, the strongest of the premises: there the debt
has moved once more, to whether the other premises on H hold at a prover with that field. The values
that par names are free; l, oneTime, columnsFirst and batches are free: tied to nothing here.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
Each is sessionStops_of_pinned at cells := cellsC X with its premise hP replaced. The premises are
said in full in Johnson/FrontRoad/TracePremises.lean, with the theorems on which gives which.
  sessionStops_of_smallTrace   from TraceSmall; at every X. TraceSmall is more than hP, which reads
      those cells alone that the lists name (by inspection, not proved): here the debt has grown.
  sessionStops_of_trace   from TraceServed; at X := Zp.p.X, as all that follow. The trace of another
      index's run meets TraceServed.
  sessionStops_of_plain   from TracePlain rd; rd is free.
  sessionStops_of_hinge   from TraceHinge Zp.p.X trace rd (Johnson/HonestTrace/TraceHinge.lean) and
      TraceThrough trace; trace and rd are free but for TraceHinge. The index is the input's own,
      and the instance is the one that rd reads off the input's bytes.
  sessionStops_of_tiedOwn   from TraceOwn. Index and instance are the input's own: the index that
      the matrix holds, and the typed request of which the input's instance is written. That the
      index serves the request is paid from the statement's own "tied" (served_of_valid; the field
      rel of Tied).
  sessionStops_of_tied, sessionStops_of_yes   two corollaries of sessionStops_of_tiedOwn: from
      TraceOwnRel (at the whole relation; it does not name Yes), and from TraceOwnYes (at the
      requests of Yes).
  sessionStops_of_valid   sessionStops_of_yes with one premise more, hY: every request of Yes is in
      the relation RyesZ Z. No proof uses hY.
  sessionStops_of_tied_hinge   sessionStops_of_tied with TraceOwnRel replaced: H.trace goes, at an
      index that the matrix holds, through a trace function that meets TraceHinge at the reader
      ProofFile.instOf (ownRel_of_through). sessionStops_of_model: sessionStops_of_tied with TraceOwnRel
      replaced by TraceIsModel: the prover's trace field is the written function viaIndex
      (modelTrace Zp.p.X) (ownRel_of_model). TraceIsModel binds every matrix and every written
      instance and reads both, as an equation between functions; it assumes of no request that it is
      in the relation, served or small. hR binds one input. That acceptance, or the other premise of
      the implication on index privacy that names H (the field rows of PremWDebts,
      E2E/BridgeDebts.lean), holds at a prover with that trace field is not proved; no parameters
      are known at which that list's fields hold together.

How it fits. Which premise gives which: TraceThrough with TraceHinge gives TracePlain, and
TracePlain gives them back at a written trace function; TracePlain gives TraceServed; TraceServed
gives TraceSmall, at the public premises; TraceSmall gives hP. TracePlain at the reader ProofFile.instOf
gives TraceOwn, and, at public files in scope that can be read and pass protocolDataWellFormed, under LaidAt,
TraceOwn gives it back. TraceOwnRel and TraceOwnYes each give TraceOwn, and at the public premises
TraceOwn gives TraceOwnYes back: so there TraceOwn, TraceOwnYes and TracePlain at ProofFile.instOf are one
premise in three forms, and TraceHinge at ProofFile.instOf with TraceThrough, at some trace function, is a
fourth; there too TraceOwnRel, and the two premises of sessionStops_of_tied_hinge at some trace
function, are one premise (ownRel_of_through, throughRel_of_ownRel). TraceIsModel gives TraceOwnRel.
The measure is HidSmall's own, as in sessionStops_of_pinned. Words (member, half, part, public and
private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Glue; not one of the
release's goal statements.

Limits.
  No parameters are known at which the premises of any of the ten hold together. No value is given
      for the bound.
  In the first nine the premise on the trace is the one premise that says something of the traces at
      requests; hR binds one input, and the pin binds every input with its trace, as in the tenth.
      Of TraceOwn: It is proved only of a prover whose trace field is laid so by definition, and of
      no prover whose rows are pinned. TraceOwnRel and TraceOwnYes are proved too, idly, of a prover
      whose trace function never answers (none_meets_ownRel, none_meets_ownYes); of TraceSmall,
      TraceServed, TracePlain and TraceThrough no theorem states it of any prover. So laid: as
      viaIndex (modelTrace Zp.p.X) (model_meets_ownRel, with model_answers: that function answers
      wherever an index serves a typed request; Johnson/FrontRoad/TracePremisesTests.lean).
  Paid from the statement's own "tied" is this alone, in sessionStops_of_tiedOwn and its
      corollaries: that an index which the matrix holds serves the request. That the cells are small
      is not.
  Asked by no premise here, and proved by nothing here: that a tied request of Yes has a trace at
      all; that the list P.2 which par names at a place (the parameter mats of smallLot,
      Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
      (Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
      description's test covers there, by owner, label and first column; that what the other kinds'
      parts send is read off the same reader. In sessionStops_of_model the first of these follows
      from TraceIsModel (trace_there_of_model). In sessionStops_of_smallTrace also: that the trace
      is theTrace at any index and instance at all. In sessionStops_of_trace also: that the index
      and the instance are the input's own. In sessionStops_of_plain and sessionStops_of_hinge also:
      that rd reads what the request's written instance holds.
  Yes is free. A tied request is written of some typed request in the relation RyesZ Z already.
  A prover whose H.trace never answers does not meet hR (ready refuses where the request has no
      trace, Johnson/Desc/ProofFile/Honest/Frame.lean; by inspection, not proved); hR asks a trace
      at one input of the caller's choice alone.
  The pin is narrower than in sessionStops_of_pinned: it asks the part at the reader cellsC X. That
      any prover's rows are pinned is not proved here.
  The full size alone, in all ten. theTrace is noncomputable.
  It is vacuous at rows that always abort publicly, at lists P.2 whose strings are no labels (there
      the reader yields zeros alone), in the first nine where no tied request of Yes has a trace, in
      the tenth where Yes has no tied request and where no index serves an instance (there hR
      fails), and at sec = 0 with at most one slot, one batch and one copy, where the bound is 1.
      All limits of Johnson/FrontRoad/SessionStopsOfPinned.lean and
      Johnson/FrontRoad/TracePremises.lean hold.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.TracePremises

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
local instance (priority := high) nonemptyPadZ_ofTrace : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_ofTrace {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **An implication: HidSmall at famG at the planner's bound, from the premises of
sessionStops_of_pinned at the reader cellsC X, with the premise on the cells replaced by TraceSmall:
at every tied request of Yes every entry of the trace that H.trace returns is below 129 in absolute
value.** X is free: tied to nothing here. TraceSmall is more than the premise that it replaces (by
inspection, not proved): here the debt has grown. The values that par names are free; l, oneTime,
columnsFirst and batches are free: tied to nothing here. The reader of cells is cellsC X. The
premise on the cells is gone; in its place stands TraceSmall: the debt has moved, not shrunk. It is
a premise; of which provers it is proved stands in the Limits of
Johnson/FrontRoad/TracePremises.lean. It is vacuous at rows that always abort publicly, at lists P.2
whose strings are no labels (there the reader yields zeros alone), where no tied request of Yes has
a trace, and at sec = 0 with at most one slot, one batch and one copy, where the bound is 1. Asked
by no premise here, and proved by nothing here: that the trace is theTrace at any index and instance
at all; that a tied request of Yes has a trace at all; that the list P.2 which par names at a place
(the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_smallTrace (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (X : OnBytes.Model.Verify.Public)
    (h₁ : RowsPinned par (cellsC X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hS : TraceSmall Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_pinned Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par (cellsC X) l
    oneTime columnsFirst batches h₁ h₃ hm
    (cells_of_small Z Zp Np cF run₂ run₃ B G H Yes hS X par _) ok Gs

/-- **The same at X := Zp.p.X, from TraceServed: the trace is theTrace Zp.p.X i x at some index i
and instance x that i serves.** Nothing ties i and x to the input: the trace of another index's run
meets TraceServed. The values that par names are free; l, oneTime, columnsFirst and batches are
free: tied to nothing here. The reader of cells is cellsC Zp.p.X. The premise on the cells is gone;
in its place stands TraceServed: the debt has moved, not shrunk. It is a premise; of which provers
it is proved stands in the Limits of Johnson/FrontRoad/TracePremises.lean. It is vacuous at rows
that always abort publicly, at lists P.2 whose strings are no labels (there the reader yields zeros
alone), where no tied request of Yes has a trace, and at sec = 0 with at most one slot, one batch
and one copy, where the bound is 1. Asked by no premise here, and proved by nothing here: that the
index and the instance at which the trace is theTrace are the input's own; that a tied request of
Yes has a trace at all; that the list P.2 which par names at a place (the parameter mats of
smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_trace (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hT : TraceServed Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_smallTrace Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches Zp.p.X h₁ h₃ hm
    (small_of_served Z Zp Np cF run₂ run₃ B G H Yes scope hr live L hT) ok Gs

/-- **The same from TracePlain rd: the trace is theTrace Zp.p.X i x at an index i that the input's
matrix holds and an instance x that rd reads off the input's written instance and i serves.** rd is
free. The clauses on Holds and on rd are used by no proof. The values that par names are free; l,
oneTime, columnsFirst and batches are free: tied to nothing here. The reader of cells is cellsC
Zp.p.X. The premise on the cells is gone; in its place stands TracePlain rd: the debt has moved, not
shrunk. It is a premise; of which provers it is proved stands in the Limits of
Johnson/FrontRoad/TracePremises.lean. It is vacuous at rows that always abort publicly, at lists P.2
whose strings are no labels (there the reader yields zeros alone), where no tied request of Yes has
a trace, and at sec = 0 with at most one slot, one batch and one copy, where the bound is 1. Asked
by no premise here, and proved by nothing here: that rd reads what the request's written instance
holds; that a tied request of Yes has a trace at all; that the list P.2 which par names at a place
(the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_plain (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (rd : ProofFile.Inst → Option (Instance ppref)) (hQ : TracePlain Z Zp Np cF run₂ run₃ B G H Yes rd)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_trace Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (served_of_plain Z Zp Np cF run₂ run₃ B G H Yes rd hQ) ok Gs

/-- **The same where the trace goes through a trace function that meets TraceHinge at Zp.p.X, at an
index that the input's matrix holds: so the index is the input's own, and the instance is the one
that rd reads off the input's bytes.** trace and rd are free but for hh. The clause on Holds, and
what hh says of rd, are used by no proof. The values that par names are free; l, oneTime,
columnsFirst and batches are free: tied to nothing here. The reader of cells is cellsC Zp.p.X. The
premise on the cells is gone; in its place stands TraceThrough trace, with TraceHinge: the debt has
moved, not shrunk. It is a premise; of which provers it is proved stands in the Limits of
Johnson/FrontRoad/TracePremises.lean. It is vacuous at rows that always abort publicly, at lists P.2
whose strings are no labels (there the reader yields zeros alone), where no tied request of Yes has
a trace, and at sec = 0 with at most one slot, one batch and one copy, where the bound is 1. Asked
by no premise here, and proved by nothing here: that rd reads what the request's written instance
holds; that a tied request of Yes has a trace at all; that the list P.2 which par names at a place
(the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_hinge (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (trace : Cm.Idx → ProofFile.Inst → Option Tr) (rd : ProofFile.Inst → Option (Instance ppref))
    (hh : TraceHinge Zp.p.X trace rd) (hH : TraceThrough Z Zp Np cF run₂ run₃ B G H Yes trace)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_plain Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm rd
    (plain_of_through Z Zp Np cF run₂ run₃ B G H Yes trace rd hh hH) ok Gs

/-- **The same from TraceOwn: at every tied request of Yes, of whichever typed request in the
relation RyesZ Z the input's instance is written, the trace that H.trace returns is theTrace at the
index that the matrix holds, where that index serves the request, and at that typed request's own
instance.** Index and instance are the input's own. That an index which the matrix holds serves the
request is paid from the statement's own "tied": the field rel of Tied
(Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean), at RyesZ Z in TiedG
(E2E/BridgeLinkAtFiles.lean). That the cells are small is not paid from it. The values that par
names are free; l, oneTime, columnsFirst and batches are free: tied to nothing here. The reader of
cells is cellsC Zp.p.X. The premise on the cells is gone; in its place stands TraceOwn: the debt has
moved, not shrunk. It is proved only of a prover whose trace field is laid so by definition, and of
no prover whose rows are pinned. It can fail (const_not_own, Johnson/FrontRoad/ServedExists.lean).
It is vacuous at rows that always abort publicly, at lists P.2 whose strings are no labels (there
the reader yields zeros alone), where no tied request of Yes has a trace, and at sec = 0 with at
most one slot, one batch and one copy, where the bound is 1. Asked by no premise here, and proved by
nothing here: that a tied request of Yes has a trace at all; that the list P.2 which par names at a
place (the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X
k (Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_tiedOwn (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hO : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_trace Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (served_of_own Z Zp Np cF run₂ run₃ B G H Yes scope hr live L hO) ok Gs

/-- **A corollary of sessionStops_of_tiedOwn, from TraceOwnRel: the like at every private input and
every typed request in the relation RyesZ Z, at every OOD seed.** No premise names Yes: TraceOwnRel
is asked at every typed request in the relation, also outside Yes. The seed is bound by "for all"
and need not be the input's own. The values that par names are free; l, oneTime, columnsFirst and
batches are free: tied to nothing here. The reader of cells is cellsC Zp.p.X. The premise on the
cells is gone; in its place stands TraceOwnRel: the debt has moved, not shrunk. It is a premise; of
which provers it is proved stands in the Limits of Johnson/FrontRoad/TracePremises.lean. It is
vacuous at rows that always abort publicly, at lists P.2 whose strings are no labels (there the
reader yields zeros alone), where no tied request of Yes has a trace, and at sec = 0 with at most
one slot, one batch and one copy, where the bound is 1. Asked by no premise here, and proved by
nothing here: that a tied request of Yes has a trace at all; that the list P.2 which par names at a
place (the parameter mats of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X
k (Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_tied (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hV : TraceOwnRel Z Zp H)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_tiedOwn Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (own_of_ownRel Z Zp Np cF run₂ run₃ B G H Yes hV) ok Gs

/-- **A corollary of sessionStops_of_tiedOwn, from TraceOwnYes: the like at every private input and
every typed request of Yes, at the input's own seed.** It asks nothing outside Yes. The values that
par names are free; l, oneTime, columnsFirst and batches are free: tied to nothing here. The reader
of cells is cellsC Zp.p.X. The premise on the cells is gone; in its place stands TraceOwnYes: the
debt has moved, not shrunk. It is a premise; of which provers it is proved stands in the Limits of
Johnson/FrontRoad/TracePremises.lean. It is vacuous at rows that always abort publicly, at lists P.2
whose strings are no labels (there the reader yields zeros alone), where no tied request of Yes has
a trace, and at sec = 0 with at most one slot, one batch and one copy, where the bound is 1. Asked
by no premise here, and proved by nothing here: that a tied request of Yes has a trace at all; that
the list P.2 which par names at a place (the parameter mats of smallLot,
Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_yes (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hV : TraceOwnYes Z Zp H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_tiedOwn Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (own_of_ownYes Z Zp Np cF run₂ run₃ B G H Yes hV) ok Gs

/-- **sessionStops_of_yes with one premise more, hY: every request of Yes is in the relation RyesZ
Z.** No proof uses hY: a tied request is written of a typed request in the relation already, and the
writer is one to one in the typed request. All that the docstring of sessionStops_of_yes says is
free, vacuous or not asked holds here too. -/
theorem sessionStops_of_valid (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (_hY : ∀ m x', Yes m x' → RyesZ Z m x') (hV : TraceOwnYes Z Zp H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_yes Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm hV ok Gs

/-- **sessionStops_of_tied with TraceHinge in TraceOwnRel's place**: at a typed request in the
relation, where H.trace answers, the matrix holds an index at which a trace function gives that
answer, and that function meets TraceHinge at Zp.p.X and the reader ProofFile.instOf. Index and instance
are the input's own. hh and hH are premises. All that the docstring of sessionStops_of_tied says is
free, vacuous or not asked holds here too. -/
theorem sessionStops_of_tied_hinge (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (trace : Cm.Idx → ProofFile.Inst → Option Tr) (hh : TraceHinge Zp.p.X trace ProofFile.instOf)
    (hH : ∀ (w : WZ Z) (x' : XF) (s : (protocolAtFiles Z).OutOfDomainSeed) (tr : Tr), RyesZ Z w.1 x' →
      H.trace w.1 (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds w.1 i ∧
        trace i (LPFD.Full.instanceAsPlainRecord (x', (s, ansAt (AZ Z) PadZ (holdZ Z) w.1 w.2.1 s))) = some tr)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_tied Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (ownRel_of_through Z Zp H trace hh hH) ok Gs

/-- **sessionStops_of_tied with TraceOwnRel replaced by TraceIsModel: the prover's trace field is
the written function viaIndex (modelTrace Zp.p.X).** TraceIsModel is an equation on one field of H.
It binds every matrix and every written instance and reads both: as H.trace's arguments, in indexOf
and in ProofFile.instOf (of a written instance that reader takes the request's and the reply's bytes
alone, not the key). It assumes of no request that it is in the relation, served or small. The pin
binds every input with its trace, in its second alternative: a condition on the parts. hR binds one
input of the caller's choice. The other premises bind no index, no pads, no OOD seed, no instance
and no trace. Not proved here, and asked by no premise: that acceptance, or the other premise of the
implication on index privacy that names H (the field rows of PremWDebts, E2E/BridgeDebts.lean),
holds at a prover with that trace field. No parameters are known at which that list's fields hold
together. The function is noncomputable, at the full size alone; no program runs it. hR then asks
that one request is read by ProofFile.instOf and served by the index that its matrix holds. Every written
instance is read (instOf_at_frame, Johnson/Desc/ProofFile/InstOfTies.lean); that one is served is
servedTyped_exists (Johnson/FrontRoad/ServedExists.lean), at the all-zero weights. No parameters are
known at which the premises of sessionStops_of_model hold together; that any prover's rows are
pinned is not proved here. At every tied request of Yes the trace is there (trace_there_of_model,
Johnson/FrontRoad/TracePremises.lean). The values that par names are free; l, oneTime, columnsFirst
and batches are free: tied to nothing here. The reader of cells is cellsC Zp.p.X. It is vacuous at
rows that always abort publicly, at lists P.2 whose strings are no labels (there the reader yields
zeros alone), where Yes has no tied request, where no index serves an instance (there hR fails), and
at sec = 0 with at most one slot, one batch and one copy, where the bound is 1. Asked by no premise
here, and proved by nothing here: that the list P.2 which par names at a place (the parameter mats
of smallLot, Johnson/Desc/ProofFile/Honest/K8/Part.lean) is matsOf Zp.p.X k
(Johnson/HonestTrace/DigitsAtTrace.lean), and that this is the list of the matrices that the
description's test covers there, by owner, label and first column; that what the other kinds' parts
send is read off the same reader. -/
theorem sessionStops_of_model (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (l : Lines) (oneTime columnsFirst batches : ℕ)
    (h₁ : RowsPinned par (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (hm : missedInTheChecks l
      (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => par b.place).map
        (·.1))) oneTime columnsFirst batches = false)
    (hM : TraceIsModel Z Zp H)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-((l.sec : ℝ) + (clog2 l.slots : ℝ) +
        (clog2 (max 1 batches) : ℝ) +
        (clog2 (plannedCopies l oneTime columnsFirst) : ℝ)))) + 0) :=
  sessionStops_of_tied Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes par l oneTime
    columnsFirst batches h₁ h₃ hm
    (ownRel_of_model Z Zp H hM) ok Gs

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_ofTrace
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_ofTrace
#print axioms OnBytes.FrontRoad.sessionStops_of_smallTrace
#print axioms OnBytes.FrontRoad.sessionStops_of_trace
#print axioms OnBytes.FrontRoad.sessionStops_of_plain
#print axioms OnBytes.FrontRoad.sessionStops_of_hinge
#print axioms OnBytes.FrontRoad.sessionStops_of_tiedOwn
#print axioms OnBytes.FrontRoad.sessionStops_of_tied
#print axioms OnBytes.FrontRoad.sessionStops_of_yes
#print axioms OnBytes.FrontRoad.sessionStops_of_valid
#print axioms OnBytes.FrontRoad.sessionStops_of_tied_hinge
#print axioms OnBytes.FrontRoad.sessionStops_of_model
