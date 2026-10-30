-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureFullIn.lean: the full-size trace and the index's own matrix of
digits, in the form in which `widerFillAt` (Honest/AtPureWiderAt.lean) takes them. One definition,
`fullIn`, and six lemmas that hold by unfolding.

Read this first. `fullIn` is noncomputable: no program can run a choice of fields that is made
from it. It is at the full size alone. The test programs run `widerFillAt` and its relatives at
another value of `WiderIn`, over a runnable trace at a small example; nothing here compares the two.

What it is for. The lemmas on the full-size trace are about `theTrace X i x` under `ServesAt X i x`
(Johnson/HonestTrace/FullPlanes.lean, Johnson/HonestTrace/Full.lean). The lemmas on the prover's
sides are about the choice of fields `widerFillAt I o S O`, whose trace is the field `I.trace` and
has the type `Cells`: a reader of cells. `fullFill` (Honest/AtPureFull.lean) has the full-size trace
too, but at another type of trace, so it is no value of `widerFillAt`. `fullIn` is a value of
`WiderIn` at which a hypothesis "the trace is the full-size trace of this index and this instance,
read by `cellOf`" is a lemma.

  `fullIn`               the four fields of `WiderIn`, at the index `Cm.Idx`. Its field `dummy` is
                         `Policy.PosGuards.idx0` (Policy/Rel/PosGuards.lean: made-up weights at
                         which every token votes for token 0); the tests on the range alone read
                         it, and `inRange` is constant: which index stands there does not matter
  `fullIn_trace_some`    where its trace is there, it is `theTrace`, read by `cellOf`, at an
                         instance that the request's bytes are read as and that the index serves
  `fullIn_trace_served`  and it is there at every such instance; where it is not there, `ready`
                         (Honest/Frame.lean) refuses, aloud: "the request has no trace"
  `fullIn_weights`       its reader of the digits is `entryOf` at the index, at every public part
  `fullIn_fill_trace`    the trace of `widerFillAt fullIn o S O` is the field `fullIn.trace`
  `fullIn_readers`       at the cells of a trace T, the readers of `widerFillAt fullIn o S O` are
                         `fullReaders` at T
  `fullIn_range`         its named member is in range

Limits.
  * All limits of Honest/AtPureFull.lean hold here, but for the one on `Owners`, which speaks of
    `fullFill`. Among them: the trace chooses names by `Classical.choice`; whether an index serves
    a request is a proposition; the instance's type, the twelve groups and the 25 sub-proofs are
    those of the reference sizes; `inRange` is true at every index, because the range is in the
    type `Cm.Idx`. Neither that file nor this one compares the rows and columns of `entryOf` with
    those of docs/format/11-5-weights-in-the-table.md. Outside the matrix's shape `entryOf` is 0
    (`entryOf_out`, Johnson/HonestTrace/IndexReaders.lean): a silent default of the reader
    `fullIn.weights`. Likewise `cellOf` (Johnson/HonestTrace/Full.lean) is 0 at an unknown label,
    at a label of another sort of segment, at a part beyond the parts and from k = 25 on, and the
    trace that it reads is 0 outside the shapes (`trFull_out`, the same file): silent defaults of
    the reader of cells in `fullIn.trace`.
  * All limits of Honest/AtPureWiderAt.lean hold here (of the four open functions that
    Honest/AtPureWider.lean names, `cells` is not read by `widerFillAt`). Its limit "nothing
    compares `WiderIn.trace` with `WiderIn.weights`" is met here in this sense alone: both fields
    are computed from the same index `i`. That the trace is a correct forward pass at the integer
    digits `i.mat`, whose image in the field `entryOf i` is by definition, is what `ServesAt` and
    `theTrace` are about, and is not restated.
  * The argument `S` of `widerFillAt` (the model's sizes, for the data of the main rows) stays free.
    Nothing here says that a caller supplies the full size there.
  * No lemma of this file says that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns at
    `widerFillAt fullIn o S O` or at `widerFillAtC fullIn o S O` (Honest/AtPureWiderK10.lean). Of
    the second, under the library's head, that is a lemma of another file
    (`atPure_returns_widerC_fullIn`, Honest/K5/Law/ReturnsAtWiderCFullIn.lean, not imported here).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureFullLaw
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Inst.Model (Instance ppref)
open OnBytes.HonestTrace (Tr theTrace ServesAt cellOf entryOf)

/-- **The full-size trace and the index's matrix of digits, as a value of `WiderIn`.** The reader
of an instance is `ProofFile.instOf`, as in `fullFill`. -/
noncomputable def fullIn : WiderIn Cm.Idx :=
  { weights := fun _ i => ⟨entryOf i⟩
    trace := fun Z i ξ => (fullTrace ProofFile.instOf Z i ξ).map fun T => ⟨cellOf Z.p.X T⟩
    inRange := fun _ => true
    dummy := Policy.PosGuards.idx0 }

/-- Where the trace is there, it is the full-size trace, read by `cellOf`, at an instance that the
request's bytes are read as and that the index serves. -/
theorem fullIn_trace_some {Z : Pub} {i : Cm.Idx} {ξ : Inst} {C : Cells}
    (h : fullIn.trace Z i ξ = some C) :
    ∃ x, ProofFile.instOf ξ = some x ∧ ServesAt Z.p.X i x ∧
      C = ⟨cellOf Z.p.X (theTrace Z.p.X i x)⟩ := by
  have h' : (fullTrace ProofFile.instOf Z i ξ).map (fun T => (⟨cellOf Z.p.X T⟩ : Cells)) = some C := h
  cases hT : fullTrace ProofFile.instOf Z i ξ with
  | none =>
    rw [hT] at h'
    have h'' : (none : Option Cells) = some C := h'
    cases h''
  | some T =>
    rw [hT] at h'
    have e : (⟨cellOf Z.p.X T⟩ : Cells) = C := Option.some.inj h'
    obtain ⟨x, hx, hs, eT⟩ := fullTrace_some hT
    exact ⟨x, hx, hs, by rw [← e, eT]⟩

/-- And it is there at every such instance. -/
theorem fullIn_trace_served {Z : Pub} {i : Cm.Idx} {ξ : Inst} {x : Instance ppref}
    (hx : ProofFile.instOf ξ = some x) (hs : ServesAt Z.p.X i x) :
    fullIn.trace Z i ξ = some ⟨cellOf Z.p.X (theTrace Z.p.X i x)⟩ := by
  show (fullTrace ProofFile.instOf Z i ξ).map (fun T => (⟨cellOf Z.p.X T⟩ : Cells)) = _
  rw [fullTrace_served hx hs]
  rfl

/-- The reader of the digits is the index's own matrix, at every public part. -/
theorem fullIn_weights (Z : Pub) (i : Cm.Idx) : fullIn.weights Z i = ⟨entryOf i⟩ := rfl

/-- The trace of the choice of fields is the field `fullIn.trace`. -/
theorem fullIn_fill_trace (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillAt fullIn o S O).trace = fullIn.trace := rfl

/-- At the cells of a trace the readers of the choice of fields are `fullReaders` at that trace. -/
theorem fullIn_readers (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub)
    (i : Cm.Idx) (rc : IndexCommitterCoins) (T : Tr) :
    (widerFillAt fullIn o S O).readers Z i rc ⟨cellOf Z.p.X T⟩ = fullReaders Z i rc T := rfl

/-- The named member is in range. -/
theorem fullIn_range : fullIn.inRange fullIn.dummy = true := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.fullIn_trace_some
#print axioms ProofFile.Honest.fullIn_trace_served
#print axioms ProofFile.Honest.fullIn_weights
#print axioms ProofFile.Honest.fullIn_fill_trace
#print axioms ProofFile.Honest.fullIn_readers
#print axioms ProofFile.Honest.fullIn_range
