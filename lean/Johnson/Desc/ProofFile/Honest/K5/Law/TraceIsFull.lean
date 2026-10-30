-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TraceIsFull.lean: PAID BY NOBODY: ONE NAMED PREMISE ON THE
TRACE IN THE STEAD OF THREE: UPHILL: A WEAKER LAW UNDER A STRONGER PREMISE. `TraceIsFull` gives two
premises of attention's joined law on K5's member at a Script laid from lots
(`k5_owes_all_joined_typed_book`, LotsJoinedBook.lean in this folder): hqa and hSm; a third, hrd, is
met by a choice of the reader; nothing goes back. IT PAYS NOTHING: AN EXCHANGE. WHAT IS WON IS A
NAME THAT A PAYER CAN AIM AT: one sentence on the trace in the library's own terms. IT MAY HOLD
EMPTILY. CONDITIONAL: under the hypothesis h, the library's head on the public input (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). One theorem. The form `TraceIsFull` and the seven other theorems that are
named below are declared in TraceFull.lean in this folder: what is said of them here holds of them
there.

Main names:
  `TraceIsFull X Vd cells`: THE FORM: at each input v that meets Vd there are pl, an index i and a
    request x that is served (`ServesAt`, Johnson/HonestTrace/Full.lean) such that the trace's
    reader has, at each segment of a proof with 12 groups and each matrix's label OFF THE PLANES,
    the image in the field of the entry of the library's own full-size trace `trFull X pl i x`.
  `k5_owes_all_joined_typed_trace`: THE LAW: the statement of `k5_owes_all_joined_typed_book` with
    hrd, hqa, hSm gone for hT, at the reader fun v => ⟨v.trace, wt v.w₀, v.rc⟩. LEFT, thirteen. hT,
    on the trace: PAID BY NOBODY. HM, F0, F1, hH, on the Script and its lots: unpaid. hA, hBook,
    hoff, hRdM, on what `onlineProverFromPublicFiles` returns, the book, the lots of trees and the thread's letter:
    unpaid here. hSz: met at `Sz.ref`, and at `Sz.ofPublic X` in the goals' scope
    (`planesAtRef_ref`; `planesAtRef_ofPublic`, which is conditional; SizesOffPlanes.lean in this
    folder). hg: a number below 12. hO, hf: met by a choice of a letter; the same O stands in hA's
    filling.
  `hqa_of_traceIsFull`, `hSm_of_traceIsFull`: the two premises from the form.
  `traceIsFull_of_hinge`: THE FORM FOLLOWS FROM `TraceHinge` (Johnson/HonestTrace/TraceHinge.lean)
    AND hV. HOW THE TWO PART: `TraceHinge` is on an integer trace as a function of an index and an
    input; it reads the request off the input; the index is the function's own first argument, which
    nothing ties to the input; it has the planes; it goes one way: where the trace is there.
    `TraceIsFull` is on a valid input's reader of cells; untied; off the planes. BETWEEN THEM STANDS
    hV: at a valid input the function answers at the input's own instance, and the input's reader is
    `cellOf` of what it answers.
  `traceIsFull_of_cellOf`: a reader that is the library's reader by labels (`cellOf`) of such a
    trace meets the form.
  `noAt_ff_bNo_iff`, `noAt_att_bNo_iff`, `noAt_head_bNo_iff`: THE FENCE a ≠ bNo X (σ.no 12) SHUTS
    OUT JUST THE PLANES' NAME (b, bA, bH), at every X.

How. Sealed, in Johnson/Goal/HonestTrace/FullInScope.lean: `cellOf_label_in_scope`;
`borrowed_in_scope`: an attention sub-proof's qa is its group's, served or not;
`small_off_planes_in_scope`: at a served request every entry off the planes' number is below 129 in
absolute value. The fence: `bNo_even`, `bNo_odd`, `bNo_head` (Full.lean) and `MatName.no?_inj`
(Johnson/HonestTrace/Names.lean). `hSm_of_traceIsFull` has the steps of `cellsSmallQ_of_int`
(CellsSmallOfInt.lean in this folder), unfolded, with `labelOf_label` (PackedAtSeg.lean) and
`val_eOfF` (PackedVals.lean).

Limits. pl, i and x stand under "there is", behind "for all v": NOTHING TIES i TO THE INPUT's INDEX
OR x TO ITS REQUEST: the form is no word on the committed weights. It speaks of all 25 segments'
matrices off the planes, where K5 at group g spends two segments'. NOTHING AT A PLANE's NUMBER.
`hqa_of_traceIsFull` does not spend the serving. wt is a letter that no premise ties: the lots at
two wt answer alike and are two terms. At a Vd that holds of no input the form asks nothing; nothing
proves that any input's trace is such a trace: in the frame's filling the trace is a letter
(`WiderIn.trace`, Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean). In `traceIsFull_of_hinge` trace
and instOf are letters that nothing ties to the filling of hA; the function that never answers meets
the hinge, and then hV fails at every valid input. The docstring of `TraceHinge` names a function
that meets it (fullTrace, in two files of the frame's folder): these two files are not imported, and
were not at hand. TraceHinge.lean lies in a later seal than the one over which this file was tried:
it is carried. All is at the library's full size: 12 groups, and the numbers of parts of
`parts_in_scope`. All limits of LotsJoinedBook.lean hold here. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsJoinedBook
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.HonestTrace.TraceHinge
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

section
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree)
open ProofFile.Honest.K1 (cellsVals)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- hT IS PAID BY NOBODY. **THE JOINED LAW AT THE LAYING, AT THE TYPED SEATS AND THE BOOK's TEST,
WITH ONE PREMISE ON THE TRACE.** A COROLLARY: A WEAKER LAW UNDER A STRONGER PREMISE. CONDITIONAL:
every premise stands, by name, in the file's head. -/
theorem k5_owes_all_joined_typed_trace
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))) (hSz : planesAtRef S = Sz.ref)
    {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hoff : ∀ b blk, cF.blocksInOrder[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (tl b).off j ≤ blk.rounds.length)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true)
    (wt : W₀ → Weights) (hT : TraceIsFull (P5J.At.X Zp) Vd (id : Cells → Cells))
    (HM : ∀ (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
      (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      maskMsg h.𝔇.sent x₁.link = some kM →
      maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a) (OnBytes.Model.Forest.elems a.fs) ∈ ml ∧
      LotsAgree ml (maskLot h x₁ kM hk (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs)))
    (F0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) →
      fillLot h S (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g)) (fun _ => 0) Ad
        (2 * g) m ∈ ml ∧
      LotsAgree ml (fillLot h S (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g))
        (fun _ => 0) Ad (2 * g) m))
    (F1 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g + 1) Ad = some (2 * g + 1, m) →
      fillLot h S (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g + 1))
        (fun _ => 0) Ad (2 * g + 1) m ∈ ml ∧
      LotsAgree ml (fillLot h S (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (typedSeat h A.G (2 * g + 1))
        (fun _ => 0) Ad (2 * g + 1) m))
    (hH : Vd w → ∃ i,
      VerifiableInference.OnPublicFiles.Flat.Holds
        ((Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml).cells w) i) :
    (Plays (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
          test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_typed_book h test carryX item n₁ n₂ Vd RdL f w cq tok pl tl ml hSz hg hA hO
    hoff hf hRdM hBook (rd := fun v => ⟨v.trace, wt v.w₀, v.rc⟩) (fun _ => rfl)
    (hqa_of_traceIsFull h hT hg) (fun _ ha => hSm_of_traceIsFull h hT hg ha rfl rfl) HM F0 F1 hH

end

end ProofFile.Honest.K5
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_typed_trace
