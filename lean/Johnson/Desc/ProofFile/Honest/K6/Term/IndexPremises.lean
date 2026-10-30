-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/IndexPremises.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6
of the online proof): THE TWO PREMISES OF THE STRUCTURE K6HeadBelow's FILLING THAT READ THE INDEX,
BY NAME, WITH THE TYPE OF THE INDEX A LETTER. Two definitions and two short theorems.

WHAT IT IS NOT. No premise is paid here. The two definitions are forms of hypotheses: nothing is
claimed of them. The two theorems exchange them for plainer premises, which stay premises. Where no
input is valid (Vd false everywhere) all four hold for nothing. Closed facts that Lean's kernel
decided by evaluation lie beneath the second theorem's hypothesis h and the laws that it calls.
Nothing says that a verifier accepts a proof. Nothing on soundness or on what a proof hides.

WHAT IT IS. K6HeadBelow (Honest/K6/Law/ScriptBelowFree.lean) is the structure of twelve fields under
which, with the seat, this member delivers what it owes (the statement ExchangeS at border 341). The
honest prover's index is a matrix; the integer model's index has the type Cm.Idx. So here the type
W₀ of the prover's index and its reader, weights, are letters.

  IndexHeld             the field index of K6HeadBelow, to the letter: the cells that the Script
                        makes of the valid input hold an index of the integer model, and in the
                        output matrix's two bands of rows the reader of the committed digits reads
                        that index's entries
  TraceIsTheModels      the valid input's trace is the library's reader by labels at the integer
                        model's trace (theTrace), at an index and at a served instance that is read
                        off the input's own bytes; and the head's weights, read through weights, are
                        that index's output matrix. It is the premise of k6_guests_of_theTrace
                        (Honest/K6/Law/GuestsOfTheTrace.lean), to the letter, at the identity as the
                        reader of the trace's cells
  indexHeldAtAnIndexReader, traceIsTheModelsAtAnIndexReader
                        the two from: "at the valid input the reader of the committed digits is the
                        library's reader entryOf of an index i", with "the Script's cells hold i"
                        for the one and "the input's trace is the library's trace at i" for the
                        other

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's flat list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.

THE NAMES' HOME. The file works inside the namespace of the head's laws, so that the premises read
there to the letter as in the laws that take them; the new names are laid in ProofFile.Honest.K6.Term.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.GuestsAtFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model (ppref Instance)
open Inst.Model.Head (oH)
open Inst.Model.Layout (kRef hRef)
open OnBytes.HonestTrace (theTrace cellOf ServesAt entryOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Local fullIn fullIn_trace_some)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K6 (headTensorOf headTensor_entryOf_in_scope valMinAbs_entryOf)

/-- **The Script's cells hold an index, which the reader of the committed digits reads.** The field
index of K6HeadBelow, to the letter. A definition: the form of a hypothesis. -/
def _root_.ProofFile.Honest.K6.Term.IndexHeld {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (weights : W₀ → ProofFile.Honest.Weights) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) : Prop :=
  ∀ v, (v = w ∧ Vd v) → ∃ i : Cm.Idx, Holds (Q.cells v) i ∧
    ∀ row col, oH ≤ row → row < oH + 2 * 5120 → col < 202048 →
      (ZMod.valMinAbs ((weights v.w₀).entry row col) : Int) = i.mat row col

/-- **The valid input's trace is the integer model's.** The premise of k6_guests_of_theTrace, to the
letter, at the identity as the reader of the trace's cells. A definition: the form of a hypothesis.
The index i is bound here on its own: nothing in this text says that it is the index of
IndexHeld. -/
def _root_.ProofFile.Honest.K6.Term.TraceIsTheModels {W₀ Rc : Type} (Zp : ProofFile.Pub) (G : ProofFile.Ground)
    (weights : W₀ → ProofFile.Honest.Weights)
    (Vd : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
    (w : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) : Prop :=
  Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ProofFile.instOf w.x = some xI ∧
    ServesAt (At.X Zp) i xI ∧ id w.trace = ⟨cellOf (At.X Zp) (theTrace (At.X Zp) i xI)⟩ ∧
    (letI := sizesOf (At.X Zp).hS
     ∀ k v, k < Norm.d → v < V → headTensorOf G.W.layers.wsLay (weights w.w₀) k v =
       (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v)

/-- CONDITIONAL on readsAnIndex, which stays a premise. **IndexHeld where the reader of the
committed digits is the library's reader of an index that the Script's cells hold.** -/
theorem _root_.ProofFile.Honest.K6.Term.indexHeldAtAnIndexReader {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {weights : W₀ → ProofFile.Honest.Weights} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {w : Local W₀ Rc ProofFile.Inst Tr}
    (readsAnIndex : Vd w → ∃ i : Cm.Idx, Holds (Q.cells w) i ∧
      weights w.w₀ = (⟨entryOf i⟩ : ProofFile.Honest.Weights)) :
    ProofFile.Honest.K6.Term.IndexHeld Q weights Vd w := by
  unfold ProofFile.Honest.K6.Term.IndexHeld
  rintro v ⟨rfl, valid⟩
  obtain ⟨i, holds, reader⟩ := readsAnIndex valid
  refine ⟨i, holds, ?_⟩
  rw [reader]
  intro row col rowAbove rowBelow colBelow
  clear rowAbove
  have rowInside : row < hRef := by
    have e1 : oH = 3065840 := rfl
    have e2 : hRef = 3076096 := rfl
    rw [e1] at rowBelow
    rw [e2]
    clear e1 e2
    omega
  have colInside : col < 2 ^ kRef := by
    have e3 : (2 : Nat) ^ kRef = 262144 := by decide
    rw [e3]
    clear e3
    omega
  exact valMinAbs_entryOf i rowInside colInside

/-- CONDITIONAL on the library's hypothesis h on the public files, on "G is the blank ground of the
public part" and on readsAnIndex, which stays a premise. **TraceIsTheModels where the reader of the
committed digits is the library's reader of an index, and the input's trace is the library's trace
at that index** (fullIn.trace, Honest/AtPureFullIn.lean: by its definition the integer model's trace
at a served instance that is read off the request's bytes, and none elsewhere; no program runs
it). -/
theorem _root_.ProofFile.Honest.K6.Term.traceIsTheModelsAtAnIndexReader {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc : Type}
    {G : ProofFile.Ground} (groundIsBlank : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {weights : W₀ → ProofFile.Honest.Weights} {Vd : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Prop}
    {w : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells}
    (readsAnIndex : Vd w → ∃ i : Cm.Idx, weights w.w₀ = (⟨entryOf i⟩ : ProofFile.Honest.Weights) ∧
      fullIn.trace Zp i w.x = some w.trace) :
    ProofFile.Honest.K6.Term.TraceIsTheModels Zp G weights Vd w := by
  unfold ProofFile.Honest.K6.Term.TraceIsTheModels
  intro valid
  obtain ⟨i, reader, traced⟩ := readsAnIndex valid
  obtain ⟨xI, hx, Sv, hC⟩ := fullIn_trace_some traced
  refine ⟨i, xI, hx, Sv, hC, ?_⟩
  intro k v hk hv
  have B := OnBytes.Road.Hd.public_of_core h.pubOne
    (OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne)
  have hk' : k < (At.X Zp).hS.d := hk
  have hv' : v < (At.X Zp).hS.V := hv
  rw [B.full.d] at hk'
  rw [B.full.V] at hv'
  rw [reader, ground_of_blank groundIsBlank]
  exact headTensor_entryOf_in_scope h.scope h.reads h.pubOne i k v hk' hv'

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms ProofFile.Honest.K6.Term.indexHeldAtAnIndexReader
#print axioms ProofFile.Honest.K6.Term.traceIsTheModelsAtAnIndexReader
