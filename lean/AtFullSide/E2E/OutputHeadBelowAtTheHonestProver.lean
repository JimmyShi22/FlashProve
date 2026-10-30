-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadBelowAtTheHonestProver.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): THE TWELVE FIELDS OF K6HeadBelow AT THE HONEST PROVER's INDEX, A MATRIX, AND AT
ITS READER AND TRACE (matrixInput, E2E/TheHonestProver.lean), UNDER THIRTEEN NAMED PREMISES.

WHAT IT IS NOT. Every theorem here is conditional. Thirteen premises stay beside the library's
hypothesis h (with the seat, fourteen), and that they can be met together with a valid input is not
shown here (at the base prover, of valid inputs, eleven are had under three premises:
AtFullSide/E2E/OutputHeadDebtsAtTheFirstScript.lean), and with a thread that stands by nobody: so
nothing here says that the member delivers what it owes at any run, or that the verifier accepts.
Where no input is valid, five of the twelve fields hold for nothing, and so does the statement on
what is delivered; at a valid input the same holds of four fields, of streamSymbolsAreThePacking and
of that statement wherever the thread's invariant holds at no state in front of the member. OF THE
HONEST PROVER THESE THEOREMS HAVE the index's type, its reader, the definition of its trace, the
data of the sender's main rows and the layout, and (in the last one) the book and the ground of its
maker's return; THE PROVER, THE SCRIPT, Vd, Said AND readers ARE LETTERS. Closed facts that Lean's
kernel decided by evaluation at written values lie beneath (the head of
AtFullSide/K6/BelowAtAnyIndex.lean names them). The trace of matrixInput is a definition by choice
at the full size, which no program runs: "the input's trace is the integer model's" follows here
from that definition, not from a run. Nothing on soundness or on what a proof hides.

WHAT IT IS. headBelowUnderNamed (AtFullSide/K6/BelowAtAnyIndex.lean) has two premises that read the
index, IndexHeld and TraceIsTheModels, and one on the code switch's public test. Here the sender's
text is taken at the honest filling's own letters: the data of the main rows are K2.withSwitchData
Sz.ref (K1.lotData Sz.ref), which is the filling's widerRows Sz.ref by definition, and the layout is
the ground's. There the three follow from three plainer ones:

  startTestAccepts               the description's own test on the instance accepts the input's
                                 instance; the description's decision asks that test too, behind
                                 its tests on the plan (runCore, Johnson/Desc/Block.lean). By
                                 switchTestAccepts (Honest/K6/Term/SwitchTestAccepts.lean)
  validInputCarriesTheTrace      the valid input's trace is what matrixInput.trace returns at the
                                 input's matrix and instance: a premise on the thread's letter Vd
  scriptCellsHoldTheInputsIndex  the cells that the Script makes of the valid input hold whatever
                                 index the input's matrix holds: a premise on the Script; it is met
                                 where these cells are the input's matrix

The last two: E2E/OutputHeadIndexAtTheHonestProver.lean.

  headBelowAtTheMatrices            the twelve fields at every filling over the matrices: the type
                                    of the stored tables' randomness, the filling and the prover are
                                    letters. So it serves at the filling onlineProverPartsInUse
                                    matrixInput … itself and at that filling read through readers
  deliversAtTheMatrices             so, under the seat, what the member owes is delivered
                                    (ExchangeS)
  headBelowAtTheOnlineMakersReturn  the twelve fields at a return of the honest prover's own maker
                                    (onlineMaker)

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's blocksInOrder list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.
-/
import E2E.OutputHeadIndexAtTheHonestProver
import AtFullSide.K6.BelowAtAnyIndex
import Johnson.Desc.ProofFile.Honest.K6.Term.SwitchTestAccepts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds indexOf matrixOf)
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput)
open ProofFile.Honest.K6.Term
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K2 (SwitchPlace)
open P5J (AtMgA CellsM TS)

section AtTheMatrices
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Rc Ky X₀ X₀' X : Type}
  {P : ProofFile.Honest.OnlineProverParts FullSizeMatrix Rc ProofFile.Honest.Cells X₀ X}
  {A : ProofFile.Honest.OnlineProverWithDescription FullSizeMatrix Rc ProofFile.Honest.Cells X₀ X}
  {H : ProofFile.Honest.Prover FullSizeMatrix Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀' X}
  {Q : Script A.B (ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells)
    (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {item n₁ n₂ b₀ : Nat} {Vd : ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells → Prop}
  {Rd : Nat → ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop}
  {Kp : Place → TS → TS → Prop} {w : ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells}
  {Said : Nat → ProofFile.Honest.Coins A.B →
    ProofFile.Honest.Mid (ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop}
  {readers : ProofFile.Honest.Local FullSizeMatrix Rc ProofFile.Inst ProofFile.Honest.Cells → ProofFile.Honest.Readers}
  {p : SwitchPlace} {N fx free : Nat}

/-- CONDITIONAL on the library's hypothesis h and on thirteen named premises, none of which is paid
here; it may hold for nothing (the head says where). **ALL TWELVE FIELDS OF K6HeadBelow AT THE
HONEST PROVER's INDEX, READER AND TRACE, at the book and the ground of a return of the maker at any
filling over the matrices.** -/
theorem headBelowAtTheMatrices (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : ProofFile.Honest.onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (debts : HeadBelowDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said A.G
      (ProofFile.Honest.K1.lotData OnBytes.HonestTrace.Sz.ref) readers A.G.first.layout p N fx free)
    (startTestAccepts : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (validInputCarriesTheTrace : Vd w → matrixInput.trace Zp w.w₀ w.x = some w.trace)
    (scriptCellsHoldTheInputsIndex : Vd w → ∀ i : Cm.Idx, Holds w.w₀ i → Holds (Q.cells w) i) :
    HeadBelowAtTheSwitch h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said (matrixInput.weights Zp)
      A.G p free (bookLendsTheSwitch h makerReturns debts.placeIsWritten) :=
  headBelowUnderNamed h makerReturns debts
    (switchTestAccepts h (groundOfAReturnIsBlank h makerReturns) debts.placeIsWritten
      startTestAccepts)
    (indexHeldAtTheMatrices validInputCarriesTheTrace scriptCellsHoldTheInputsIndex)
    (traceIsTheModelsAtTheMatrices h (groundOfAReturnIsBlank h makerReturns)
      validInputCarriesTheTrace)

/-- CONDITIONAL as headBelowAtTheMatrices, and on the seat: the prover's first side at the member's
place is the head's row at the honest prover's reader. None of these is paid here; where the
thread's invariant holds nowhere in front of the member it holds for nothing. **BEHIND THE MEMBER's
ACCEPTING STEP WHAT THE MEMBER OWES IS DELIVERED** (the statement ExchangeS at border 341), at the
honest prover's index, reader and trace. One call: k6_exchangeS_of_below
(Honest/K6/Law/ScriptBelowFree.lean). -/
theorem deliversAtTheMatrices (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : ProofFile.Honest.onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (seat : ProofFile.Honest.K6.K6HalfAt Zp H
      (ProofFile.Honest.K6.headWit' id (matrixInput.weights Zp) Zp A.G))
    (debts : HeadBelowDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said A.G
      (ProofFile.Honest.K1.lotData OnBytes.HonestTrace.Sz.ref) readers A.G.first.layout p N fx free)
    (startTestAccepts : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (validInputCarriesTheTrace : Vd w → matrixInput.trace Zp w.w₀ w.x = some w.trace)
    (scriptCellsHoldTheInputsIndex : Vd w → ∀ i : Cm.Idx, Holds w.w₀ i → Holds (Q.cells w) i) :
    ProofFile.Honest.ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 :=
  VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_of_below
    (headBelowAtTheMatrices h makerReturns debts startTestAccepts validInputCarriesTheTrace
      scriptCellsHoldTheInputsIndex) seat

end AtTheMatrices

/-- CONDITIONAL as headBelowAtTheMatrices. **THE SAME AT A RETURN OF THE HONEST PROVER's OWN
MAKER**, at every prover over the matrices and the object's randomness: the caller sets the prover.
NO SCRIPT OF THIS TYPE IS LAID (the first chain's Script is typed at the base filling's randomness),
so that its premises can be met is shown by nobody; it is called by nothing. -/
theorem headBelowAtTheOnlineMakersReturn {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files}
    {D : WholeD} {r : LPFD.Full.RunPF} {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {Ky X₀ : Type}
    {prover : ProofFile.Honest.Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Ky ProofFile.Honest.Cells X₀ Unit}
    {Q : Script returned.B (ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells)
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
    {item n₁ n₂ b₀ : Nat}
    {Vd : ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells → Prop}
    {Rd : Nat → ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells → TS → Prop}
    {Kp : Place → TS → TS → Prop}
    {w : ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells}
    {Said : Nat → ProofFile.Honest.Coins returned.B →
      ProofFile.Honest.Mid (ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop}
    {readers : ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst ProofFile.Honest.Cells → ProofFile.Honest.Readers}
    {p : SwitchPlace} {N fx free : Nat}
    (h : AtMgA OnBytes.secondHashFunction files D r returned.Z places firstChain x)
    (makerReturns : onlineMaker files = .ok returned)
    (debts : HeadBelowDebts h prover Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said returned.G
      (ProofFile.Honest.K1.lotData OnBytes.HonestTrace.Sz.ref) readers returned.G.first.layout p N fx
      free)
    (startTestAccepts :
      (P5J.F0T OnBytes.secondHashFunction returned.Z places firstChain).okStart w.x = true)
    (validInputCarriesTheTrace : Vd w → matrixInput.trace returned.Z w.w₀ w.x = some w.trace)
    (scriptCellsHoldTheInputsIndex : Vd w → ∀ i : Cm.Idx, Holds w.w₀ i → Holds (Q.cells w) i) :
    HeadBelowAtTheSwitch h prover Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      (matrixInput.weights returned.Z) returned.G p free
      (bookLendsTheSwitch h makerReturns debts.placeIsWritten) :=
  headBelowAtTheMatrices h makerReturns debts startTestAccepts validInputCarriesTheTrace
    scriptCellsHoldTheInputsIndex

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.headBelowAtTheMatrices
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.deliversAtTheMatrices
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.headBelowAtTheOnlineMakersReturn
