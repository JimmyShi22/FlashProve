-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadDebtsAtTheFirstScript.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of
the online proof): CONDITIONAL: THE NINE PREMISES OF HeadBelowDebts, AND THE TWO THAT READ THE
INDEX, AT THE FIRST CHAIN's SCRIPT AS A VALUE (firstScriptAt, AtFullSide/K1/FirstScript.lean), AT
THE PROVER THAT THE MAKER RETURNS AT THE BASE FILLING OVER THE MATRICES, AND AT "AN INPUT THAT ready
COULD PREPARE" (ReadyInput) AS THE VALID INPUTS. No premise on the Script is left.

WHAT IT IS NOT. It does not say that the member delivers what it owes, and not that the verifier
accepts. Three premises stay: the library's hypothesis h at the return's public part; "the maker
returns at the base filling"; and closingsReturn, the code switch's public test closingOk at each of
its places. Where no input is ready, most of it holds for nothing. The trace of matrixInput is a
definition by choice at the full size, which no program runs. That the prover's sides of the code
switch play the Script's texts is not said here. The base filling alone, not that filling read
through readers. The full size and the format's second hash function alone. It stands at a filling that its
reviewer has cleared as the base for the proofs; two named debts stand before anything at it counts:
that W's rows are ready where their sender plays (number 356), and that the lent words of the
message o_sp are tied at the tests U and O (numbers 9 and 10 of the shared chain). Closed facts that
Lean's kernel decided by evaluation at written values lie beneath. Nothing on soundness or on what a
proof hides.

WHAT IT IS. Each premise, with what pays it.
  the Script's message at the sender's number is the sender's own text
        ownMsgs_switch_first (AtFullSide/K1/FirstScript.lean), at message 2 of the switch into link
        24; that the switch is that message's first sender: placesOkW (AtFullSide/K1/LaysAtSwitches)
  at the borrowed stream's seats the witness holds the packing of the input's cells
        streamSymbolsArePackedWhereTheScriptLaysTheLastGroup (Honest/K6/Term/Stream.lean), from
        laysFilling_switches (AtFullSide/K1/LaysAtSwitches.lean) at segment 22. Its three premises:
        the switch's part is handed its coins (switchIsHandedItsCoins, here, from
        bookLendsTheSwitch); closingsReturn; the code switch's public test on the instance
        (switchTestAccepts, from the first clause of ReadyInput)
  the valid input's trace is what matrixInput.trace returns
        the third clause of ReadyInput, and atPure_ok: the returned prover's trace is the filling's
  the Script's cells hold the index that the input's matrix holds
        the Script's cells are the matrix of cells of the index's reader, by its definition;
        matrixReaderAtAHeldIndex; holds_cellsOfF (Honest/K13/CellsAreIndex.lean)
  the letters: the place by link24W_one; N := 0; free := 2168; the reply's border 339; fx := the
  rounds in front of the place's member; readers := readersB matrixInput A.Z; the data of the main
  rows := lotData Sz.ref; the layout := the ground's.

  aWrittenSwitchLeadsIntoLink24, switchIsHandedItsCoins   two short lemmas
  readyInputCarriesTheTrace, firstScriptsCellsHoldTheIndex   the two that read the index
  debtsAtTheFirstScript                                   the nine
  deliversWhereItDeliversAtAValidInput                    general: ExchangeS at border 341 follows
                                                          from "the input is valid → ExchangeS"
WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's flat list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.
-/
import E2E.OutputHeadIndexAtTheHonestProver
import AtFullSide.K6.BookLendsTheSwitch
import AtFullSide.K1.LaysAtSwitches
import Johnson.Desc.ProofFile.Honest.K6.Term.BelowPremises
import Johnson.Desc.ProofFile.Honest.K6.Term.SwitchTestAccepts
import Johnson.Desc.ProofFile.Honest.K6.Term.Stream
import Johnson.Desc.ProofFile.Honest.K6.Cells.Link24Main
import Johnson.Desc.ProofFile.Honest.K13.CellsAreIndex
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover OnlineProverWithDescription onlineProverFromPublicFiles atPure_ok atPure_at_laid_ground IndexCommitterCoins
  OnlineProverArguments ReadyInput ExchangeS onlineProverPartsInUse lendsPart lookDue look_dueIs lendPart_ok_iff
  roundsTo borderNo)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K6.Term
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head pseatsAll_at_head atLink24W
  atLink24_gives link24W_one)
open P5J (AtMgA CellsM TS F0T)
open P5T (seatsAllFull)

/-! ## 1 Two short lemmas -/

/-- A written place of a code switch has link 24. -/
theorem aWrittenSwitchLeadsIntoLink24 : ∃ p ∈ placesW, p.link = 24 := by
  cases found : placesW.filter fun p => p.link == 24 with
  | nil =>
    have one := link24W_one
    rw [found] at one
    exact absurd one (by decide)
  | cons p rest =>
    have isIn : p ∈ placesW.filter fun p => p.link == 24 := by
      rw [found]
      exact List.mem_cons_self
    exact ⟨p, (List.mem_filter.1 isIn).1, beq_iff_eq.1 (List.mem_filter.1 isIn).2⟩

/-- CONDITIONAL on h, on "the maker returns" and on "p is a written place of a code switch". **At
every run's coins the frame hands the switch's first part something.** That it is the part's own
coins, once, is not said: the test beneath asks name, count and that the owners' cuts fit. -/
theorem switchIsHandedItsCoins {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    {W₀ Rc Tr X₀ X : Type} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {p : SwitchPlace}
    (placeIsWritten : p ∈ placesW) (k : Coins A.B) :
    (ProofFile.Honest.K2.handed 0 p k).isSome = true := by
  have sameCounts : (fun a => (k.look 0 a).1) = lookDue A.B 0 := funext fun a => look_dueIs k 0 a
  obtain ⟨y, lent⟩ := (lendPart_ok_iff A.B (A.B.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
    (ProofFile.Honest.K2.switchPart (ProofFile.Honest.K2.coreSender ProofFile.Honest.K2.freshTable) p.sizes p.others
      p.foldVars p.carries)).2
    (by rw [sameCounts]; exact bookLendsTheSwitch h makerReturns placeIsWritten)
  unfold ProofFile.Honest.K2.handed
  rw [lent]
  rfl

/-- GENERAL. **What the member owes is delivered, if it is delivered wherever the thread's input is
valid**: the thread's invariant holds "the input is the thread's and is valid". -/
theorem deliversWhereItDeliversAtAValidInput {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
    {item n₁ n₂ b₀ : Nat} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop} {Kp : Place → TS → TS → Prop}
    {w : Local W₀ Rc ProofFile.Inst Tr} {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (atAValidInput : Vd w →
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 :=
  fun blk there k s m E ds y cols s' stands =>
    have valid : m.st.input = w ∧ Vd m.st.input := stands.1.2.2.2.2.2.2
    atAValidInput (valid.1 ▸ valid.2) blk there k s m E ds y cols s' stands

/-! ## 2 At the base filling over the matrices -/

section AtTheBase
variable {files : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}

/-- CONDITIONAL on "the maker returns at the base filling". **An input that ready could prepare
carries the trace that matrixInput.trace returns at its matrix and instance.** -/
theorem readyInputCarriesTheTrace
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells}
    (ready : ReadyInput F A.H w) : matrixInput.trace A.Z w.w₀ w.x = some w.trace := by
  have sameTrace : A.H.trace = matrixInput.trace A.Z := (atPure_ok makerReturns).2.2.2.1
  rw [← sameTrace]
  exact ready.2.2

/-- No premise: A, Op and cF are tied to nothing here: it is a fact on the Script's definition of
its cells. **The cells that the first chain's Script makes of an input hold whatever index the
input's matrix holds.** -/
theorem firstScriptsCellsHoldTheIndex (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) (i : Cm.Idx)
    (holds : Holds w.w₀ i) :
    Holds ((ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A cF).cells w) i := by
  show Holds (Bind.ForProver.cellsOfF OnBytes.Slice.frS OnBytes.Slice.frZ 402653181
    VerifiableInference.OnPublicFiles.numsRef (matrixInput.weights A.Z w.w₀).entry) i
  rw [matrixReaderAtAHeldIndex holds A.Z]
  exact ProofFile.Honest.K13.holds_cellsOfF _
    fun y c => map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) (i.mat y.val c.val)

/-- CONDITIONAL on the library's hypothesis h at the return's public part, on "the maker returns at
the base filling" and on closingsReturn, which stays a premise. **THE NINE PREMISES OF
HeadBelowDebts AT THE FIRST CHAIN's SCRIPT, the returned prover and ReadyInput**, at a written place
of the code switch into link 24, at the honest filling's data of the main rows, readers and layout;
the thread's other letters are free. -/
theorem debtsAtTheFirstScript (h : AtMgA OnBytes.secondHashFunction files D r A.Z Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (closingsReturn : ∀ p ∈ ProofFile.Honest.K2.switchPlaces A.Z A.G,
      ProofFile.Honest.K2.closingOk ProofFile.Honest.K2.freshTable
        ((ProofFile.Honest.K2.segmentsOf A.Z A.G).take p.link) p = true)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Rd : Nat → Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst ProofFile.Honest.Cells) Unit → Prop) :
    ∃ p, HeadBelowDebts h A.H (ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A cF) test carryX
      item n₁ n₂ 339 (ReadyInput (F0T OnBytes.secondHashFunction A.Z Np cF) A.H) Rd Kp w Said A.G
      (ProofFile.Honest.K1.lotData Sz.ref) (ProofFile.Honest.K1.readersB matrixInput A.Z) A.G.first.layout p 0
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place)) 2168 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, sameGround, -⟩ := atPure_at_laid_ground h.laid O.blank makerReturns
  have groundIsBlank := groundOfAReturnIsBlank h makerReturns
  have placesAre : ProofFile.Honest.K2.switchPlaces A.Z A.G = placesW := by
    rw [sameGround]
    exact places_at_head h.toAtMg O
  have segmentsAre : ProofFile.Honest.K2.segmentsOf A.Z A.G = segsW := by
    rw [sameGround]
    exact segments_at_head h.toAtMg O
  obtain ⟨p, placeIsWritten, placeIsLink24⟩ := aWrittenSwitchLeadsIntoLink24
  have four := (atLink24_gives (List.all_eq_true.1 atLink24W p placeIsWritten) placeIsLink24).2.1
  have keptOne := (ProofFile.Honest.K6.atLink24Main_gives
    (List.all_eq_true.1 ProofFile.Honest.K6.atLink24MainW p placeIsWritten) placeIsLink24).1
  have firstSender : ProofFile.Honest.K2.firstSender p 2 = true := by
    have passes := List.all_eq_true.1 ProofFile.Honest.K1.placesOkW.1 p placeIsWritten
    unfold ProofFile.Honest.K1.placeOk at passes
    rw [Bool.and_eq_true] at passes
    have number : ProofFile.Honest.msgNo proofSizedFull.request p.link 0 0 = some 0 := by
      rw [placeIsLink24]
      exact ProofFile.Honest.K6.msgNo24W
    have own := (ProofFile.Honest.K1.ownMsgOk_gives (List.all_eq_true.1 passes.2 0
            (List.mem_range.2 (ProofFile.Honest.K1.rank_lt number))) number).2.1
    rw [keptOne] at own
    exact own
  have traceIsTheModels := traceIsTheModelsAtTheMatrices (w := w) h groundIsBlank
    (readyInputCarriesTheTrace (F := F0T OnBytes.secondHashFunction A.Z Np cF) makerReturns)
  refine ⟨p, ?_⟩
  exact
    { replyFixedBefore := by decide
      placeIsWritten := placeIsWritten
      placeIsLink24 := placeIsLink24
      roundsInFront := Nat.zero_le _
      freeAtLeast := Nat.le_refl _
      freeAtMost := by decide
      scriptSendsTheSendersText := by
        have text := ProofFile.Honest.K1.ownMsgs_switch_first (I := matrixInput) (S := Sz.ref) (Op := Op)
          h makerReturns (fun v => v = w ∧ ReadyInput (F0T OnBytes.secondHashFunction A.Z Np cF) A.H v) 0
          (p := p) (by rw [placesAre]; exact placeIsWritten) (n := 2) (by rw [four]; decide)
          firstSender
        have number : ProofFile.Honest.K2.switchNum A.Z p 2 =
            ProofFile.Honest.K2.switchNumIn seatsAllFull 24 2 := by
          unfold ProofFile.Honest.K2.switchNum
          rw [pseatsAll_at_head h.toAtMg, placeIsLink24]
        have closing : ProofFile.Honest.K1.closingB A.Z A.G =
            ProofFile.Honest.K2.lotClosingAt A.G.first.layout segsW := by
          unfold ProofFile.Honest.K1.closingB
          rw [segmentsAre]
        rw [number, closing] at text
        exact text
      readersCellsAreTheTrace := rfl
      streamSymbolsAreThePacking :=
        streamSymbolsArePackedWhereTheScriptLaysTheLastGroup _ _ _ _ _ _ _ _ _ _ _ h _ _ A.H _
          (ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref Op A cF) test carryX item n₁ n₂ 339
          (ReadyInput (F0T OnBytes.secondHashFunction A.Z Np cF) A.H) Rd Kp w Said id
          (ProofFile.Honest.K1.readersB matrixInput A.Z) 0 (ProofFile.Honest.K2.switchSeat A.Z A.G)
          (fun _ => 0) (Nat.zero_le _)
          (ProofFile.Honest.K1.laysFilling_switches h makerReturns _ 0
            (fun q isPlace k => switchIsHandedItsCoins h makerReturns (placesAre ▸ isPlace) k)
            closingsReturn
            (fun q isPlace v valid => by
              have accepts := switchTestAccepts h groundIsBlank (p := q) (placesAre ▸ isPlace)
                valid.2.1
              rw [segmentsAre]
              exact accepts)
            (by decide) (by decide))
          rfl
          (streamCellsAreTheLastGroupsAtTheModelsTrace _ _ _ _ _ _ _ _ _ _ h _ w id fun valid => by
            obtain ⟨i, xI, -, served, cells, -⟩ := traceIsTheModels valid
            exact ⟨i, xI, served, cells⟩) }

end AtTheBase

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.aWrittenSwitchLeadsIntoLink24
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.switchIsHandedItsCoins
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.deliversWhereItDeliversAtAValidInput
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.readyInputCarriesTheTrace
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.firstScriptsCellsHoldTheIndex
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.debtsAtTheFirstScript
