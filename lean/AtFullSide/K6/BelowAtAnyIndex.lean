-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K6/BelowAtAnyIndex.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the online proof):
ALL TWELVE FIELDS OF K6HeadBelow AT ONE SET OF LETTERS, WITH THE TYPE OF THE INDEX A LETTER, UNDER
THIRTEEN NAMED PREMISES. One definition (these letters) and one theorem: calls and five short lines.

WHAT IT IS NOT. It pays none of its thirteen premises. It does not say that the member delivers what
it owes at any run, and not that a verifier accepts. That the premises can be met together with a
valid input is not shown here (near it, at the base prover: a valid input at storedPublicFiles, by its clauses:
AtFullSide/HonestTrace/EntersAtStoredFilesInput.lean; eleven of the premises, under three others:
AtFullSide/E2E/OutputHeadDebtsAtTheFirstScript.lean); that they can be met with a thread that stands
is shown by nobody: where no input is valid, five of the twelve fields (index, points, guests,
cellsOn, reader) and four of the premises hold for nothing; and at a valid input, wherever the
thread's invariant holds at no state in front of the member (a letter Said that is false there; a
border b₀ so small that no reply is laid yet), four fields (points, guests, cellsOn, reader) and
streamSymbolsAreThePacking hold for nothing still. The prover H and the book A.B are tied by nothing
here: that H has the sides of the prover which the maker returns with that book is the caller's to
set. The library's hypothesis h holds at the full size and the format's second hash function alone. Closed
facts that Lean's kernel decided by evaluation at written values lie beneath: on the book, on the
written places of the code switches and the switch into link 24, on the closings, on the layout's
arrays of link 24. Nothing on soundness or on what a proof hides.

WHAT IT IS. K6HeadBelow (Honest/K6/Law/ScriptBelowFree.lean) is the structure of twelve fields under
which, with the seat, the member at border 341 of the online proof's first chain delivers what it
owes (ExchangeS: k6_exchangeS_of_below). Here the twelve are filled at once, each by a law that is
general in the index's type W₀, in the type Rc of the stored tables' randomness and in the filling
P. So the theorem can be called at the honest prover's index, a matrix
(AtFullSide/E2E/OutputHeadBelowAtTheHonestProver.lean does).

THE THIRTEEN PREMISES, beside h. makerReturns: the maker of the prover returns A at the filling P;
of A the theorem reads the book A.B and the ground A.G alone. The nine fields of HeadBelowDebts,
then publicTestAccepts (the code switch's public test accepts the input's public part), IndexHeld
and TraceIsTheModels (BelowPremises.lean and IndexPremises.lean of the folder
Johnson/Desc/ProofFile/Honest/K6/Term/ say of each what it is about). Six of the nine are closed, or
bounds on a letter, or a choice of a letter that the caller makes (placeIsWritten, placeIsLink24,
freeAtLeast, freeAtMost, replyFixedBefore, readersCellsAreTheTrace); roundsInFront is met at N := 0,
where scriptSendsTheSendersText asks the most. SO SIX BEAR WEIGHT: makerReturns, publicTestAccepts,
scriptSendsTheSendersText, streamSymbolsAreThePacking, IndexHeld, TraceIsTheModels. OF THE TWELVE
FIELDS seven are light: sender and lent hold by the choice of the letters rowOf and own, reply is
339 ≤ 341, and ground, below, inside, stretch are facts on public data and the book; the weight lies
in index, points, guests, cellsOn, reader.

NO PREMISE ON THE BOOK IS LEFT. That the book lends the code switch's first part what its text asks
(the public test lendsPart) follows from h and makerReturns: bookLendsTheSwitch
(AtFullSide/K6/BookLendsTheSwitch.lean). WHAT THAT TEST IS NOT: lendsPart asks name, count and that
the owners' cuts fit: it holds as well at a book that lends another owner's coins of that count. Of
it this file reads two things: the part's own count is the book's count at the part's address, and
the part is handed something at every run's coins.

WHICH FIELD BY WHICH LAW. reply: the premise. ground: ground_of_blank. index: the premise IndexHeld.
points: k6_points_at_head. guests: k6_guests_of_theTrace, from TraceIsTheModels. cellsOn:
k6_cellsOn_of_sym_and_stream, from k6_sym_at_withSwitchData (Honest/K6/Cells/SymAtTake.lean: at the
seats of the head's six own matrices the witness holds the packing of the input's cells: from the
premises on the sender's text), streamIsTiedWhereItsSymbolsArePacked
(Honest/K6/Term/StreamOfSymbols.lean: the same for the borrowed stream, from
streamSymbolsAreThePacking) and k6_small_of_theTrace (from two limbs of TraceIsTheModels). reader:
k6_reader_at_link24. stretch: k6_stretch_at_switch. below: k6_below_of. sender, lent:
sender_at_take, lent_at_take. inside: inside_at_link24.

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's flat list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.

THE NAMES' HOME. As in BelowPremises.lean: the file works inside the namespace of the head's laws;
the new name is laid in ProofFile.Honest.K6.Term.
-/
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.PointsAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.SmallOfTheTrace
import Johnson.Desc.ProofFile.Honest.K6.Term.IndexPremises
import Johnson.Desc.ProofFile.Honest.K6.Term.BelowPremises
import Johnson.Desc.ProofFile.Honest.K6.Law.ReaderAtLink24
import Johnson.Desc.ProofFile.Honest.K6.Term.StreamOfSymbols
import Johnson.Desc.ProofFile.Honest.K6.Cells.SymAtTake
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import AtFullSide.K6.StretchAtSwitch
import AtFullSide.K6.BookLendsTheSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover OnlineProverParts OnlineProverWithDescription onlineProverFromPublicFiles atPure_ok atPure_at_laid RowDataOf
  Readers lendsPart lookDue)
open ProofFile.Honest.FirstThread (Script WtF)
open ProofFile.Honest.K2 (SwitchPlace publicOk)
open ProofFile.Honest.K2.Law (placesW segsW)
open ProofFile.Honest.K6 (k6_points_at_head k6_stretch_at_switch k6_below_of)
open ProofFile.Honest.K6.Term (IndexHeld TraceIsTheModels HeadBelowDebts)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place} {W₀ Rc Ky X₀ X₀' X : Type}

/-- **K6HeadBelow at the letters of the sender of the mask row**: the address of the switch's first
part; that part's own count; the row that is the part's coins from the mask row's start on; the
part's coins as the book's cut of a run's coins; that start; the head's count of entries spent; and
free. The reader of the trace's cells is the identity. bookLends: the book's public test on that
part accepts; the cut is opened by it. -/
abbrev _root_.ProofFile.Honest.K6.Term.HeadBelowAtTheSwitch {Bk : ProverCoinCounts}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (H : Prover W₀ Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀' X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop)
    (weights : W₀ → ProofFile.Honest.Weights) (G : ProofFile.Ground) (p : SwitchPlace) (free : Nat)
    (bookLends : lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (takePart p) = true) :
    Prop :=
  K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id weights G ⟨p.place, 0⟩ (takeDue p)
    (rowFromCoin (takeBase p 2))
    (ownByCut 0 (Nat.zero_le 1) ⟨p.place, 0⟩ (takeDue p) (covers_of_lends bookLends))
    (takeBase p 2) (takesOf (parOf (At.X Zp).hS (workOf (At.X Zp)))) free

variable {P : OnlineProverParts W₀ Rc ProofFile.Honest.Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc ProofFile.Honest.Cells X₀ X}
  {H : Prover W₀ Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀' X}
  {Q : Script A.B (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) (CellsM OnBytes.Flat.numsFull)
    P5J.At.Tok MsgT}
  {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {item n₁ n₂ b₀ : Nat} {Vd : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Prop}
  {Rd : Nat → Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop}
  {Kp : Place → TS → TS → Prop} {w : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells}
  {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop}
  {weights : W₀ → ProofFile.Honest.Weights}
  {rowsBeside : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Readers}
  {lay : OnBytes.Params.ReqLayout} {p : SwitchPlace} {N fx free : Nat}

/-- CONDITIONAL on the library's hypothesis h on the public files and on thirteen named premises,
none of which is paid here; it may hold for nothing (the head says where). **ALL TWELVE FIELDS OF
K6HeadBelow AT THE BOOK AND THE GROUND OF A RETURN OF THE MAKER AND AT THE LETTERS OF THE SENDER OF
THE MASK ROW, THE INDEX's TYPE, ITS READER, THE FILLING AND THE PROVER LETTERS.** -/
theorem _root_.ProofFile.Honest.K6.Term.headBelowUnderNamed
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (debts : HeadBelowDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said A.G rowsBeside readers
      lay p N fx free)
    (publicTestAccepts : publicOk
      (ProofFile.Honest.K2.withSwitchData OnBytes.HonestTrace.Sz.ref rowsBeside Zp A.G) lay p
      (segsW.take p.link) w.x = true)
    (indexHeld : IndexHeld Q weights Vd w)
    (traceIsTheModels : TraceIsTheModels Zp A.G weights Vd w) :
    ProofFile.Honest.K6.Term.HeadBelowAtTheSwitch h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said weights
      A.G p free
      (ProofFile.Honest.K6.Term.bookLendsTheSwitch h makerReturns debts.placeIsWritten) := by
  have groundIsBlank := ProofFile.Honest.K6.Term.groundOfAReturnIsBlank h makerReturns
  have freeAtMost := debts.freeAtMost
  unfold ProofFile.Honest.K6.Term.HeadBelowAtTheSwitch
  exact
    { reply := debts.replyFixedBefore
      ground := ground_of_blank groundIsBlank
      index := indexHeld
      points := k6_points_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id weights
        groundIsBlank
      guests := k6_guests_of_theTrace h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id weights
        groundIsBlank traceIsTheModels
      cellsOn := k6_cellsOn_of_sym_and_stream h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id
        groundIsBlank
        (k6_sym_at_withSwitchData h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said readers lay N fx
          id rowsBeside groundIsBlank debts.placeIsWritten debts.placeIsLink24
          (ProofFile.Honest.K6.Term.bookLendsTheSwitch h makerReturns debts.placeIsWritten)
          debts.roundsInFront publicTestAccepts debts.scriptSendsTheSendersText
          debts.readersCellsAreTheTrace)
        (k6_small_of_theTrace h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said id groundIsBlank
          fun valid => by
            obtain ⟨i, xI, -, served, cells, -⟩ := traceIsTheModels valid
            exact ⟨i, xI, served, cells⟩)
        (ProofFile.Honest.K6.Term.streamIsTiedWhereItsSymbolsArePacked h H Q test carryX item n₁ n₂ b₀ Vd
          Rd Kp w Said id groundIsBlank debts.streamSymbolsAreThePacking fun valid => by
            obtain ⟨i, xI, -, served, cells, -⟩ := traceIsTheModels valid
            exact ⟨i, xI, served, cells⟩)
      reader := k6_reader_at_link24 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
        (ProofFile.Honest.K2.withSwitchData OnBytes.HonestTrace.Sz.ref rowsBeside Zp A.G) readers lay N
        fx free debts.placeIsWritten debts.placeIsLink24
        (ProofFile.Honest.K6.Term.bookLendsTheSwitch h makerReturns debts.placeIsWritten)
        debts.roundsInFront
        (by omega)
        (by rw [(InScope.plan_in_scope h.scope h.reads h.pubOne).ns]; omega)
        publicTestAccepts debts.scriptSendsTheSendersText
      stretch := k6_stretch_at_switch h makerReturns debts.placeIsWritten debts.placeIsLink24 _
      below := k6_below_of h debts.freeAtLeast
      sender := sender_at_take _ _ _
      inside := inside_at_link24 (h := h) (free := free) debts.placeIsWritten debts.placeIsLink24
        (by omega)
      lent := lent_at_take _ _ _ }

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms ProofFile.Honest.K6.Term.headBelowUnderNamed
