--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/StreamStatements.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind
K6 of the online proof): THE STREAM THAT THE HEAD BORROWS: WHERE ITS SYMBOLS ARE READ, AND FROM
WHICH ONE SENTENCE ON THE SCRIPT THEY ARE THE PACKING OF THE INPUT's CELLS. Statements: definitions
alone. The proofs: Honest/K6/Term/Stream.lean.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * NOTHING IS PAID. The law at the end is an exchange: the sentence "at the stream's seats the
    thread's witness holds the packing of the input's cells" (StreamSymbolsAreThePacking) goes; the
    sentence "the Script lays the filling at segment 22" (LaysFilling,
    Honest/K5/Law/LaysFilling.lean) comes. That sentence is shown of no Script; no Script is laid.
  * NOTHING IS SAID OF A KEPT COPY, and nothing of the code switch into link 24. Elder heads of this
    kind (Honest/K6/Law/CellsOnOfSym.lean) say that the stream "reaches the head's link in a kept
    copy". That is so of the oracle messages that are sent; it is not what the sentence reads. The
    seats are a function of a matrix's label, and the label names the OWNER's segment and array; off
    the pads a segment reads the witness's shared message at that seat.
  * It speaks only of states at which the thread stands at border 341: where the invariant holds at
    no run, the law says nothing.
  * Under the library's hypothesis h: the full size and the format's second hash function alone.
  * Nothing on soundness, on completeness or on what a proof hides.

WORDS. The stream is matrix number 7 of segment 24 (the name xbL): the activations that come into
the output head. Its owner is matrix number 7 of segment 22 (the name xbO): the activations that go
out of the last group of layers. A seat is the witness's message's number, a main row and a place.

WHAT IT IS.
  StreamSymbolsAreThePacking      THE SENTENCE THAT IS EXCHANGED, as the law on the stream's range
                                  asks it (streamIsTiedWhereItsSymbolsArePacked,
                                  Honest/K6/Term/StreamOfSymbols.lean), to the letter
  StreamIsOwnedByTheLastGroup     ON PUBLIC DATA: the label of matrix 7 of segment 24 names segment
                                  22 and the number 7
  StreamSeatsLieInTheLastGroupsArray   ON PUBLIC DATA: every seat of the stream, within its sizes,
                                  lies in the array "M7" of SEGMENT 22's list in the layout: in the
                                  witness's message with the plan's number of (22, that array's
                                  message), where the layout's rule lays the element
  StreamCellsAreTheLastGroups     ON THE INPUT's TRACE: the valid input's cells under (24, "xbL")
                                  are its cells under (22, "xbO")
  StreamCellsAreTheLastGroupsAtTheModelsTrace   that sentence holds where the valid input's trace is
                                  the integer model's: by another house's law
                                  (headReadsTheStreamOfTheLastGroup,
                                  Honest/K3/Term/BorrowedMatricesBearOneNumber.lean)
  StreamSymbolsArePackedWhereTheScriptLaysTheLastGroup   THE LAW
  ScriptHoldsTheSwitchesDataAtTheLastGroup   the one sentence in the code switches' letters: the
                                  form's field on the Script at the seat over the switches' sendings
  StreamSymbolsArePackedWhereTheScriptHoldsTheSwitchesData   the law from that sentence: the form's
                                  public field is paid there

THE ONE SENTENCE, AND WHO CAN PAY IT. LaysFilling h Q valid N readers seat heard 22: where the
filling of a segment's first sending (firstData) answers an element in a main row of a message of
segment 22, the Script's message with the plan's number holds it. It is another kind's form, made
for the matrix qa, which an attention segment borrows of its group's segment in the same way
(eSyms_of_lays). seat and heard are letters. At seat := K2.switchSeat Zp G and heard := fun _ => 0
the filling is the code switches' own data (K2.switchData, Honest/K2/OwnData.lean): there the
sentence says what THE SWITCH INTO LINK 22 sends as its own messages, and the form's public field
(reach) is a sealed theorem at the segments 1 to 23 (reach_switchSeat,
Honest/K5/Law/ReachAtHead.lean). Of the form's two fields the law spends what they say of the one
array "M7".

THE PREMISES OF THE LAW, AND WHOSE EACH IS.
  h                     the library's hypothesis on the first chain (P5J.AtMgA).
  roundsInFront         N is at most the number of rounds in front of border 341: a bound on a
                        letter.
  scriptLaysTheLastGroup   the one sentence: whoever writes the Script, with the switch's file.
  readersCellsAreTheTrace  the readers' cells at w are the trace's: by rfl at the honest readers.
  streamCellsAreTheLastGroups   on the trace: paid at the integer model's trace (above).
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.K6.Law.CellsOnOfSym

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open Inst.Model (ppref Instance)
open OnBytes.HonestTrace (Sz MatName packedCells ServesAt)
open VerifiableInference.Desc (Chain Place Strs arrayOf laidAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Law (seatLay)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K5 (LaysFilling)

/-! ## 1 On public data -/

/-- **The label of the head's matrix number 7 names segment 22 and the number 7.** -/
def StreamIsOwnedByTheLastGroup : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub) (Np : H2U.Places4)
    (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    Meaning.ownerK (Meaning.labAt (At.X Zp) 24 7) = 22 ∧
      Meaning.ownerA (Meaning.labAt (At.X Zp) 24 7) = 7

/-- **Every seat of the stream lies in segment 22's array "M7"**: the array, its two sizes, where
the layout's rule lays the element, and the message's number in the witness. -/
def StreamSeatsLieInTheLastGroupsArray : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub) (Np : H2U.Places4)
    (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ∀ (inList : 7 < (Meaning.sizesOf (At.X Zp) 24).NM) (i c : Nat),
    i < Alg.symRows ((Meaning.sizesOf (At.X Zp) 24).m 7) →
    c < (Meaning.sizesOf (At.X Zp) 24).k 7 →
    ∃ A, arrayOf (At.layout Zp) 22 (Meaning.nameOf 7) = some A ∧
      A.sizeI = Alg.symRows ((Meaning.sizesOf (At.X Zp) 24).m 7) ∧
      A.sizeC = (Meaning.sizesOf (At.X Zp) 24).k 7 ∧
      laidAt A i c =
        some ((seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, inList⟩ i c).2.1,
          (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, inList⟩ i c).2.2) ∧
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24 ⟨7, inList⟩ i c).1 =
        At.num Zp 22 A.message

/-! ## 2 The sentences at the first chain's thread -/

section Thread
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
  (cells : Tr → Cells)

/-- **THE SENTENCE THAT IS EXCHANGED**: wherever the invariant holds at border 341, at the seats of
matrix number 7 of segment 24 the thread's witness holds the image of the format's packing of the
input's cells. A definition: a premise's form. -/
def StreamSymbolsAreThePacking : Prop :=
  ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    ∀ ds (ha' : 7 < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
      Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
        (VerifiableInference.Desc.Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp)
          (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
          (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨7, ha'⟩ i' c =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cells m.st.input.trace).cell 24 7
        i'.val c.val)

/-- **On the trace**: the valid input's cells under the head's segment and the stream's name there
are its cells under the last group's segment and the stream's name there. A definition: a premise's
form. -/
def StreamCellsAreTheLastGroups : Prop :=
  Vd w → ∀ row column, (cells w.trace).cell 24 MatName.xbL.label row column =
    (cells w.trace).cell 22 MatName.xbO.label row column

/-- **THE ONE SENTENCE, IN THE CODE SWITCHES' LETTERS**: the field "lays" of LaysFilling at segment
22, at the seat over the switches' sendings and "no challenge has been heard": where the filling of
the switches' own data answers an element in a main row of message m of segment 22, the Script's
message with the plan's number of (22, m) holds it. A definition: a premise's form. -/
def ScriptHoldsTheSwitchesDataAtTheLastGroup (readers : Local W₀ Rc Inst Tr → Readers) (N : Nat)
    (G : Ground) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc Inst Tr) (hd : List Fmt.Drawn), (v = w ∧ Vd v) →
    N ≤ hd.length → ∀ (Ad : MsgAddr) (m : Nat), K2.switchSeat Zp G Ad = some (22, m) →
    ∀ (row place : Nat) (y : Cb.Gl.F ⊕ Cb.Gl.E),
    (K1.firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G)
      (fun _ => 0)).ask (readers v) hd Ad row place = .ok (some y) →
    Q.msg (At.num Zp 22 m) k v (hd.take (Q.fixedMsg (At.num Zp 22 m))) false row place =
      asE (some y)

end Thread

/-- **That sentence holds where the valid input's trace is the integer model's**, at whatever index
and instance. -/
def StreamCellsAreTheLastGroupsAtTheModelsTrace : Prop :=
  ∀ (W₀ Rc Tr : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place),
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ∀ (Vd : Local W₀ Rc Inst Tr → Prop) (w : Local W₀ Rc Inst Tr) (cells : Tr → Cells),
    (Vd w → ∃ (i : Cm.Idx) (xI : Instance ppref), ServesAt (At.X Zp) i xI ∧
      cells w.trace =
        ⟨OnBytes.HonestTrace.cellOf (At.X Zp) (OnBytes.HonestTrace.theTrace (At.X Zp) i xI)⟩) →
    StreamCellsAreTheLastGroups Vd w cells

/-- **THE LAW: where the Script lays the filling at segment 22, the stream's symbols are the packing
of the input's cells.** An exchange. -/
def StreamSymbolsArePackedWhereTheScriptLaysTheLastGroup : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (cells : Tr → Cells) (readers : Local W₀ Rc Inst Tr → Readers) (N : Nat)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat),
    N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length →
    LaysFilling h Q (fun v => v = w ∧ Vd v) N readers seat heard 22 →
    (readers w).cells = cells w.trace →
    StreamCellsAreTheLastGroups Vd w cells →
    StreamSymbolsAreThePacking h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells

/-- **THE LAW, IN THE CODE SWITCHES' LETTERS**: the public field of the form is paid there by
another kind's sealed law (reach_switchSeat, Honest/K5/Law/ReachAtHead.lean), so the one sentence on
the Script is all that is left of it. An exchange. -/
def StreamSymbolsArePackedWhereTheScriptHoldsTheSwitchesData : Prop :=
  ∀ (W₀ Rc Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ky X₀ : Type) (H : Prover W₀ Rc Inst Ky Tr X₀ X) (Bk : ProverCoinCounts)
    (Q : Script Bk (Local W₀ Rc Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (cells : Tr → Cells) (readers : Local W₀ Rc Inst Tr → Readers) (N : Nat) (G : Ground),
    blankBy pureRoad.links Zp = some G →
    N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
      declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length →
    ScriptHoldsTheSwitchesDataAtTheLastGroup h Q Vd w readers N G →
    (readers w).cells = cells w.trace →
    StreamCellsAreTheLastGroups Vd w cells →
    StreamSymbolsAreThePacking h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells

end ProofFile.Honest.K6.Term
