-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/BelowPremises.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6
of the online proof): NINE OF THE PREMISES UNDER WHICH THE STRUCTURE K6HeadBelow IS FILLED, BY NAME,
WITH THE TYPE OF THE INDEX A LETTER. One definition.

WHAT IT IS NOT. Nothing is proved here. The definition is a form: nothing is claimed of it, and
whether the premises can be met together, with a valid input and a thread that stands, is not
shown. Where no input is valid (Vd false everywhere) two fields of HeadBelowDebts
(scriptSendsTheSendersText, streamSymbolsAreThePacking) hold for nothing; streamSymbolsAreThePacking
holds for nothing also at a valid input, wherever the thread's invariant holds at no state in front
of the member. Nothing says that a verifier accepts a proof. Nothing on soundness or on what a proof
hides.

WHAT IT IS. K6HeadBelow (Honest/K6/Law/ScriptBelowFree.lean) is the structure of twelve fields under
which, with the seat, this member delivers what it owes (the statement ExchangeS at border 341).

  HeadBelowDebts        nine premises, as a structure; each field says what it is about. No field
                        names the index or its reader. The premises that do are in
                        IndexPremises.lean of this folder

WORDS. As in Statements.lean of the folder Johnson/Desc/ProofFile/Honest/K6/Term/: a border is the
point in front of a member of a chain's flat list; a thread is the structure of parameters of one
chain's invariant, and its parameters are called letters; the seat is the sentence "the prover's
first side at the member's place is this kind's row". Besides: the maker is the function that makes
the prover, its book of coins and its ground from the public files and a filling (the choice of the
prover's sides); the Script is what the honest prover's messages are, as functions of a run's coins,
the input and the challenges heard.

THE NAMES' HOME. The file works inside the namespace of the head's laws, so that the premises read
there to the letter as in the laws that take them; the new name is laid in ProofFile.Honest.K6.Term.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.CellsOnOfSym
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.ProofFile.Honest.K2.OwnData
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.HonestTrace (Sz packedCells)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open P5T (seatsAllFull)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS declsTo RowDataOf Readers)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K2 (SwitchPlace switchMsgTxt lotClosingAt switchNumIn)
open ProofFile.Honest.K2.Law (placesW segsW)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky ProofFile.Honest.Cells X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) (CellsM OnBytes.Flat.numsFull)
    P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → TS → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells) X → Prop)
  (G : ProofFile.Ground)
  (rowsBeside : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
  (readers : Local W₀ Rc ProofFile.Inst ProofFile.Honest.Cells → Readers)
  (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) (N fx free : Nat)

/-- **What is left to pay for K6HeadBelow, beside "the maker returns", "the code switch's public
test accepts the input's public part", IndexHeld and TraceIsTheModels.** A structure of premises:
nothing is claimed of it. The index's type is a letter and no field names the index or its reader.
p: the place of the code switch whose first part sends the mask row that the head's rounds spend.
rowsBeside, readers, lay: what that sender's text is written at: the data of its main rows are the
code switches' own data joined to rowsBeside (K2.withSwitchData, Honest/K2/OwnData.lean), at the
reference sizes. N, fx: from how many challenges on the Script's message is that text, and how many
of them the text reads. free: how many entries of the mask row count as free. -/
structure _root_.ProofFile.Honest.K6.Term.HeadBelowDebts : Prop where
  /-- on a letter of the thread: the border from which the reply is fixed is at most 341 -/
  replyFixedBefore : b₀ ≤ 341
  /-- closed: p is one of the written places of a code switch -/
  placeIsWritten : p ∈ placesW
  /-- closed: it is the switch into link 24 (there is one: exists_link24; and just one:
  link24W_one, Honest/K2/Law/Link24Written.lean) -/
  placeIsLink24 : p.link = 24
  /-- on the letter N: at most the number of rounds in front of border 341 -/
  roundsInFront : N ≤ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
    declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 341).length
  /-- on the letter free -/
  freeAtLeast : 2168 ≤ free
  /-- on the letter free -/
  freeAtMost : free ≤ 3569
  /-- on the Script: from N challenges on, its message at the sender's number is the sender's own
  text -/
  scriptSendsTheSendersText : OwnMsgs Q (fun v => v = w ∧ Vd v) N (switchNumIn seatsAllFull 24 2) fx
    (switchMsgTxt 0 (ProofFile.Honest.K2.withSwitchData Sz.ref rowsBeside Zp G) readers
      (lotClosingAt lay segsW) p 2)
  /-- on the letter readers: the cells that the sender's text reads are the input's trace -/
  readersCellsAreTheTrace : (readers w).cells = id w.trace
  /-- on the Script and the trace: at the seats of the stream that the head borrows (matrix number 7
  of segment 24) the thread's witness holds the packing of the input's cells -/
  streamSymbolsAreThePacking : ∀ k s m E,
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E →
    ∀ ds (ha' : 7 < (Meaning.sizesOf (At.X Zp) 24).NM) i' c,
      Meaning.symAt (Meaning.sizesOf (At.X Zp) 24)
        (seatLay (At.X Zp) (At.layout Zp) (At.num Zp) 24)
        (Sound.readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) 24
          (Q.wit k m.st.input (m.st.heard ++ ds))) ⟨7, ha'⟩ i' c =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (id m.st.input.trace).cell 24 7
        i'.val c.val)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

