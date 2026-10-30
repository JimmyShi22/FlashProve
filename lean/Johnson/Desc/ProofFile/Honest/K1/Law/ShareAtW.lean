-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/ShareAtW.lean: THE SHARED "SENDING" (the kind K1): K1's SHARE
OF "THE EXCHANGE" AT NUMBER 356 (W's SENDING; THE PLACE "M:4"): pinV, AND pinV ALONE: WHAT THE
GATHER's BINDER ASKS THERE · K1's SHARE AT THE RETURNED PROVER AND ITS OWN BOOK. Two theorems; no
definition. NO NEW ARGUMENT: CALLS.

UNDER THE HEAD, A RETURNED PROVER, TWO PREMISES ON THE LOTS AND THE TIE, WHICH HOLDS AT NO SCRIPT
THAT ANYBODY HAS: IT PAYS NOTHING AT A SCRIPT. R IS "EXCHANGED", NOT "HAD".

  - asked_w: PUBLIC: of the four items that ProofFile's forward row owes at 356 (pinV, pileOne, pinW,
    wrow) the gather's binder hX356 asks three: pinW is open in front of 356 and falls out by the
    binder's own premise ("j open → j ≠ pinW"): an item that is owed and passes that premise is
    pinV, pileOne or wrow.
  - k1_share_w_at_book: ExchangeAtS L.thread Said 356 pinV, AT ProofFile's OWN LETTER L, at the returned
    prover A.H and its own book A.B: the binders are k1Seated_w_at_book's (RecordAtBookFill.lean),
    one string, and Said: one "obtain" and one call of exchange_pinV (ExchangeAtPins.lean).

WHOSE THE OTHER ITEMS ARE. wrow, pileOne, pinW: KIND K13's: another house's k13_seated_m4
(Honest/K13/SeatedM4.lean): in the elder form ExchangeOf, under its record K13SeatedM4. pinW also:
ProofFile's exchangeAt_pinW (Honest/Thread/HeadPinW.lean). NOT JOINED HERE.

KIN, TOLD; NONE IS RESTATED. What the row owes at the place "M:4": owes_at_m4, owes_tied
(Honest/K13/ExchangeM4Proof.lean). What is open in front of 356: m4_open_is
(Honest/K13/RidesAtM4.lean): CALLED; m4_pileOne_open (Honest/K13/ExchangeM4At.lean). The share at
pinV at a general L, b, under the record at the sort .w: exchange_pinV: at lettersHead and 356 it is
that law's instance: not typed.

THE BOOK. The sentence, to the letter, with
its second arm, in marks: "At a book whose count at the part's address does not cover the part's due
this law holds for nothing, and it is never quoted as if it spoke there: hasCoins is paid at the
returned prover's own book by hasCoins_w_at_book." OUR OWN WORDS: that lemma lies in
HasCoinsAtBook.lean and is called inside k1Seated_w_at_book (RecordAtBookFill.lean), which
k1_share_w_at_book calls. NO GUARD STANDS IN THE STATEMENT: THE BOOK A.B IS NO LETTER THAT COULD BE
SHORT. asked_w names no book.

Limits. THE FULL SIZE ALONE; the format's second hash function alone. That hA, hex, ho, msgs and pads can be
met together is not proved. The end stands under the pair ThrS and the member's accepted step. It
stands over files of L25's, of another house's and of ours; some are on no seal. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtBookFill
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.ProofFile.Honest.K13.RidesAtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 100000 in
/-- **WHAT THE GATHER's BINDER ASKS AT 356: THREE OF THE FOUR.** -/
theorem asked_w {j : Item} (hj : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps 356).owes)
    (hx : j ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356 →
      j ≠ Item.pinW) :
    j = Item.pinV ∨ j = Item.pileOne ∨ j = Item.wrow := by
  have e : (FirstRows.rows P5J.At.links P5J.At.ps 356).owes =
      [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] := by decide +kernel
  rw [e] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · have ho := List.all_eq_true.1 K13.m4_open_is.2 Item.pinW (by simp)
    exact absurd rfl (hx (List.contains_iff_mem.1 ho))
  · exact Or.inr (Or.inr rfl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- UNDER THE HEAD, A RETURNED PROVER, TWO PREMISES ON THE LOTS AND THE TIE, SHOWN HERE AT NO
SCRIPT THAT A RUN HAS: IT PAYS NOTHING AT A SCRIPT:
**K1's SHARE AT NUMBER 356, AT THE PROVER's OWN BOOK: pinV.** -/
theorem k1_share_w_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters A.B ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
      (Dd Zp A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 356)
        ((P5J.At.arr Zp) (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2)
        (L.thread.front + roundsTo L.bs 356) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2
        (fun k _ => padTxt 0 J n k))
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS L.thread Said 356 Item.pinV := by
  obtain ⟨blk, R⟩ := k1Seated_w_at_book h hA wit no Dd hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp
    w own₀ hL hJ msgs pads
  exact exchange_pinV R Said

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.asked_w
#print axioms ProofFile.Honest.K1.k1_share_w_at_book
