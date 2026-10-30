-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskOfOwn.lean: CONDITIONAL. One definition, one
abbreviation, and statements with their proofs.

What is here. THE TIE `K4MaskTieAt` (Law/ScriptAt.lean: the segment's mask row's entries under the
slots of the member of the feed-forward layers' own rounds, sub-protocol K4, are the coins that the
book lent) FOLLOWS, WHEREVER THE THREAD WITH THE LIBRARY's OWN VALUES STANDS IN FRONT OF THE MEMBER,
FROM ONE EQUATION ON THE SCRIPT's MESSAGES AT PUBLIC NUMBERS (`k4MaskTie_of_own`): message number
`maskNumAt Zp m` holds, in its mask row 0, at the places e + j with e the number of the lookup's
entries and j + 1 below the number of slots that the hearing takes (`k4Takes`), THE READING
`Reading.gl.val` OF coin number j of those that the parts of the row which the book lends K4's place
SPEND (`spentOf`, Law/Script.lean); that the reading gives the coin back behind the packing is
`val_coin` (Honest/Law/Rule/CoinBack.lean). `OwnMsgsForm` is the form of that equation: «own entries
of a message»: a form for a hypothesis on the Script: at the entries at which a text answers, the
Script's message of a number holds the text's answer. It is a second text of `OwnMsgs`
(Honest/Thread/ScriptLots.lean), which this file does not import. From `OwnMsgs` at the three fields
of K4's lot to this form at K4's text the step is taken inside the proofs of `k4MaskTie_of_ownMsgsG`
(Law/W/MaskTieOfLot.lean) and `k4MaskTie_coinsG` (Law/W/MaskLotGPub.lean). `k4MaskTxt` is K4's text
for it, an abbreviation of `Lot.k4MaskTextG` (Lot/MaskTxtG.lean), where the text lies: IT READS THE
COINS ALONE: no input and no challenge: so it is asked with 0 challenges read. Its look-up in the
list can fail; inside the fences it returns (`mask_lookup_some`, Law/W/MaskTxtGIs.lean). How. The
mask row is read off the witness link by link. The data's field mask is the one accessor at the
message that `maskOracle` names (as in the proof of the library's `mask_dataQ`,
Johnson/Road/K4/K4PinsMaskQ.lean). Three facts on the state (`maskRow_front_head`,
Law/W/MaskSixHead.lean) make that the witness's table at the seat of one member u, row 0. u is the
member found at its seat (`maskRow_find`). The table reads the message and not the pad, since every
entry asked lies at least two places below the row's last (`maskEntries_room_head`,
Law/W/MaskBelowHead.lean, against the text of `padB`). u's number is `maskNumAt Zp m`
(`maskRow_laid`, Law/W/MaskRowAtSeg.lean). The ledger's next free slot is e (`ledger_front_head`)
and the coins are `k4Takes` many (`spent_total`).

Not shown here. THAT ANY SCRIPT MEETS THE EQUATION: O is a hypothesis. NOTHING HERE SAYS THAT THE
MEMBER WHICH SENDS THE MESSAGE LAYS THESE COINS THERE: the message is another member's, and the
coins that K4 spends are runs of an owner's coins (`k4MaskOwn_of_senderLot`,
Law/W/MaskOfSenderLot.lean, has, under hypotheses on the sender's text, on public numbers and a
public test on the book, that a Script which meets `OwnMsgs` at the sender's lot meets it at K4's
text; these hypotheses are shown there of no text and no book; the test on the book is had, under
the library's head, at a book that `bookWhole` returns, at the number of scalars that the lookup's
declared rounds count, AT THE MAKER's OWN OWNER AND START, WHICH ARE NOT SHOWN TO BE THE SENDER's:
`k4Names_at_head_elems`, Law/W/LockAtHeadElems.lean). THAT THE THREAD HOLDS AT ANY RUN: hT is a
hypothesis: where the thread stands nowhere `k4MaskTie_of_own` is empty. The hypotheses, all: h (the
library's `P5J.AtMgA` on the public files), `LaidK4`, hQ (a name of a public value: `k4Pub_head`,
Law/FrontCount.lean, has it), O, hT, and the two fences of the form met at the stand (hV, hN: at the
fences «always» and 0 both hold outright). Of h together with `LaidK4`, hQ, O, hT, hV and hN no
example is known to us. That h can hold: the side library AtFullSide proves, with no hypothesis,
that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). WHERE THE BOOK LENDS
NO ROW `k4MaskTxt` ANSWERS NOTHING, the tie asks nothing, and a laying by lots lays another lot's
answer or 0 there; whether it answers is public (`k4MaskTextG_isSome`, Law/W/MaskTxtGPub.lean); no
hypothesis here says by name that the book lends the row: the form with the public test by name is
`k4MaskTie_coinsG` (Law/W/MaskLotGPub.lean). O FOLLOWS FROM `ofLots_ownMsgs`
(Honest/Thread/ScriptLots.lean) AT ANY LIST THAT HOLDS A LOT OF THESE THREE FIELDS AND AGREES WITH
IT, also at one that lacks the lot of the message's sender: it is not to be called there. THE TEXT
NAMES cells, weights, tokens AND look, though no coin hangs on them: they stand in the type of the
row's coins. Nothing on the row's last coin, which the tie on the index masks' entry names
(`K4IndexTieAt`, Law/WoTies.lean; `k4_last_coin`, Law/W/IndexOfOwn.lean). Nothing on any other entry
of the message. THE FULL SIZE ALONE, and the format's second hash function alone. Beneath it stand
closed facts by Lean's own kernel, which no independent checker has replayed (the heads of
Law/W/MaskBelowHead.lean and Law/W/MaskEllHead.lean name them). A program's walk from import to
import, which reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property.
No property is claimed.

  `OwnMsgsForm`   the form «own entries of a message». A definition: a hypothesis's form
  `k4MaskTxt`   K4's text: which entries, and which coin at each. An abbreviation
  `k4MaskTxt_at`   the text at an entry that the tie asks
  `mask_at_seat`, `tab_off_pad`   the mask row off the witness; the table off the pad
  `k4MaskTie_of_own`   **the tie, from the equation on the Script**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskBelowHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskTxtG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Johnson.Pack (pMask)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit padB)
open VerifiableInference.Desc.K9 (segAt? seatAt)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT MsgQ Mem dataQ tabQ seatTab memTab seatOf numOf)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-! ## 1 The form, and K4's text -/

/-- **OWN ENTRIES OF A MESSAGE.** n: the message's number in the witness; fx: after how many
challenges the text turns no more; txt: the entries that the asker owns, none everywhere else.
Vq, N: two fences, which make the sentence weaker. This defines a hypothesis's form; the definition
claims nothing. -/
def OwnMsgsForm {Bk : ProverCoinCounts} {W Cells Tok : Type} (Q : Script Bk W Cells Tok MsgT) (Vq : W → Prop)
    (N n fx : ℕ) (txt : Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E) : Prop :=
  ∀ k w (hd : List Fmt.Drawn), Vq w → N ≤ hd.length → ∀ mask row place y,
    txt k w (hd.take fx) mask row place = some y →
      Q.msg n k w (hd.take (Q.fixedMsg n)) mask row place = y

/-- **K4's TEXT**: in the mask row 0, at the places e + j with j + 1 below the number of slots that
the hearing takes: the reading of coin number j of those that the parts of the row which the book
lends K4's place in the first chain spend; nothing elsewhere, nothing where the book lends no row,
and nothing where the list has no such member (inside the fences it has: `mask_lookup_some`,
Law/W/MaskTxtGIs.lean). e: the first place. X: a letter of the half's type. An abbreviation: the
text is `Lot.k4MaskTextG`'s (Lot/MaskTxtG.lean). -/
abbrev k4MaskTxt {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (X : Type) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub) (e : ℕ) :
    Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E :=
  Lot.k4MaskTextG X cells weights tokens look Qp e

/-- The text at an entry that the tie asks. CONDITIONAL on hl and hj. -/
theorem k4MaskTxt_at {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub) (e : ℕ) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts}
    (hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
      (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0 = .ok c) {j : ℕ}
    (hj : j + 1 < (spentOf _ c).length) :
    k4MaskTxt X cells weights tokens look Qp e k w hd true 0 (e + j) =
      some (Reading.gl.val ((spentOf _ c).getD j zeroE)) := by
  have hlen : j < (spentOf _ c).length := by omega
  rw [spent_total cells weights tokens look Qp c] at hj
  unfold k4MaskTxt Lot.k4MaskTextG
  rw [if_pos ⟨rfl, rfl, Nat.le_add_right _ _, by omega⟩, hl, Nat.add_sub_cancel_left]
  show ((spentOf _ c)[j]?).map Reading.gl.val = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  rfl

/-! ## 2 The mask row off the witness -/

/-- The data's mask row at a message that is seated, with row bits 0 at the state: after the proof
of the library's `mask_dataQ`. CONDITIONAL on f1, f2 and f3. -/
theorem mask_at_seat {own : List (ℕ × ℕ)} {a : VerifiableInference.Desc.K9.Part} {o : ℕ}
    {y : ℕ × ℕ} (f1 : maskOracle a.L.check.frame = some o) (f2 : seatAt own a.d.book o = some y)
    (f3 : a.d.st.rowBits o .mask = 0) (rd : ℕ × ℕ → MsgQ) (ν : ℕ) :
    (dataQ own a rd).mask ν = rd y true 0 ν := by
  show (match maskOracle a.L.check.frame with
    | some o => tabQ own a.d.st a.d.book rd o .mask ν
    | none => 0) = _
  rw [f1]
  show tabQ own a.d.st a.d.book rd o .mask ν = _
  unfold tabQ
  rw [f2, f3, Nat.pow_zero, Nat.mod_one, Nat.div_one]
  rfl

/-- Below the mask row's last place the one accessor reads the message, not the pad. CONDITIONAL on
hν. -/
theorem tab_off_pad {Cells Tok : Type} (w : Wit Cells Tok MsgT) (cs : OnBytes.Codes)
    (s : OnBytes.OracleShape) (n j t row ν : ℕ) (hν : ν + 1 < (pMask cs s).ell) :
    w.tab cs s n j t true row ν = w.msg n true row ν := by
  have hp : padB cs s true row ν = false := by
    unfold padB
    have ne : (ν + 1 == (cs.mask.getD s.maskCode default).ell) = false :=
      beq_false_of_ne (by
        unfold pMask at hν
        omega)
    rw [if_pos rfl, ne, Bool.and_false]
  show (if padB cs s true row ν = true then w.pad j t true row ν else w.msg n true row ν) = _
  rw [hp]
  rfl

/-! ## 3 The tie -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, O, hT, hV and hN. **THE TIE ON THE MASK ROW, FROM ONE EQUATION ON THE
SCRIPT's MESSAGES AT PUBLIC NUMBERS.** -/
theorem k4MaskTie_of_own {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (O : OwnMsgsForm Q Vq N (maskNumAt Zp m) 0
      (k4MaskTxt X' cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo)))
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
      tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  intro a cc ha hlend ds j hj
  obtain ⟨xl, o, u, _, hl, hns, P, _, hnum, _, _⟩ := maskRow_laid h Lh
  obtain ⟨f1, f2, f3⟩ :=
    maskRow_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT P a ha
  obtain ⟨en, _⟩ := ledger_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha
  have rm := (maskEntries_room_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ hT P hl hns
    a ha cc j hj).2
  rw [mask_at_seat f1 f2 f3]
  have R2 : ∀ w : WtF, seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w (seatOf u) =
      memTab h.𝔇.cs h.𝔇.arr w u := by
    intro w
    unfold seatTab
    rw [maskRow_find P]
  rw [R2]
  show Wit.tab _ h.𝔇.cs (u.1.l.get u.2).1 (numOf h.𝔇.arr u) (u.1.seat u.2).1 (u.1.seat u.2).2 true 0
    (a.F.next + j) = _
  rw [tab_off_pad _ _ _ _ _ _ _ _ (by omega), hnum, en]
  exact O c mm.st.input (mm.st.heard ++ ds) hV
    (by
      rw [List.length_append]
      omega)
    true 0 _ _ (k4MaskTxt_at cells weights tokens look Qp _ c _ _ hlend hj)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskTxt_at
#print axioms ProofFile.Honest.K4.W.mask_at_seat
#print axioms ProofFile.Honest.K4.W.tab_off_pad
#print axioms ProofFile.Honest.K4.W.k4MaskTie_of_own
