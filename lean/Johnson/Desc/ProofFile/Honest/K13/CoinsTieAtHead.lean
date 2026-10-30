-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsTieAtHead.lean: kind K13, the members' batching: UNDER THE
LIBRARY's HEAD h AND NAMED PREMISES ON THE SCRIPT, THE SENDING AND THE BOOK (they are not shown;
no example is known at which all hold and the thread stands somewhere): THE KIND's TIE `CoinsTie`
(ExchangeAtM3.lean of this folder) AT THE FIRST CHAIN's THREAD AT THE HEAD (`lettersHead`,
Honest/Thread/FirstHead.lean), AT THE BORDER 355, AT THE LIBRARY's READER (`k13ReaderAt`), AT KIND
K1's OWN TEXT `msgTxt`. THAT THE BOOK's ENTRY FOR THE KIND's ROW BEGINS AT maskStart + 13 IS THE
PREMISE hS: A TEST ON THE BOOK THAT HAS NOT RUN: IT IS ASSUMED, NOT SHOWN. THE SENDING's TABLE OF
CODES (J.P.codes) IS TIED TO THE VERIFIER's BY NOTHING HERE. All is on what is written and read
where, at every run: no entry is said to be fresh, uniform or a mask; it is not said that a value is
laid once; that msgTxt answers is said only under the public test `bookCovers`; nothing is said on
what an entry is for. Seven statements with their proofs; no definition. THE FULL SIZE AND THE
FORMAT's EARLIER HASH ALONE: 355, 13, 4 and (1, 0) are that size's numbers.

Main names.
`heard_reaches`: where a thread stands at a border, the challenges heard are at least those in front
of any border that is no later. `castWit_mask`: the cast of the reader's number of rows leaves its
mask entries. `k13_len`: under h the first chain has at least 355 members.
`k13_state_facts`: **under h, where the ledger as it is made has at least 13 free entries: wherever
the thread stands at 355 the eight facts on the state hold** that `coinsTie_of_facts`
(CoinsTieOfFacts.lean of this folder) asks, at im := 4 and k₀ := 13.
`k13_taken_at_head`: **THE LEDGER's TAKES: there, whatever the verifier's taking of n' entries of
the index masks' message returns is the list of the entries of the takes 13, 14, …, 13 + n' - 1.**
`k13_reader_at_take`: **THE READER AT A TAKE: there, under hO, hcov, the public premises on the
sending and the two between it and the verifier's list (premises here; shown under h, O and hP, at n
= 4, in AtFullSide/K13/CoinsTieFive.lean), at every ν below the ledger's count: what the reader
reads at the entry of the take number ν is the value number maskStart + ν of the sender's cut**
`lentCut`, read by `ce`: an equation of options by its type, the cut named; its left side is `some`
by form, so at a book that does not cover the count it would be false: hcov is a premise, and of
such a book nothing is said. `ce` GIVES 0 BEYOND THE PART's COUNT (Honest/K1/Coins.lean): under hn,
hfit, ha, hfreeP and ν below the count K1's `mask_in` (Honest/K1/MaskLaw.lean) gives maskStart + ν
below the count of dueR J.P J.ride, so no 0 of that sort is read; THIS STATEMENT DOES NOT CALL IT;
the tie's road does, in CoinsTieOfK1.lean. The 13 has no part in its conclusion: it is asked because
that the message is there, with a mask row and an answer, is had from `LedgerAt s.st 4 13`.
`k13_coinsTie_of_msgTxt`: **the tie**: its type has the two outer ends alone: what the reader reads
under the j-th entry taken, and the j-th value that the book lends the kind's row. THE TWO
STATEMENTS ON THE TAKES ARE CALLED BY NOTHING: they state at the head two steps that the tie's proof
takes anew inside CoinsTieOfFacts.lean and CoinsTieOfMsgTxt.lean. WITH hS THEY DO NOT CLOSE THE TIE:
also wanted are that the state's number of the message is 4, hfree, `val_coinsE_getD`
(CoinsTieOfK1.lean), AND THE BOOK's STEP: that the j-th of what the row's parts spend is the
sender's cut's value at the book's entry's start + j: IT HAS NO STATEMENT HERE: it is taken inside
`coinsTie_of_facts`, by `maskTieOn_whole_free` (Honest/Law/Rule/TiesFree.lean) under hS.

THE PREMISES OF `k13_coinsTie_of_msgTxt`, BESIDE h; NONE IS SHOWN HERE. hO (THE SCRIPT's: `OwnMsgs`
at the thread's own `valid` (the one input w₁, where Vd w₁ holds), at lists of challenges at least
as long as the rounds in front of a border b₁ ≤ 355 (meant: the border in front of the sender's
sub-protocol), at the witness's number `k4IndexNum Zp`, at msgTxt … n: that the Script is laid so,
AND THAT THE SENDER's MESSAGE NUMBER n IS LAID AT THAT NUMBER: under kind K1's record of premises at
the opening both are had, at n = 4: CoinsTieOfSeated.lean of this folder; the record itself is a
premise there) · hcov (THE BOOK's: THE PUBLIC TEST `bookCovers`, Honest/K1/ScriptAt.lean, BY NAME:
the book's count at the sender's address covers the part's) · hS (THE BOOK's: the public test
`oneStretch`, Honest/BookStretch.lean: the entries for the kind's row are one stretch of the
sender's, from maskStart + 13 on, 2 kCol + 1 long; StretchAtHead.lean of this folder carries it,
under h, to "the book is the one that the maker `bookWhole` returns" and two public sentences that
name no book: none of the three is shown here; h3 is had under h at the written sendings
(`k13_h3_at_head`, AtFullSide/K13/WantsAtHead.lean), and h1 falls under h, O, hP and hR, at n = 4
and the written sendings (AtFullSide/K13/CoinsTieWritten.lean); `k13_coinsTie_of_seated_whole`
(CoinsTieOfSeated.lean) joins the two statements) · hn, hfit, ha (public, on the sending alone: it
has a message number n; `sendFits`; that message has an answer) · hshape, hfreeP (public, BETWEEN
THE SENDING AND THE VERIFIER's LIST: premises here; shown under h, O and hP, at n = 4, in
AtFullSide/K13/CoinsTieFive.lean: the listed shape at number 4 is that message's; the ledger's count
as it is made, which is at the public part's codes, is at most the shape's count at the sending's
codes) · hfree (numbers: 13 + (2 kCol + 1) is at most the ledger's count).

How. `k13_state_facts` by calls: `ProofFile.Honest.K4.W.indexFacts_thr`
(Honest/K4/Law/W/IndexFactsThr.lean) at the border 355, whose premise on the item pinI is the
library's `pin_at` (Johnson/HB/LLHARD/IndexOpenWritten.lean); `ledgerAt_of_left`
(Honest/K4/Law/W/IndexLedgerAt.lean) at what `head_room` (Honest/Thread/RoomAtHead.lean) says is
left, at `P1L20.takenAt 355 = 13` (`m3_takenAt`, TakenAtM3.lean of this folder); that the two terms
for the ledger's count are one number: the library's `P1L20.free0_is` at `P5J.startB_at_head`.
`k13_len`: the lines that stand inside `k13_reach_at` (TakenAtM3.lean), as a lemma. `heard_reaches`:
`Thread.heard_length` (Honest/Thread/PaysLaw.lean) and `roundsTo_mono`
(Honest/Thread/ScriptFit.lean). The ledger's takes: `takeMasksP_numbers`
(Johnson/Desc/K13/Honest/TakenList.lean). The reader at a take: `reader_mask_own`
(ReaderMaskScript.lean of this folder) at K1's `msgTxt_mask_slot` (Honest/K1/ScriptMaskSlot.lean).
The tie: `coinsTie_of_msgTxt` (CoinsTieOfMsgTxt.lean of this folder), its premise `OwnIs` from hcov
by K1's `lentCut_isSome` (Honest/K1/ScriptAtLaw.lean) at the chain number 0.

Who spends the tie: it is the premise hC of `k13_pileOne_at` and `k13_exchange_at`
(ExchangeAtM3.lean), which are stated at `lettersAt`; no call at `lettersHead` is made here.

Limits. NOT IN FRONT OF A LAW OVER COINS: the ground: the Limits of CoinsTieOfFacts.lean of this
folder. CONDITIONAL ON h AND THE PREMISES NAMED: none is shown here of any Script, sending or book;
that h can be met, and that the thread holds at any run, is not shown here: it stands at the one
input w₁ alone, and nowhere where Vd w₁ fails; where it holds nowhere all holds for nothing. THE TIE
ALSO HOLDS FOR NOTHING WHERE THE BOOK's LENDING (`lendRow`) ERRS AT THE KIND's ROW, OR WHERE THE
VERIFIER's TAKING DOES NOT RETURN: both stand in front of its equation (`CoinsTie`,
ExchangeAtM3.lean). OF THE TAKING: under h it returns wherever the thread stands at 355
(`k13_guard_taken`, GuardsAtM3.lean of this folder, at `lettersAt`, of which `lettersHead` is an
instance by its text): so that case is empty at these letters. OF THE LENDING: no premise here gives
it; under h it returns at the book that the maker returns at the head's own three lists of sendings
(`k13_lendRow_at_head`, AtFullSide/K13/LendRowAtHead.lean, where that return is a premise). THE TIES
OF COUNTS THAT CoinsTieOfFacts.lean's head names are premises here: in hS (maskStart + 13 against
the book's entry's start), in hO (n against k4IndexNum Zp), in hshape and hfreeP. Under the thread
the state's codes are the public part's (a field of `indexFacts_thr`'s conclusion): what lacks is
one equation on public data: J.P.codes against P5J.At.cs Zp. That no value is laid at two places is
not said: not across messages, and NOT AGAINST THE OTHER TWO KINDS THAT SPEND ENTRIES OF THIS ONE
MESSAGE (K4; K11, one entry): that the three spenders' stretches do not meet is the book's matter
(`ProverCoinCounts.clauses`, Honest/Frame.lean: the clause "a coin stands in two entries that spend it"; the
maker's test `wantsFree`, Honest/BookEntries.lean, over all pairs of stretches) and is named in no
statement here. "Coin" is the frame's word for a value that the book hands out. This file's imports
reach Johnson/Goal/: the hypothesis h is the library's own (`P5J.AtMgA`), which is stated over the
goals' description. No definition stands here.

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.CoinsTieOfMsgTxt
import Johnson.Desc.ProofFile.Honest.K13.TakenAtM3
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexFactsThr
import Johnson.Desc.ProofFile.Honest.Thread.RoomAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.HB.LLHARD.IndexOpenWritten
import Johnson.P1L20R.Free0Is
import Johnson.P5J.StartAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K12.Door (msgsOfChain msgShapesB bookInOrderB seatsCarriedB
  placesBelowB msgShape_at)
open VerifiableInference.Desc.K13.Law (Wit rwBook LFull pin_at LedgerAt dOf)
open VerifiableInference.Desc.K13.Honest (takeMasksP_numbers)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs head_room)
open ProofFile.Honest.K4.W (indexFree0 IndexMaskFacts indexFacts_thr ledgerAt_of_left)
open ProofFile.Honest.K4.Lot (k4IndexNum)
open ProofFile.Honest.K1 (dueR ce sendFits msgTxt lentCut bookCovers lentCut_isSome msgTxt_mask_slot
  fits_noRide free_lt)

/-- **Where a thread stands at a border, the challenges heard are at least those in front of any
border that is no later** (the rounds in front of the chain counted). General in the thread. By
`Thread.heard_length` and `roundsTo_mono`. -/
theorem heard_reaches {Bk' : ProverCoinCounts} {S' Cl' V' W'' X'' Pb' : Type}
    {T : Thread Bk' S' Cl' V' W'' X'' Pb'} {b b₁ : ℕ} (hb : b₁ ≤ b) {k : Coins Bk'} {s : S'}
    {m : Mid W'' X''} {En : Env} (hT : Thr T b k s m En) :
    T.front + roundsTo T.bs b₁ ≤ m.st.heard.length := by
  rw [Thread.heard_length T hT.2.1]
  exact Nat.add_le_add_left (roundsTo_mono _ _ _ hb) _

/-- The cast of the number of rows leaves the mask entries. -/
theorem castWit_mask {K : Type} {n n' k : Nat} (e : n = n') (W : Wit K n k) :
    (castWit e W).mask = W.mask := by
  subst e
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)

include h in
/-- Under h the first chain has at least 355 members. -/
theorem k13_len : 355 ≤ cF.blocksInOrder.length := by
  cases hb : cF.blocksInOrder[355]? with
  | none =>
    have e : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[355]? = none := by
      show (cF.blocksInOrder.map (·.place))[355]? = none
      rw [List.getElem?_map, hb]
      rfl
    rw [P5J.At.places_paid h.scope h.reads h.laid, m3_place] at e
    cases e
  | some blk => exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE EIGHT FACTS ON THE STATE, WHEREVER THE THREAD STANDS AT THE BORDER 355.** CONDITIONAL: on
h; sh is the listed shape at number 4; the ledger as it is made has at least 13 free entries. -/
theorem k13_state_facts {sh : OracleShape}
    (hsh : (msgsOfChain Zp.made.proof.1)[4]? = some sh) (h13 : 13 ≤ indexFree0 Zp cF) :
    ∀ k s m En, Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 355
        k s m En →
      s.out.indexMasks = 4 ∧ msgShapesB (msgsOfChain Zp.made.proof.1) s.st = true ∧
        bookInOrderB 0 s.book s.roots = true ∧ seatsCarriedB LFull s.book = true ∧
        s.book.place.size = s.st.oracles.size ∧
        placesBelowB LFull s.book.place.size s.book.trees.size = true ∧ LedgerAt s.st 4 13 ∧
        indexFree0 Zp cF = Send.freeMaskEntries sh.maskRows
          (s.st.codes.mask.getD sh.maskCode default).ell sh.answers := by
  intro k s m En hT
  obtain ⟨sh', F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (k13_len h) (by decide) (pin_at (k := 355) (by decide) (by decide)) hT
  obtain rfl : sh' = sh := Option.some.inj (F.hsh.symm.trans hsh)
  obtain ⟨Bs, base', O⟩ := h.toAtMg.laid.opened
  have hfr : VerifiableInference.Desc.K1.free0Of Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp) = indexFree0 Zp cF :=
    P1L20.free0_is O (P5J.startB_at_head h.toAtMg)
  have hL := (head_room h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ O (k13_len h) (by decide)
    (Nat.le_refl _) hT).1
  rw [m3_takenAt, hfr] at hL
  refine ⟨F.hi, F.h₁, F.h₂, F.h₃, F.hs, F.hb,
    ledgerAt_of_left F.hi F.h₁ F.hc F.hW hL F.hsh F.hf (by omega), ?_⟩
  rw [F.hc]
  exact F.hf

/-- **THE LEDGER's TAKES: WHAT THE TAKING AT 355 RETURNS IS THE LIST OF THE ENTRIES OF THE TAKES
13, 14, ….**
CONDITIONAL: as `k13_state_facts`; the thread stands at 355; the taking of n' entries returns t. -/
theorem k13_taken_at_head {sh : OracleShape}
    (hsh : (msgsOfChain Zp.made.proof.1)[4]? = some sh) (h13 : 13 ≤ indexFree0 Zp cF)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 355 k s m En)
    {n' : ℕ} {t : List ℕ × VerifiableInference.Desc.K13.St}
    (ht : takeMasksP (dOf s) s.out.indexMasks n' = some t) :
    t.1 = (List.range n').map fun j => takenNo sh.maskRows (13 + j) := by
  obtain ⟨hi, h₁, _, _, _, _, hL, _⟩ :=
    k13_state_facts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hsh h13 k s m En hT
  obtain ⟨x, _, hx, _⟩ := id hL
  obtain ⟨hoo, _⟩ := Array.getElem?_eq_some_iff.1 hx
  have hxs : x.shape = sh := by
    have e := msgShape_at h₁ 4 hoo
    rw [hx, hsh] at e
    exact Option.some.inj e
  rw [hi] at ht
  have e := takeMasksP_numbers (d := dOf s) hL hx ht
  rw [hxs] at e
  exact e

/-- **THE READER AT A TAKE: WHAT IT READS AT THE ENTRY OF THE TAKE NUMBER ν IS THE VALUE NUMBER
maskStart + ν OF THE SENDER's CUT.** An equation of options; the cut is named. `ce` gives 0 beyond
the part's count: K1's `mask_in` bars that under hn, hfit, ha, hfreeP and hν; it is not called here.
CONDITIONAL: on h, hO (at the thread's own `valid` and at lists of challenges at least as long as
the rounds in front of a border b₁ ≤ 355), the public premises on the sending (hn, hfit, ha) and
between it and the verifier's list (hshape, hfreeP: premises here), the public test `bookCovers`;
the thread stands at 355; ν is below the ledger's count as it is made, which is at least 13. -/
theorem k13_reader_at_take {fx : ℕ} {W' Y' : Type}
    (wit : Local W₀ Rc ProofFile.Inst Tr → W') (J : K1.SendJob W' Y') (own₀ : Y') (n : ℕ)
    {b₁ : ℕ} (hb₁ : b₁ ≤ 355)
    (hO : OwnMsgs Q (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).valid
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front +
        roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).bs b₁)
      (k4IndexNum Zp) fx
      (msgTxt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain wit J own₀
        n))
    (hn : n < J.P.sent.size) (hfit : sendFits J.P J.ride = true)
    (hshape : (msgsOfChain Zp.made.proof.1)[4]? = some (shapeAt J.P n))
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hfreeP : indexFree0 Zp cF ≤ Send.freeMaskEntries (shapeAt J.P n).maskRows
      (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell (shapeAt J.P n).answers)
    (hcov : bookCovers Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain
      ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true)
    (h13 : 13 ≤ indexFree0 Zp cF)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 355 k s m En)
    (ds : List Fmt.Drawn) {ν : ℕ} (hν : ν < indexFree0 Zp cF) :
    some ((k13ReaderAt h
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m.st.input.x, s)
        (Q.wit k m.st.input (m.st.heard ++ ds))).mask
          ⟨4, takenNo (shapeAt J.P n).maskRows ν⟩) =
      (lentCut k (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain
        ⟨J.P.place, 0⟩ (dueR J.P J.ride)).map fun c => ce c (K1.maskStart J.P J.ride n + ν) := by
  obtain ⟨_, h₁, h₂, h₃, hs, hbk, hL, hf⟩ :=
    k13_state_facts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hshape h13 k s m En hT
  obtain ⟨_, F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (k13_len h) (by decide) (pin_at (k := 355) (by decide) (by decide)) hT
  obtain ⟨x, _, hx, _, hm, ha', _⟩ := id hL
  obtain ⟨hoo, _⟩ := Array.getElem?_eq_some_iff.1 hx
  have hxs : x.shape = shapeAt J.P n := by
    have e := msgShape_at h₁ 4 hoo
    rw [hx, hshape] at e
    exact Option.some.inj e
  have hr : J.ride n = none := fits_noRide J.P J.ride n hfit hn ha
  have hsome := lentCut_isSome k
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain (Nat.zero_le 1)
    ⟨J.P.place, 0⟩ (dueR J.P J.ride)
  rw [hcov] at hsome
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
  rw [hc]
  show some _ = some _
  refine congrArg some ((congrFun (castWit_mask _ _) _).trans ?_)
  refine (reader_mask_own Q k m.st.input (m.st.heard ++ ds) h.𝔇.arr h.𝔇.mat13
    (msgsOfChain Zp.made.proof.1) LFull _ s 4 ν (shapeAt J.P n) (1, 0) h₁ h₂ h₃ hs hbk hoo hshape
    F.hq (hxs ▸ hm) (hxs ▸ ha') (hf ▸ hν) hO hT.2.2.2.2.2.2
    (by
      rw [List.length_append]
      exact Nat.le_add_right_of_le (heard_reaches hb₁ hT)) ?_)
  rw [msgTxt_mask_slot _ wit J own₀ n ν k m.st.input _ hr
    (free_lt _ _ _ ν (Nat.pos_of_ne_zero ha) (Nat.lt_of_lt_of_le hν hfreeP)), hc]
  rfl

/-- **`CoinsTie` AT THE HEAD, AT THE BORDER 355, AT KIND K1's OWN TEXT.** CONDITIONAL: on h and the
premises named; which they are, and that hS ASSUMES that the book lends from maskStart + 13 on: the
head. -/
theorem k13_coinsTie_of_msgTxt {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    {fx : ℕ} {W' Y' : Type}
    (wit : Local W₀ Rc ProofFile.Inst Tr → W') (J : K1.SendJob W' Y') (own₀ : Y') (n : ℕ)
    {b₁ : ℕ} (hb₁ : b₁ ≤ 355)
    (hO : OwnMsgs Q (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).valid
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front +
        roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).bs b₁)
      (k4IndexNum Zp) fx
      (msgTxt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain wit J own₀
        n))
    (hn : n < J.P.sent.size) (hfit : sendFits J.P J.ride = true)
    (hshape : (msgsOfChain Zp.made.proof.1)[4]? = some (shapeAt J.P n))
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hfreeP : indexFree0 Zp cF ≤ Send.freeMaskEntries (shapeAt J.P n).maskRows
      (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell (shapeAt J.P n).answers)
    (hcov : bookCovers Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain
      ⟨J.P.place, 0⟩ (dueR J.P J.ride) = true)
    (hS : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[355]? =
        some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (⟨J.P.place, 0⟩, K1.maskStart J.P J.ride n + 13, 2 * h.𝔇.P13.lin.kCol + 1))
    (hfree : 13 + (2 * h.𝔇.P13.lin.kCol + 1) ≤ indexFree0 Zp cF) :
    CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights pile h.𝔇.P13
      (k13ReaderAt h) := by
  intro blk hb k s m En hT
  obtain ⟨sh, F⟩ := indexFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (k13_len h) (by decide) (pin_at (k := 355) (by decide) (by decide)) hT
  have hsome : ∀ k' : Coins Bk, (lentCut k'
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain
      ⟨J.P.place, 0⟩ (dueR J.P J.ride)).isSome = true := fun k' => by
    have e := lentCut_isSome k'
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain (Nat.zero_le 1)
      ⟨J.P.place, 0⟩ (dueR J.P J.ride)
    rw [hcov] at e
    exact e
  have ho : OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain
      ⟨J.P.place, 0⟩ (dueR J.P J.ride) (fun k' => Option.get _ (hsome k')) :=
    fun k' => (Option.some_get (hsome k')).symm
  exact coinsTie_of_msgTxt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) 355 weights
    pile h.𝔇.P13 (k13ReaderAt h) h.𝔇.arr h.𝔇.mat13 (fun a v => castWit_mask _ _)
    (msgsOfChain Zp.made.proof.1) LFull 4 13 (indexFree0 Zp cF) (shapeAt J.P n) (1, 0) hshape F.hq
    (k13_state_facts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hshape (by omega))
    wit J own₀ n hO (fun _ _ _ _ hT' => ⟨hT'.2.2.2.2.2.2, heard_reaches hb₁ hT'⟩) hn hfit rfl ha
    hfreeP
    ho hS hfree blk hb k s m En hT

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.heard_reaches
#print axioms ProofFile.Honest.K13.castWit_mask
#print axioms ProofFile.Honest.K13.k13_len
#print axioms ProofFile.Honest.K13.k13_state_facts
#print axioms ProofFile.Honest.K13.k13_taken_at_head
#print axioms ProofFile.Honest.K13.k13_reader_at_take
#print axioms ProofFile.Honest.K13.k13_coinsTie_of_msgTxt
