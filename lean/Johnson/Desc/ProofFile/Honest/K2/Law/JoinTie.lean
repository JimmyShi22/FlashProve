-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/JoinTie.lean: the kind "the code switch" (K2): THE KIND's TIES
AT THE JOINED SCRIPT: at `joinQ` (Honest/Thread/Join.lean, of other authors), the one Script that is
laid of all senders' lots. Where one place's lots lie in the other senders' share of the list
(`Others`) and the joined lists agree (`MsgsAgree`, `PadsAgree`), the joined Script meets the
threads' forms `OwnMsgs` and `OwnPads` at this kind's texts. Where that record holds the switch's
own table at the member's number, a thread that has the joined Script's tables meets `OwnTrees`:
this end asks neither the lots nor that they agree. After the pattern of `join_tie_k1` and
`join_trees_k1` there, with one turn: those take the yes of the test `agreeB`; these take the two
forms that the yes gives (`agree_of_test`, there), so they can also be called where the forms are
shown without an evaluation. Four statements with their proofs: calls; no definition.

  `join_tie_k2`     a message of which the switch is the first sender: `OwnMsgs` at `switchMsgTxt`;
                    every message of the sending: `OwnPads` at `switchPadTxt`
  `join_off_k2`     the first half at the text off the pad, `switchMsgOff`
  `join_rows_k2`    so the joined Script's witness holds, at such a message, the rows that the
                    switch lays
  `join_trees_k2`   `OwnTrees` at `switchTableAt`, at a member's number that is no job's of the
                    shared sending

By: `ownMsgs_of_lots`, `ownPads_of_lots`, `hin_switchMsgs_of_agree`, `hin_switchPads_of_agree`,
`tab_rows_of_lots` (Honest/K2/Law/LotsLaid.lean) · `ownMsgs_off` (Honest/K2/Law/TabRowsOff.lean) ·
`ofLots_ownTrees` (Honest/Thread/ScriptLots.lean) · `k1TreeLots_rest`
(Honest/K1/Law/TreeLotsAtAll.lean).

Limits. NO LIST IS LAID HERE: the jobs, the book and the record `Others` are letters; that a place's
lots lie in the record (hsm, hsp, htl) and that the joined lists agree (hm, hq) are premises, shown
here of no list. AT A KEPT COPY NOTHING IS SAID ON THE MESSAGE: no lot of messages is laid there;
its tie follows from its first sender's by another law (`ownMsgs_copy_at_pair`,
Honest/K2/Law/OwnMsgsAtPair.lean, not imported), under premises of its own. num, fx, tree and tenant
are letters: that num n is the plan's number at the seat (tree, tenant n) is not said. A text that
answers nothing meets the forms idly: where the frame hands the part nothing, or the closing
refuses, the first three ends say nothing. Where the texts answer is told by `padTxt_isSome` and, at
the lot's own closing `lotClosingAt` under `closingOk`, by `msgTxt_isSome`
(Honest/K2/Law/LotsAnswer.lean, not imported); here closing is a letter. THE FOURTH END IS NOT IDLE
THERE: at each tree that the member declares (it says nothing at a member that declares none)
`OwnTrees` is an equation at all coins, inputs and challenges; on each of the three roads that
`switchTableAt`'s docstring names (Honest/K2/Seated.lean) that table is the one without a word
(`noTable`), and the end says that the thread's table is that. Nothing is asked of the book here:
whoever quotes these laws at a book names beside them that the book lends the part its own cut and
each stretch that it carries. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Join
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsLaid
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff
import Johnson.Desc.ProofFile.Honest.K2.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot OwnMsgs OwnPads OwnTrees MsgsAgree
  PadsAgree Others joinMl joinPl joinTl joinQ ofLots_ownTrees)

variable {W₀ Rc Xi Tr Xj X Cl Cells Tok : Type} {Bk : ProverCoinCounts} {bs : List (Block S Cl)} {front : Nat}
  {arr : Nat → Nat → Nat} {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {O : Others Bk (Local W₀ Rc Xi Tr)}

/-- **THE TIE AT THE JOINED SCRIPT**, at one place whose lots lie in the record. closing is a
letter: whether `switchMsgTxt` answers is a theorem on public data at the lot's own closing
`lotClosingAt` under `closingOk` alone (`msgTxt_isSome`, `msgTxt_public`,
Honest/K2/Law/LotsAnswer.lean). At a book whose count at the part's address does not cover the
part's due both halves hold for nothing; the first half also at a book that does not lend the part
just its due and each stretch that it carries. It is never quoted as if it spoke there: that the
frame hands the part its coins (`handed`) is neither asked nor paid here: whoever quotes this law at
a book names that at that book beside it. -/
theorem join_tie_k2 (hm : MsgsAgree (joinMl bs front arr wit own₀ jobs O))
    (hq : PadsAgree (joinPl bs jobs O))
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (num : Nat → Nat) (fx tree : Nat) (tenant : Nat → Nat)
    (hsm : ∀ L ∈ switchMsgLots ch D readers closing p num fx, L ∈ O.ml)
    (hsp : ∀ L ∈ switchPadLots ch p tree tenant, L ∈ O.pl) :
    (∀ n, n < (switchSent p.sizes p.others).size → firstSender p n = true →
      OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N (num n) fx
        (switchMsgTxt ch D readers closing p n)) ∧
    ∀ n, n < (switchSent p.sizes p.others).size →
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd tree (tenant n)
        (fun k _ => switchPadTxt ch p n k) :=
  ⟨fun n hn h1 =>
      ownMsgs_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
        (joinMl bs front arr wit own₀ jobs O) ch D readers closing p num fx n
        (hin_switchMsgs_of_agree (joinMl bs front arr wit own₀ jobs O) ch D readers closing p num
          fx (fun L hL => List.mem_append.2 (Or.inr (hsm L hL))) hm hn h1) Vd N,
    fun n hn =>
      ownPads_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
        (joinMl bs front arr wit own₀ jobs O) ch p tree tenant n
        (hin_switchPads_of_agree (joinPl bs jobs O) ch p tree tenant
          (fun L hL => List.mem_append.2 (Or.inr (hsp L hL))) hq hn) Vd⟩

/-- The first half at the text off the pad. The pads' lots are not asked. closing is a letter:
whether `switchMsgTxt` answers is a theorem on public data at the lot's own closing `lotClosingAt`
under `closingOk` alone (`msgTxt_isSome`, `msgTxt_public`, Honest/K2/Law/LotsAnswer.lean). At a book
whose count at the part's address does not cover the part's due, or that does not lend it a stretch
that it carries, this law holds for nothing, and it is never quoted as if it spoke there: that the
frame hands the part its coins (`handed`) is neither asked nor paid here: whoever quotes this law at
a book names that at that book beside it. -/
theorem join_off_k2 (hm : MsgsAgree (joinMl bs front arr wit own₀ jobs O))
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace)
    (num : Nat → Nat) (fx : Nat)
    (hsm : ∀ L ∈ switchMsgLots ch D readers closing p num fx, L ∈ O.ml) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) :
    OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N (num n) fx
      (switchMsgOff ch D readers closing p n) :=
  ownMsgs_off _ Vd N ch D readers closing p fx n (num n)
    (ownMsgs_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
      (joinMl bs front arr wit own₀ jobs O) ch D readers closing p num fx n
      (hin_switchMsgs_of_agree (joinMl bs front arr wit own₀ jobs O) ch D readers closing p num
        fx (fun L hL => List.mem_append.2 (Or.inr (hsm L hL))) hm hn h1) Vd N)

/-- **THE JOINED SCRIPT's WITNESS HOLDS THE ROWS THAT THE SWITCH LAYS**, at a message of which the
switch is the first sender, where no message of the sending is a word (hw), the part is handed its
coins (hH) and its rows are laid (hV). closing is a letter: whether the rows are laid is a theorem
on public data at `lotClosingAt` under `closingOk` alone (`rows_isSome`,
Honest/K2/Law/LotsAnswer.lean). At a book that does not hand the part its coins, or where the rows
are not laid, this law holds for nothing, and it is never quoted as if it spoke there. -/
theorem join_rows_k2 (hm : MsgsAgree (joinMl bs front arr wit own₀ jobs O))
    (hq : PadsAgree (joinPl bs jobs O))
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok) (ch : Nat)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (num : Nat → Nat) (fx tree : Nat) (tenant : Nat → Nat)
    (hsm : ∀ L ∈ switchMsgLots ch D readers closing p num fx, L ∈ O.ml)
    (hsp : ∀ L ∈ switchPadLots ch p tree tenant, L ∈ O.pl)
    (hw : NoWord (switchSent p.sizes p.others)) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) (h1 : firstSender p n = true) (k : Coins Bk)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : handed ch p k = some c)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w (hd.take fx) = .ok V) :
    ((joinQ bs front cells tok arr wit own₀ jobs O).wit k w hd).tab p.sizes.codes
        ((switchSent p.sizes p.others).getD n default).shape (num n) tree (tenant n) =
      K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) :=
  tab_rows_of_lots bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) ch D readers closing p num fx tree tenant
    (fun L hL => List.mem_append.2 (Or.inr (hsm L hL))) hm
    (fun L hL => List.mem_append.2 (Or.inr (hsp L hL))) hq hw hn h1 k hH w hd hV

/-- **THE TREES AT THE JOINED SCRIPT**, at a thread whose four fields are the joined Script's, at a
member's number b that is no job's of the shared sending and at which the record holds the switch's
own table. closing is a letter here too; what is shown on public data stands at `lotClosingAt` under
`closingOk` alone (Honest/K2/Law/LotsAnswer.lean). THREE ROADS LEAD TO THE TABLE WITHOUT A WORD
(`noTable`): the frame hands the part nothing; the first move refuses, so no rows are laid; the
sending has no table number j. Nothing is asked of the book here, and on each of the three the end
is not empty: it speaks of that table. -/
theorem join_trees_k2 {V X' Pb : Type} (cells : Local W₀ Rc Xi Tr → Cells)
    (tok : Local W₀ Rc Xi Tr → Tok) (T : Thread Bk S Cl V (Local W₀ Rc Xi Tr) X' Pb)
    (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) {b : Nat}
    (hb : b ∉ jobs.map (·.1)) {blk : Block S Cl} (hblk : bs[b]? = some blk) (ch : Nat)
    (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace)
    (htl : O.tl b =
      ⟨fun j k w h => (p.place, switchTableAt Bk ch Sd D readers closing p k w h j), fun _ => 0⟩) :
    OwnTrees T b (blk.oracles.flatMap id).length
      (fun j k w h => (p.place, switchTableAt Bk ch Sd D readers closing p k w h j))
      (fun _ => 0) := by
  have e := ofLots_ownTrees bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) T hbs hfr htab hfix hblk
  have e2 : joinTl wit own₀ jobs O b = O.tl b := K1.k1TreeLots_rest wit own₀ O.tl hb
  rw [e2, htl] at e
  exact e

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.join_tie_k2
#print axioms ProofFile.Honest.K2.Law.join_off_k2
#print axioms ProofFile.Honest.K2.Law.join_rows_k2
#print axioms ProofFile.Honest.K2.Law.join_trees_k2
