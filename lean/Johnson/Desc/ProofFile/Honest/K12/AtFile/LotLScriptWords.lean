-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptWords.lean

It states no goal. No property of the protocol is claimed.

THE TIE OF THE WORDS AT THE CLOSING
PROXIMITY TEST OF THE PROOF FILE's FIRST CHAIN (`WordsTied`, K12/SaysOfMet.lean: the premise hw of
says_head_L, ClosingSaysAt.lean), FROM THE WITNESS's TABLE AT THE MEMBERS' SEAT; and that table at
the witness of the joined Script (`joinQ`, Honest/Thread/Join.lean).

  `words_of_table`   at one member, one table and one index: the words that the first chain's reader
      makes of the witness are the words that the plain rows `plainL R P` (ClosingData.lean) make,
      where the witness's table at the member's seat is the message of the rows R. This is
      words_carrying (not beneath this file) with the table as its premise in place of
      the message and the pad entry by entry; the proof follows that law's
  `MemberSitsAtTheCarryingSeat`   THE FORM OF A PREMISE: what a member of the group under test must
      be: it sits at one seat, has the shape of the switch's message 0, of degree 3 and with no mask
      row, and the layout finds it
  `wordsTied_of_table`   `WordsTied` from that form at each member and the table at the seat
  `wordsTied_at_joined`   `WordsTied` AT THE JOINED SCRIPT's WITNESS: the table is paid by
      `join_rows_k2` (K2/Law/JoinTie.lean) at the switch's message 0
  `wordsTied_of_clause`   the same at any Script that meets the two forms `OwnMsgs` and `OwnPads` at
      the switch's texts for its message 0 (`tab_rows_switch`, K2/Law/TabRows.lean)

Hypotheses of `wordsTied_at_joined`. ON THE LISTS OF LOTS, public: hm, hq (the joined lists agree),
hsm, hsp (the switch's lots lie in the other senders' record), at num, fx, tree, tenant with
num 0 = arr tree (tenant 0). ON THE SEAT, public: hcodes and the form at each member. ON THE RUN:
NoWord, the sending has a message, the part is handed c, and ITS ROWS ARE LAID AT heard.take fx: V
is laid at the first fx of the challenges that the witness is given.

Limits. That heard.take fx is the list that the test's job reads is not said here: the plain rows
are `plainL (V 0) P` at this V. That a stand meets the hypotheses is not said here. No list of lots
is laid here. Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `wordsTied_of_clause` and `wordsTied_at_joined` bear this label;
the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- k is the theorems' own binder. The letter c stands under hH : `K2.handed ch p k = some c`, which
  names k, and the letter V under hV : `K2.switchRowsLaid … c w … = .ok V`, which names c, a cut of
  k, and w, whose rc holds the committer's coins: premises of the first kind: by their text, at a
  fixed c (a fixed V) they can hold at some values of the coins and fail at others.
- In `wordsTied_of_clause` the Script Q is a letter under hmsg and hpad (`OwnMsgs`, `OwnPads`,
  Honest/Thread/ScriptLots.lean): premises of the second kind: they read the Script; they are bound
  over all coins and every input that meets Vd, and by themselves pick among no coins. Vd, a letter
  for a predicate, stands under hv : `Vd w`, at the input w, which holds the committer's coins: of
  the first kind as far as Vd reads them; what Vd reads is not fixed here.
- In `wordsTied_at_joined` the Script is the term `joinQ` of the letters bs, front, cells, tok, arr,
  wit, own₀, jobs and O; hm, hq, hsm, hsp and hnum speak of the lots from which it is joined: of the
  second kind: they read the Script's make.
- hcodes, hmem, hw, h0 and hN speak of a statement's codes, of its members' seats, of the sending's
  public shapes and of how many challenges were heard: they name no coin. w, the run's input, is a
  letter under no other premise.
- `words_of_table` and `wordsTied_of_table` name no coin: they bear none.
- What lifts the bar. For c and V the made terms are what `K2.handed` and `K2.switchRowsLaid`
  return. At the closing `K2.lotClosingAt lay segs`, where `switchLotReady` says yes,
  `switch_lot_returns` (LotLOwedLetters.lean) shows, at every k and every w whose instance passes
  `K2.publicOk`, that both return; at another closing none is known to this file. For Vd under hv
  none is named. So the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinTie
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.LotL
open OnBytes (Statement Group GroupLayout TreeBook)
open OnBytes.Slice (begun begun_rowBits begun_shape)
open OnBytes.Means (realRows wordsOn)
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy tabAt seatBy noFirst)
open Johnson.Prover.Link (PS)
open ProofFile.Honest.K2 (NoWord)
open ProofFile.Honest.K2.Law (SwitchCoins tab_rows_switch join_rows_k2)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads MsgsAgree PadsAgree Others joinMl joinPl joinQ)

variable {Cells Tok : Type}

/-- **At one member the words of the witness are the words that the rows make**, where the witness's
table at the member's seat is the rows' message. -/
theorem words_of_table (arr : ℕ → ℕ → ℕ) (St : Statement) (book : TreeBook) (g : ℕ) (G : Group)
    (Ly : GroupLayout) (W : Wit Cells Tok MsgT) (o j t idx : ℕ) (x : OnBytes.Oracle)
    (hseat : seatBy noFirst book o = some (j, t)) (hx : St.oracles[o]? = some x) {m : ℕ}
    (hfind : Ly.find o = some m) (hdeg : x.shape.mainDeg = 3) (hnm : x.shape.maskRows = 0)
    (R : Johnson.Prover.Send.Rows)
    (htab : W.tab St.codes x.shape (arr j t) j t = K1.rowsMsg x.shape R) (P : PS)
    (pt : OnBytes.Part) :
    wordsFirst arr St book W o pt idx =
      ProofFile.Honest.K12.wordsAt (begun St g G) Ly (plainL R P) o pt idx := by
  have hreal : realRows (begun St g G) o pt = realRows St o pt := by
    have e := begun_shape St g G o
    rw [hx, Option.map_some] at e
    obtain ⟨x', h', e'⟩ := Option.map_eq_some_iff.1 e
    unfold realRows
    rw [h', hx]
    show x'.shape.rows pt = x.shape.rows pt
    rw [e']
  have htable : tabAt St.codes arr (seatBy noFirst book) St W o = K1.rowsMsg x.shape R := by
    unfold tabAt
    rw [hseat, hx]
    exact htab
  unfold wordsFirst wordsBy wordsOn ProofFile.Honest.K12.wordsAt
  rw [hfind, begun_rowBits, hreal, htable]
  by_cases hlt : idx % 2 ^ St.rowBits o pt < realRows St o pt
  · cases pt with
    | main =>
      rw [if_pos hlt]
      show K1.rowsMsg x.shape R false _ _ = (if _ then R.mainE _ _ else 0)
      rw [if_pos hlt]
      unfold K1.rowsMsg
      rw [hdeg]
      rfl
    | mask =>
      exfalso
      have : realRows St o .mask = 0 := by
        unfold realRows
        rw [hx]
        exact hnm
      omega
  · rw [if_neg hlt]
    show (0 : OnBytes.Slice.GE) = (if _ then _ else 0)
    rw [if_neg hlt]

/-- **THE FORM OF A PREMISE: what a member of the group under test must be.** p: the switch's place.
tree, tenant: the seat of the switch's message 0, the carrying message. It is a definition. -/
structure MemberSitsAtTheCarryingSeat (p : K2.SwitchPlace) (St : Statement) (book : TreeBook)
    (Ly : GroupLayout) (tree tenant o : ℕ) : Prop where
  /-- the book of trees places the member at that seat -/
  seat : seatBy noFirst book o = some (tree, tenant)
  /-- the statement has the member, with the shape of the switch's message 0, of degree 3 and with
  no mask row -/
  oracle : ∃ x, St.oracles[o]? = some x ∧
    x.shape = ((K2.switchSent p.sizes p.others).getD 0 default).shape ∧ x.shape.mainDeg = 3 ∧
    x.shape.maskRows = 0
  /-- the group's layout finds the member -/
  found : ∃ m, Ly.find o = some m

/-- **`WordsTied` from the table at the seat.** -/
theorem wordsTied_of_table (p : K2.SwitchPlace) (arr : ℕ → ℕ → ℕ) (St : Statement)
    (book : TreeBook) (g : ℕ) (G : Group) (Ly : GroupLayout) (W : Wit Cells Tok MsgT)
    (tree tenant : ℕ) (hcodes : St.codes = p.sizes.codes)
    (hmem : ∀ o ∈ G.members.toList, MemberSitsAtTheCarryingSeat p St book Ly tree tenant o)
    (R : Johnson.Prover.Send.Rows)
    (htab : W.tab p.sizes.codes ((K2.switchSent p.sizes p.others).getD 0 default).shape
      (arr tree tenant) tree tenant =
        K1.rowsMsg ((K2.switchSent p.sizes p.others).getD 0 default).shape R) (P : PS) :
    WordsTied St g G (wordsFirst arr St book W) Ly (plainL R P) := by
  intro o ho pt i _
  obtain ⟨hseat, ⟨x, hx, hs, hdeg, hnm⟩, ⟨m, hfind⟩⟩ := hmem o ho
  refine words_of_table arr St book g G Ly W o tree tenant i x hseat hx hfind hdeg hnm R ?_ P pt
  rw [hcodes, hs]
  exact htab

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **`WordsTied` at a Script that meets the threads' two forms at the switch's texts for its
message 0.** Vd, N: the forms' letters; hv, hN: the input and the challenges heard are among those
of which the forms speak. -/
theorem wordsTied_of_clause (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : ℕ) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (fx tree tenant : ℕ) (arr : ℕ → ℕ → ℕ)
    (hmsg : OwnMsgs Q Vd N (arr tree tenant) fx (K2.switchMsgTxt ch D readers closing p 0))
    (hpad : OwnPads Q Vd tree tenant (fun k _ => K2.switchPadTxt ch p 0 k))
    (St : Statement) (book : TreeBook) (g : ℕ) (G : Group) (Ly : GroupLayout)
    (hcodes : St.codes = p.sizes.codes)
    (hmem : ∀ o ∈ G.members.toList, MemberSitsAtTheCarryingSeat p St book Ly tree tenant o)
    (hw : NoWord (K2.switchSent p.sizes p.others))
    (h0 : 0 < (K2.switchSent p.sizes p.others).size) (k : Coins Bk)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : K2.handed ch p k = some c)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (heard : List Fmt.Drawn) (hN : N ≤ heard.length)
    {V : ℕ → Johnson.Prover.Send.Rows}
    (hV : K2.switchRowsLaid D readers closing p c w (heard.take fx) = .ok V) (P : PS) :
    WordsTied St g G (wordsFirst arr St book (Q.wit k w heard)) Ly (plainL (V 0) P) :=
  wordsTied_of_table p arr St book g G Ly _ tree tenant hcodes hmem (V 0)
    (tab_rows_switch Q Vd N ch D readers closing p fx 0 (arr tree tenant) tree tenant hmsg hpad hw
      h0 k hH w hv heard hN hV) P

variable {Xj X Cl : Type} {bs : List (Block S Cl)} {front : ℕ} {arr : ℕ → ℕ → ℕ}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (ℕ × K1.SendJob (K1.PlaceIn Xj) X)} {O : Others Bk (Local W₀ Rc Xi Tr)}

/-- **`WordsTied` AT THE JOINED SCRIPT's WITNESS.** hnum: the number that the switch's lot of
messages bears for its message 0 is the numbering's at the seat of its lot of pads. -/
theorem wordsTied_at_joined (hm : MsgsAgree (joinMl bs front arr wit own₀ jobs O))
    (hq : PadsAgree (joinPl bs jobs O))
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok) (ch : ℕ)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) (num : ℕ → ℕ) (fx tree : ℕ) (tenant : ℕ → ℕ)
    (hsm : ∀ L ∈ K2.switchMsgLots ch D readers closing p num fx, L ∈ O.ml)
    (hsp : ∀ L ∈ K2.switchPadLots ch p tree tenant, L ∈ O.pl)
    (hnum : num 0 = arr tree (tenant 0))
    (St : Statement) (book : TreeBook) (g : ℕ) (G : Group) (Ly : GroupLayout)
    (hcodes : St.codes = p.sizes.codes)
    (hmem : ∀ o ∈ G.members.toList, MemberSitsAtTheCarryingSeat p St book Ly tree (tenant 0) o)
    (hw : NoWord (K2.switchSent p.sizes p.others))
    (h0 : 0 < (K2.switchSent p.sizes p.others).size) (k : Coins Bk)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : K2.handed ch p k = some c)
    (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) {V : ℕ → Johnson.Prover.Send.Rows}
    (hV : K2.switchRowsLaid D readers closing p c w (heard.take fx) = .ok V) (P : PS) :
    WordsTied St g G
      (wordsFirst arr St book ((joinQ bs front cells tok arr wit own₀ jobs O).wit k w heard)) Ly
      (plainL (V 0) P) := by
  refine wordsTied_of_table p arr St book g G Ly _ tree (tenant 0) hcodes hmem (V 0) ?_ P
  rw [← hnum]
  exact join_rows_k2 hm hq cells tok ch D readers closing p num fx tree tenant hsm hsp hw h0 rfl k
    hH w heard hV

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.words_of_table
#print axioms ProofFile.Honest.K12.LotL.wordsTied_of_table
#print axioms ProofFile.Honest.K12.LotL.wordsTied_of_clause
#print axioms ProofFile.Honest.K12.LotL.wordsTied_at_joined
