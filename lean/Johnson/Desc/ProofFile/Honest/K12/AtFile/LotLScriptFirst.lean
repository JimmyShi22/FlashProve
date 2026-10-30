-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptFirst.lean

It states no goal. No property of the protocol is claimed.

AT THE FIRST CHAIN's SCRIPT AS A VALUE
(`firstScriptAt`, AtFullSide/K1/FirstScript.lean): THE WITNESS's TABLE AT THE SEAT
(76, 0) IS THE CARRYING MESSAGE THAT THE CODE SWITCH's FINISH LAYS; and so the tie of the words at
the closing proximity test (`WordsTied`, K12/SaysOfMet.lean). No clause on the Script is left: what
is left speaks of the run (the part is handed its coins, its rows are laid, no message is a word)
and of the seat's facts at the stand.

  `carrying_seat_written`   A CLOSED LINE, at the written lists: there is a finish; its sending has a
      message; the plan's seat for its message 0 is tenant 0 of tree 76. With a control that says no
  `finish_is_written`   under the head, where the maker returns, the finish is the written one
  `carrying_seat_first`   so, at the finish pl: the sending has a message, and `switchSeatIn` finds
      a seat q with q.j = 76 and q.t = 0
  `carrying_table_first`   THE TABLE's EQUATION at the Script's witness, at the number
      `P5J.At.arr A.Z 76 0` and the seat (76, 0)
  `wordsTied_first`   `WordsTied` at that witness and the rows `plainL (V 0) P`

By: `share_rows_fit` (K2/JoinShare.lean) · `joinFit_first`, `switch_in_first`
(AtFullSide/K1/FirstScript.lean) · `places_head` (AtFullSide/K12/FitsAtHeadL.lean) ·
`pseatsAll_at_head` (K2/Law/SwitchNumsAtHead.lean) · `atPure_at_laid_ground`
(Honest/AtHeadGround.lean).

Hypotheses. h: the head. hA: the maker returns A at the base prover's filling. hf: pl is the finish.
hw: NoWord. hH: the frame hands the finish's part c at the chain's number 0. hV: ITS ROWS ARE LAID AT
THE FIRST 0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder pl.place) OF THE CHALLENGES THAT THE WITNESS IS
GIVEN, at the share's own data, readers and closing (`widerRows`, `readersB`, `closingB`).
`wordsTied_first`: also hcodes and `MemberSitsAtTheCarryingSeat` at (76, 0) at each member.

Limits. The full size and the format's second hash function alone. That hH and hV hold at a stand, and that
the list of challenges in hV is the one that the test's job reads, is not said here. Where the part
is handed nothing or its rows refuse, these laws say nothing. That the head can be met together with
hA, hH and hV is not said. Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `carrying_table_first` and `wordsTied_first` bear this label; the
rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hw, hcodes and hmem speak of the finish, of the sending's public shapes, of a statement's
  codes and of its members' seats: they name no coin.
- k is the theorems' own binder. The letter c stands under hH : `K2.handed 0 pl k = some c`, which
  names k, and the letter V under hV : `K2.switchRowsLaid … c w … = .ok V`, which names c, a cut of
  k, and w, whose rc holds the committer's coins: premises of the first kind: by their text, at a
  fixed c (a fixed V) they can hold at some values of the coins and fail at others.
- w, the run's input, is a letter under no other premise. The Script is no letter: it is the term
  `firstScriptAt`.
- The other theorems of this file name no coin: they bear none.
- What lifts the bar. For c and V the made terms are what `K2.handed` and `K2.switchRowsLaid`
  return. At the closing place, at the lot's own closing, `switch_lot_returns_at_closing_place`
  (LotLOwedAtHead.lean), from h, hB, hG, hf and hok (the public files, the book, the ground, the
  finish, the closing's public test: no coin), shows, at every k, every list of challenges and every
  w whose instance passes `K2.publicOk`, that both return; `finishIsHanded_at_base`
  (LotLAcceptedFields.lean) shows the first at every k. No other letter is tied here: whoever lifts
  the bar calls these beside the call, and names `K2.publicOk` at the input's instance.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptWords
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptNumber
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.LotL
open OnBytes (Statement Group GroupLayout TreeBook)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (wordsFirst)
open Johnson.Prover.Link (PS)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB closingB cellsB tokB noTree joinFit_first
  switch_in_first)
open ProofFile.Honest.K2 (SwitchPlace switchSeatIn switchNum)
open ProofFile.Honest.K2 (NoWord)
open ProofFile.Honest.K2.Law (SwitchCoins share_rows_fit pseatsAll_at_head)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL finishAt finishW places_head)
open P5J (AtMgA TS)

/-- What the closed line asks of a place: its sending has a message, and the written plan's seat for
its message 0 is tenant t of tree j. A public test. -/
def carryingSeatIs (j t : Nat) (pl : SwitchPlace) : Bool :=
  decide (0 < (K2.switchSent pl.sizes pl.others).size) &&
    (switchSeatIn P5T.seatsAllFull pl.link 0).any fun q => q.j == j && q.t == t

set_option maxRecDepth 1000000 in
/-- **A CLOSED LINE**: at the written lists there is a finish, its sending has a message, and the
seat of its message 0 is tenant 0 of tree 76. The control: asked for tenant 1 of that tree (the fresh
table's seat) the test says no. -/
theorem carrying_seat_written :
    finishW.any (carryingSeatIs 76 0) = true ∧ finishW.any (carryingSeatIs 76 1) = false := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, where the maker returns, the finish is the written one.** -/
theorem finish_is_written (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    finishAt A.Z A.G = finishW := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  unfold finishAt finishW
  rw [places_head h.toAtMg (G := A.G) (by rw [eG]; exact O.blank)]

/-- **At the finish: the sending has a message, and the plan's seat for its message 0 is tenant 0 of
tree 76.** -/
theorem carrying_seat_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    0 < (K2.switchSent pl.sizes pl.others).size ∧
      ∃ q, switchSeatIn (P5J.At.pseatsAll A.Z) pl.link 0 = some q ∧ q.j = 76 ∧ q.t = 0 := by
  have c := carrying_seat_written.1
  rw [← finish_is_written h hA, hf, Option.any_some] at c
  unfold carryingSeatIs at c
  rw [Bool.and_eq_true, decide_eq_true_eq, ← pseatsAll_at_head h.toAtMg] at c
  refine ⟨c.1, ?_⟩
  cases hs : switchSeatIn (P5J.At.pseatsAll A.Z) pl.link 0 with
  | none =>
    have c2 := c.2
    rw [hs] at c2
    cases c2
  | some q =>
    have c2 := c.2
    rw [hs, Option.any_some, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at c2
    exact ⟨q, rfl, c2.1, c2.2⟩

/-- **THE TABLE's EQUATION AT THE FIRST CHAIN's SCRIPT.** The witness's table at the seat (76, 0),
read at the finish's codes and its message 0's shape, is the message of the rows that the finish
lays for its message 0. -/
theorem carrying_table_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hw : NoWord (K2.switchSent pl.sizes pl.others)) (k : Coins A.B)
    {c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries} (hH : K2.handed 0 pl k = some c)
    (w : LocB W₀) (heard : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : K2.switchRowsLaid (widerRows S A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl c w
      (heard.take (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder pl.place))) = .ok V) :
    ((firstScriptAt I S Op A cF).wit k w heard).tab pl.sizes.codes
        ((K2.switchSent pl.sizes pl.others).getD 0 default).shape (P5J.At.arr A.Z 76 0) 76 0 =
      K1.rowsMsg ((K2.switchSent pl.sizes pl.others).getD 0 default).shape (V 0) := by
  obtain ⟨h0, q, hq, ej, et⟩ := carrying_seat_first h hA hf
  have e := share_rows_fit 0 (K2.coreSender K2.freshTable) (widerRows S A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) _ _ _ _ _ _ noTree (joinFit_first h hA)
    (switch_in_first (I := I) (S := S) (A := A) (cF := cF)) (cellsB I A.Z) tokB
    (List.mem_of_find?_eq_some hf) hw h0 rfl k hH w heard hV
  have e1 : switchNum A.Z pl 0 = P5J.At.arr A.Z 76 0 := by
    rw [carrying_number_at_seat A.Z pl hq, ej, et]
  have e2 : ((switchSeatIn (P5J.At.pseatsAll A.Z) pl.link 0).map (·.j)).getD 0 = 76 := by
    rw [hq]
    exact ej
  have e3 : ((switchSeatIn (P5J.At.pseatsAll A.Z) pl.link 0).map (·.t)).getD 0 = 0 := by
    rw [hq]
    exact et
  rw [e1, e2, e3] at e
  exact e

/-- **`WordsTied` AT THE FIRST CHAIN's SCRIPT.** -/
theorem wordsTied_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (St : Statement) (book : TreeBook) (g : Nat) (G : Group) (Ly : GroupLayout)
    (hcodes : St.codes = pl.sizes.codes)
    (hmem : ∀ o ∈ G.members.toList, MemberSitsAtTheCarryingSeat pl St book Ly 76 0 o)
    (hw : NoWord (K2.switchSent pl.sizes pl.others)) (k : Coins A.B)
    {c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries} (hH : K2.handed 0 pl k = some c)
    (w : LocB W₀) (heard : List Fmt.Drawn) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : K2.switchRowsLaid (widerRows S A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl c w
      (heard.take (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder pl.place))) = .ok V) (P : PS) :
    WordsTied St g G
      (wordsFirst (P5J.At.arr A.Z) St book ((firstScriptAt I S Op A cF).wit k w heard)) Ly
      (plainL (V 0) P) :=
  wordsTied_of_table pl (P5J.At.arr A.Z) St book g G Ly _ 76 0 hcodes hmem (V 0)
    (carrying_table_first h hA hf hw k hH w heard hV) P

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.carrying_seat_written
#print axioms ProofFile.Honest.K12.LotL.finish_is_written
#print axioms ProofFile.Honest.K12.LotL.carrying_seat_first
#print axioms ProofFile.Honest.K12.LotL.carrying_table_first
#print axioms ProofFile.Honest.K12.LotL.wordsTied_first
