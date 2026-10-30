-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/MaskTxtG.lean: ONE DEFINITION WITH CODE. No statement.

What is here. `k4MaskTextG`: the text of the member of the feed-forward layers' own rounds
(sub-protocol K4) for its segment's mask row, BY A LOOK-UP THAT CAN FAIL: in the mask row 0, at the
places e + j with j + 1 below the number of slots that the hearing takes (`k4Takes`): member number
j of the list of what the row's parts SPEND (`spentOf`, Law/Script.lean: of what the book of coins,
`ProverCoinCounts`, Honest/Frame.lean, lends a row, the spent runs alone: neither the parts' own coins nor those
that they carry), READ BY `Reading.gl.val`, where the book lends K4's place its row AND the list has
a member of that number; nothing elsewhere. That the reading gives the coin back behind the packing
is `val_coin` (Honest/Law/Rule/CoinBack.lean). The list is asked by a look-up that can fail, not by
one that answers zero: no value stands in for a missing member. `k4MaskTxt` (Law/W/MaskOfOwn.lean),
the name at which the laws speak, is an abbreviation of it. Why it lies here, outside the files of
laws: the laws' imports reach modules under Johnson/Goal/. IT READS THE RUN's COINS BY ONE TERM,
what `lendRow` hands K4's parts of `k.look 0`; it reads no input and no challenge.

Not shown here. NOTHING IS SHOWN HERE: a definition claims nothing. That any prover's message holds
these values is said nowhere here. That the look-up never fails inside the fences, and what it
answers in terms that name no reader: Law/W/MaskTxtGIs.lean. WHERE THE TEXT ANSWERS NOTHING, A
LAYING BY LOTS LAYS ANOTHER LOT's ANSWER OR ZERO (`Script.ofLots`, Honest/Thread/ScriptLots.lean):
so whether it answers has to be a public fact: `k4MaskTextG_isSome`
(Law/W/MaskTxtGPub.lean). THE TEXT STANDS IN NO LOT THAT IS LAID: it is the text of a lemma on the
lot of the message's sender. OF OUR FILES OF LAWS IT IMPORTS Law/Script.lean, which holds the list
of coins, with what that file imports. `spentOf` IS THE ONE OF Law/Script.lean; `spent_same`
(Law/TieIs.lean) ties it to the one of Honest/Law/Rule/Spent.lean, of other writers. It names cells,
weights, tokens and look: they stand in the type of the row's coins. Lean compiles it as a
definition with code; it has been run at nothing. A program's walk from import to import, which
reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 0 modules under Johnson/Goal/ and at 2 under
Johnson/Bridge/: floors. Nothing on soundness, on completeness or on any other property. No property
is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Script
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.First.K4.Returns.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)

/-- **K4's TEXT FOR ITS SEGMENT's MASK ROW, by a look-up that can fail.** e: the first place. X: a
letter of the half's type. This is a definition; it claims nothing. -/
def k4MaskTextG {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (X : Type) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub) (e : ℕ) :
    Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E :=
  fun k _ _ mask row place =>
    if mask = true ∧ row = 0 ∧ e ≤ place ∧ place + 1 < e + k4Takes Qp.P Qp.hp Qp.g then
      (lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0).toOption.bind fun c =>
          ((spentOf _ c)[place - e]?).map Reading.gl.val
    else none

end ProofFile.Honest.K4.Lot
