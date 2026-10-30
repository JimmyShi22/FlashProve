-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/IndexTxtG.lean: one definition with code. NOTHING IS SHOWN
HERE.

What is here. THE TEXT OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4) FOR
ITS ONE ENTRY OF THE INDEX MASKS' MESSAGE. It stands in a file of its own, over no file on the
threads' Script, so that the law on the tie (Law/W/IndexOfOwn.lean) can speak at it; the lot that
is made of it is Lot/IndexLotG.lean.

  `k4IndexTextG`   the text: at the mask part, the row and the place named: the last member of the
      list `spentOf` (Law/Script.lean) of the row that the book lends the member's place, read back;
      «none» at every other entry, and everywhere where the book lends no row. THE LIST IS READ WITH
      [·]?: the text names no value that would stand in for a missing member. «MEMBER» NAMES A
      MEMBER OF THAT LIST AND NO MORE: whose coin it is, is not said here.

Not shown here. All: a definition claims nothing. That any prover's message holds this value is
said nowhere. THE TEXT STANDS IN NO LOT THAT IS LAID: it is the text of a lemma on the lot of the
message's sender. The text reads of a run's coins what `lendRow` hands the member's own row of
parts in the first chain, and of that the runs that these parts spend: members of OWNERS' coins, at
the addresses that the book's entries name. It reads neither the input nor the challenges; cells,
weights, tokens and look stand in the type of the row's coins. row AND place ARE LETTERS HERE,
AND SO IS Qp: NOTHING IN THE TYPE TIES THEM TO ONE GROUP: the lot (Lot/IndexLotG.lean) makes all
three of the group's number. Whether the text answers is a function of public data, and what it
answers: Law/W/IndexLotGIs.lean. Whether two members of such lists are one coin hangs on the book.
Lean compiles it as a definition with code; it has been run at nothing. HOW LIGHT: A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 2 under Johnson/Bridge/: so
these counts are lower bounds; it met no module under Johnson/Goal/,
ThirdParty/ or Johnson/D/ and none that begins Cb.Bridge. Nothing on soundness, on completeness or
on any other property.

No property is claimed.
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

/-- **THE TEXT: THE LIST IS READ WITH [·]?.** Qp: the member's public data; row, place: the entry.
This is a definition; it claims nothing. -/
def k4IndexTextG {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type} (X : Type) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub) (row place : ℕ) :
    Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E :=
  fun k _ _ mask r p =>
    if mask = true ∧ r = row ∧ p = place then
      (lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0).toOption.bind fun c =>
          ((spentOf _ c)[k4Takes Qp.P Qp.hp Qp.g - 1]?).map Reading.gl.val
    else none

end ProofFile.Honest.K4.Lot
