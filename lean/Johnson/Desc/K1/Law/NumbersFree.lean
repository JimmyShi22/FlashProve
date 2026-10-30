-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/NumbersFree.lean: K01_law, ROWS N1 · N2 | N3, THE STATEMENTS ALONE (Props by def; no proof; no sorry), KIND-FREE: what a yes of two of the table of joints' own tests on its numbers (First.Numbers) gives at a block that sends.
  GroupsPart    N1: rowsAtFit N n = true (Johnson/Desc/First/Borders.lean: its first conjunct: eachOnce of the groups' numbers of the segments 0 … n) → no two of these segments have one group.
  BookFitSucc   N2 | N3: bookFit N ps told = true (Johnson/Desc/First/BookFit.lean) → past block k, which tells the oracles os, the two numbers by place grow by os's trees and by their tenants.
                (BookFit.lean's own told_succ_nil | bookAt_step are this at os = []: «(2) At a block that sends: nothing here: the sending kind's own».)
OBJECT. Plain data: N, the list of places, what the blocks tell. No block, no record, no piece.
USER. k01_digits_tied | k01_reads_tied (Johnson/Desc/K1/Law/FiftyAtFull.lean): the premises hinj · trees · msgs. The joins to these binders' letters are typed, and were compiled, under these Props as premises: Johnson/Desc/K1/Law/NumbersUser.lean.
LETTERS. N (at mgAll: D.N) STAYS A LETTER; the tests' yes at the numbers of record is a premise by name. THE MEANT FILLING: (numbersOf (planSeats …)).withTold pl told (P5J/BookTests.lean [not in this library]): there bookFit ran true at both
sizes (evaluated, no theorem). rowsAtFit IS NO CONJUNCT OF planSideOk AND WE KNOW OF NO RUN OF IT AT THAT FILLING.
The proofs stand in Johnson/Desc/K1/Law/NumbersFreeProofs.lean: «theorem groupsPart : GroupsPart» ·
«theorem bookFitSucc : BookFitSucc».
-/
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (Numbers rowsAtFit bookFit)

/-- **ROW N1.** n: the number of segments. -/
def GroupsPart : Prop :=
  ∀ (N : Numbers) (n m m' : Nat), rowsAtFit N n = true → m ≤ n → m' ≤ n →
    N.groupAt m' = N.groupAt m → m' = m

/-- **ROWS N2 | N3.** os: the oracles beneath the roots that block number k sends. -/
def BookFitSucc : Prop :=
  ∀ (N : Numbers) (ps : List Place) (told : List (List Oracle)) (k : Nat) (os : List Oracle),
    bookFit N ps told = true → k < ps.length → told[k]? = some os →
      N.treesAt ps[k + 1]? = N.treesAt ps[k]? + os.length ∧
        N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + (os.map fun o => o.tenants.length).sum

end VerifiableInference.Desc.K1
