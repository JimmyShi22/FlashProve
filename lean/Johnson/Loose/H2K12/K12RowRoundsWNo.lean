-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12RowAlone
import Johnson.AtFull.Rounds.ListAt
/-
Johnson/Loose/H2K12/K12RowRoundsWNo.lean: THE THREE NEGATIVE TESTS OF roundsL_full
(H2K12/K12RowRoundsW.lean), apart in their file, since they are evaluations in Lean's kernel. Each
is a true statement about a bent value: the comparison rejects.
  roundsL_own_no   THE MEMBER BENT: at piLFull SAID TO SEND ITS OWN FIRST MASK (ownMask := true: the
                   bend of own_declares_more, Johnson/Desc/K12/Law/RootsAcross.lean) the declared
                   rounds are NOT the table's list at "F:2"
  roundsL_name_no  THE NAME BENT: at piLFull they are NOT the table's list at "M:3": a name that
                   stands in the table (its row ("M:3", 52); list number 52: 20 rounds): a true
                   other list, not the empty list that, by that file's own head, the table bears
                   at an unknown name. It is refused by its length alone (20 against 33)
  roundsL_turned_no  THE ORDER BENT: they are NOT the table's list at "F:2" read backwards: a list
                   of equal length: so this one is refused at a round's content. (How many rounds
                   the bent member of roundsL_own_no declares is not said here.)
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open H2K.Member (piLFull)

theorem roundsL_own_no :
    decide ((lotB { piLFull with nums := { piLFull.nums with ownMask := true } }).rounds =
      Johnson.AtFull.Rounds.listAt "F:2") = false := by
  decide +kernel

theorem roundsL_name_no :
    decide ((lotB piLFull).rounds = Johnson.AtFull.Rounds.listAt "M:3") = false := by
  decide +kernel

theorem roundsL_turned_no :
    decide ((lotB piLFull).rounds = (Johnson.AtFull.Rounds.listAt "F:2").reverse) = false := by
  decide +kernel

end H2K12

#print axioms H2K12.roundsL_own_no
#print axioms H2K12.roundsL_name_no
#print axioms H2K12.roundsL_turned_no
