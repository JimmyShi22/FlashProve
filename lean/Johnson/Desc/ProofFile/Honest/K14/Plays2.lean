-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Plays2.lean: kind K14: «PLAYS» (Honest/Thread/Pays.lean) AT THE
MEMBERS 1 TO 8 OF THE SHARED CHAIN's THREAD, at this kind's letters (Honest/K14/Thread2.lean:
letters2), UNDER Plan2 AND FOUR KINDS OF PREMISE ON THE OPEN LETTERS (listed below): the thread at
which Debts2.lean, Exchange2.lean, Rides2.lean and AcceptedAll.lean of this folder stand. One
theorem: eight_Play (Honest/K14/PaidAll.lean) called there.

  plays2          **Plays at the members 1 to 8**: ONE theorem, under all its premises together

What follows from how the letters are laid: the thread's list of sub-protocols is the shared chain's
own blocksInOrder list, carried: so it has the form FlatOf (flatOf_carried,
Johnson/Desc/K14/Honest/FlatForm.lean).

WHAT STAYS A PREMISE: Plan2 (public) · each of the others on a letter that is not this kind's to lay
(Others): HalvesIn and SendsIn (Honest/K14/AcceptedAll.lean), on O.hs · at the three trees of the
two sendings O.fixed and O.table are the sendings' own (TreesLaid, Honest/K14/SendingsPaid.lean) ·
at every valid input the committed table has a column of the declared width at every position below
its length (O.stored, O.valid). A.atZeta is free; A.atPoint is the number that the two sendings'
jobs read too.
The members 3 and 6 spend of all this only what AtEight says of the thread's list: not to be seen at
plays2's type; so in the proof beneath (Honest/K14/PaidQuiet.lean: six_Play, by none_Plays).

What is not claimed. That these premises can be met at the letters of a proof file's IOP as written
in Lean. (A file that is not part of this tree meets them at a small shape, at another thread. In
this tree Honest/K14/Thread2Full.lean: plays_full calls plays2 at one laid term of the open letters:
Plan2 and the premise on the columns stay premises there.) WHAT is sent: at the kind's own six
members Plays would hold with no half at all: a remark, which no statement bears. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.AcceptedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open Desc.K14 (P14 St)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OnBytes.OracleNotice}
  {layO : OnBytes.TreeLay} {O : Others Bk W₀ Rc X₀ P₁ Wt} {A : Data} {weights : W₀ → Weights}
  {rand : Rc → TableRand}

/-- **Plays at the members 1 to 8 of the shared chain's thread, at this kind's letters**, under
Plan2, HalvesIn, SendsIn, TreesLaid at both sendings (the members 2 and 5), and: at every valid
input the committed table has a column of the declared width at every position below its length. -/
theorem plays2 (hQ : Plan2 Q sentU layO) (Cl : Type) (H : HalvesIn Q O A weights)
    (Hs : SendsIn Q O A weights rand)
    (hU : TreesLaid (letters2 Q sentU O Cl).thread 2 (jobU ⟨Q, A.atPoint⟩) (witOf Q weights rand))
    (hO : TreesLaid (letters2 Q sentU O Cl).thread 5 (jobOmega ⟨Q, A.atPoint⟩)
      (witOf Q weights rand))
    (hcol : ∀ w, O.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.a,
      ∃ u, O.stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc Q.S.fold Q.item).sh.W) :
    Plays (letters2 Q sentU O Cl).thread 1 ∧ Plays (letters2 Q sentU O Cl).thread 2 ∧
      Plays (letters2 Q sentU O Cl).thread 3 ∧ Plays (letters2 Q sentU O Cl).thread 4 ∧
      Plays (letters2 Q sentU O Cl).thread 5 ∧ Plays (letters2 Q sentU O Cl).thread 6 ∧
      Plays (letters2 Q sentU O Cl).thread 7 ∧ Plays (letters2 Q sentU O Cl).thread 8 := by
  obtain ⟨B⟩ := hQ.eight
  exact eight_Play (b0 := 1) (atEight2 B sentU Cl H) Hs hU hO hcol

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.plays2
