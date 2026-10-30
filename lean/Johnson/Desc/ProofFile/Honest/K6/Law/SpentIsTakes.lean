-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/SpentIsTakes.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE ROW SPENDS
41 + 8 lt + 4 lPd COINS: THE LIBRARY'S takesOf; AND WHERE THE BOOK LENDS THE ROW ITS COINS OUT OF
ONE STRETCH, THE STRETCH'S COUNT IS THAT NUMBER.
WHAT IT IS NOT. A COUNT, BY THE TYPES OF THE ROW'S COINS ALONE: no value of a coin, no round, no
verifier's step is read. takesOf is the library's CEILING on the slots that the verifier's ledger
takes behind an accepting decision (Johnson/Desc/Kinds/Law/TakesAt.lean: k6_decide_takes); that the
ledger takes just that number the library has under two more premises (Law/K6Makes.lean:
blockAt_takes_exact): NEITHER IS CALLED HERE: nothing here says that the two counts meet at a run.
THAT ANY BOOK LENDS THE ROW ANYTHING IS NOT SHOWN: cnt_is_takes stands under "lendRow returns at
these coins", under the book's answer on one stretch and under "the stretch lies inside the owner's
count". Nothing on whether the verifier accepts a proof, on soundness, on completeness or on what a
proof hides. No example.
WHY. The premise "the member's slots lie inside the head's plan" (Law/ScriptAtHead.lean: within)
follows, under the library's hypothesis, from "cnt is no more than takesOf" (Law/DebtsLess.lean:
within_of_takes). The frame's authors have: under one stretch and room the book's count cnt is the
number of coins that the row spends (Honest/Law/Rule/TiesLen.lean: rowSpent_length), and that list
is spentOf where lendRow returns (Law/Rule/Spent.lean: spentOf_row). What was left is the length of
our own list.
  own_pointShape          a call in n variables has 2 n + 3 numbers of its own: the library's
                          own_callOf (Johnson/Desc/Kinds/Law/Takes.lean) at our stand-in shape.
  firstRun_length         a sumcheck's first stretch of coins: lead + (2 n + 3): by its type.
  headSpent_length        THE COUNT: 9 + 7 and the four sumchecks' two stretches each.
  spentOf_headRow_length  the same of the frame's spentOf at our row (Law/OutAtThread.lean:
                          headSpent_eq).
  cnt_is_takes            THE TIE: cnt = takesOf p.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.OutAtThread
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesLen
import Johnson.Desc.Kinds.Law.TakesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open VerifiableInference.Desc.Kinds (Head.Par)
open VerifiableInference.Desc.Kinds.Head.Law (callOf own_callOf takesOf)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum)
open SumLaw (SumCoins firstRun endRun)

variable {Bk : ProverCoinCounts} {W X W₀ Rc Tr : Type}

/-- A call of ours in n variables has 2 n + 3 numbers of its own. -/
theorem own_pointShape (lead n e : Nat) : ownSlots (pointShape lead n e).all = 2 * n + 3 := by
  have h : pointShape lead n e = callOf lead (List.replicate n zeroE).toArray e := by
    unfold pointShape callOf
    simp
  rw [h, own_callOf]
  simp

/-- A sumcheck's first stretch of coins, by its type: the count of Honest/K6/HidesOfEight.lean's
first_length, without that one's premise on the job's call at a run. -/
theorem firstRun_length (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) :
    (firstRun c).length = lead + (2 * n + 3) := by
  unfold firstRun
  rw [coinsE_length]
  show ownRun (pointShape lead n e) = lead + (2 * n + 3)
  unfold ownRun
  rw [own_pointShape]
  rfl

/-- **THE ROW SPENDS takesOf p COINS.** -/
theorem headSpent_length {n2 e2 n5 e5 n6 e6 n7 e7 : String} {p : Head.Par} (u1 : Cs ⟨0, 9⟩)
    (c2 : SumCoins n2 e2 (headSquaresJob p)) (u4 : Cs ⟨0, 7⟩)
    (c5 : SumCoins n5 e5 (headProductsJob p)) (c6 : SumCoins n6 e6 (headNormedJob p))
    (c7 : SumCoins n7 e7 (headLogitsJob p)) :
    (headSpent u1 c2 u4 c5 c6 c7).length = takesOf p := by
  have a2 : (firstRun c2).length = 0 + (2 * (headLPd p + headLt p) + 3) :=
    firstRun_length n2 e2 0 (headLPd p + headLt p) 2 _ _ c2
  have b2 : (endRun c2).length = 2 := end_length n2 e2 0 (headLPd p + headLt p) 2 _ _ c2
  have a5 : (firstRun c5).length = 1 + (2 * headLt p + 3) :=
    firstRun_length n5 e5 1 (headLt p) 4 _ _ c5
  have b5 : (endRun c5).length = 4 := end_length n5 e5 1 (headLt p) 4 _ _ c5
  have a6 : (firstRun c6).length = 1 + (2 * headLt p + 3) :=
    firstRun_length n6 e6 1 (headLt p) 2 _ _ c6
  have b6 : (endRun c6).length = 2 := end_length n6 e6 1 (headLt p) 2 _ _ c6
  have a7 : (firstRun c7).length = 1 + (2 * (headLt p + headLPd p) + 3) :=
    firstRun_length n7 e7 1 (headLt p + headLPd p) 2 _ _ c7
  have b7 : (endRun c7).length = 2 := end_length n7 e7 1 (headLt p + headLPd p) 2 _ _ c7
  have l1 : (coinsE u1).length = 9 := coinsE_length u1
  have l4 : (coinsE u4).length = 7 := coinsE_length u4
  have t : takesOf p = 41 + 8 * headLt p + 4 * headLPd p := rfl
  unfold headSpent
  simp only [List.length_append]
  rw [a2, b2, a5, b5, a6, b6, a7, b7, l1, l4, t]
  omega

/-- The same of the frame's list at our row. -/
theorem spentOf_headRow_length (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) :
    (spentOf (headRow wit p at_) c).length = takesOf p := by
  rw [← headSpent_eq wit p at_ c]
  exact headSpent_length _ _ _ _ _ _

/-- **WHERE THE BOOK LENDS THE ROW ITS COINS OUT OF ONE STRETCH THAT LIES INSIDE ITS OWNER'S COUNT,
THE STRETCH'S COUNT IS takesOf.** -/
theorem cnt_is_takes (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) {ch : Nat}
    {o : Addr} {s₀ cnt : Nat} {rows : List (Addr × Due)} (k : Coins Bk)
    {c : RowCoins (headRow (X := X) wit p at_)}
    (hS : oneStretch (rowEntries Bk at_ (headRow (X := X) wit p at_).length 0) = some (o, s₀, cnt))
    (hF : s₀ + cnt ≤ (k.look ch o).1.e)
    (hl : lendRow Bk rows (k.look ch) at_ (headRow wit p at_) 0 = .ok c) : cnt = takesOf p := by
  have e1 := spentOf_row Bk rows (k.look ch) at_ (headRow wit p at_) 0 c hl
  have e2 := rowSpent_length (rowBeginsBy_nil (ch := ch) hS) k hF
  have e3 := spentOf_headRow_length wit p at_ c
  rw [e1, e2] at e3
  omega

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.own_pointShape
#print axioms ProofFile.Honest.K6.firstRun_length
#print axioms ProofFile.Honest.K6.headSpent_length
#print axioms ProofFile.Honest.K6.spentOf_headRow_length
#print axioms ProofFile.Honest.K6.cnt_is_takes
