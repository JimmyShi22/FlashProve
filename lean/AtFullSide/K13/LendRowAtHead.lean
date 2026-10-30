-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/LendRowAtHead.lean: kind K13, the members' batching: UNDER THE LIBRARY's HEAD h
(`P5J.AtMgA`: a hypothesis): AT WHATEVER BOOK THE MAKER `bookWhole` RETURNS AT THE HEAD's OWN THREE
LISTS OF SENDINGS: THE FRAME's `lendRow` RETURNS AT THE KIND's ROW, AT EVERY RUN's COINS: in the
letters in which the kind's tie `CoinsTie` (Johnson/Desc/ProofFile/Honest/K13/ExchangeAtM3.lean)
asks it. One statement with its proof: calls, two small sums and an unfolding; no definition; no
evaluation by Lean's kernel here. PUBLIC DATA ALONE in what is read of the book: its tables and
entries. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE.

Main name: `k13_lendRow_at_head`.

Why. `CoinsTie` is asked where `lendRow` returns at the kind's row: where it errs the tie holds for
nothing. Under h and hW it returns: so of that tie's antecedents this one is met, at every run's
coins.

hW: THAT THE MAKER RETURNS THE BOOK Bk IS A PREMISE. It binds all three lists of sendings to the
head's own (`Zp.made.proof`): the written facts on the whole book stand at the three written lists.
`k13_coinsTie_of_five` (CoinsTieFive.lean of this folder) asks its hW at the first chain's list
alone, the two others free: this statement's hW is an instance of that one.

How. Under h the three lists are the written ones (the library's `sends_in_scope`,
Johnson/Goal/Numbers/MadeInScope.lean) and the head's description is alike to the written
description WP (`planAlike_at_head`, Honest/K14/WrittenAtHead.lean): so the maker returns the same
book at WP (`bookWhole_planAlike`, Honest/BookWholeAlike.lean; `mergesByName_alike`,
Honest/BookAlikeRows.lean). At whatever book it returns there (AtFullSide/K14/RawMineAtK13.lean):
the first table has at the kind's two addresses the count 0 of each sort, or no row (`rawDueAtK13`);
part 0 spends by no entry, part 1 by one, the written one, name and all (`rawSpentEAtK13_part0`,
`_part1`); no entry that carries names a part of the kind's place (`rawCarryAtK13`). The book passes
its own tests (the frame's `bookWhole_word`, Honest/AtPureLaw.lean). Then the law
`k13_lendRow_of_lists` (Honest/K13/LendRowOfFit.lean). The member number 355 stands at the kind's
place (`m3_member_place`, Honest/K13/FromThreadAt.lean), which is `k13Place` at the head's numbers
by unfolding (their chain and piece are 1 and 3); the thread's chain number is 0 by unfolding; kCol
is 18 (`m3_kCol`, GuardsAtM3.lean): 2 · 18 + 1 = 37.

Limits. CONDITIONAL ON h AND hW. That `bookWhole` returns is shown in the side library: at WP:
`bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean); at the head's description and
the written lists: `bookWhole_returns_at_head_ahead` (AtFullSide/K14/WholeAheadAtHead.lean): over
the frame's `segmentCarries` as it lies beneath alone (Honest/BookCarry.lean); at `mergesByName`,
the maker's guess which masked sumchecks are merges; only a build of the side library shows a break
in it, and no independent checker has replayed it; THAT THE BOOK WHICH IT RETURNS IS A THREAD's BOOK
IS NOT SHOWN HERE: that it is the book A.B of whatever the maker `onlineProverFromPublicFiles` returns:
`atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean). The written facts' own limits bind: WP's
values were printed by Lean's evaluator; the sendings are found by their labels, which rest on one
print; evaluations in Lean's kernel beneath, which no independent checker has replayed. WHAT IS
RETURNED IS NOT DESCRIBED: only that something is: THAT `lendRow` RETURNS IS NO WORD THAT THE
STRETCH LENT IS THE ONE THAT THE SENDER LAYS: a book's number is a claim on a sender's text. Of
`CoinsTie`'s other antecedents (the thread stands; the verifier's taking returns) nothing is said.
Nothing on the four tests that `chainSteps` makes before it gives a row its coins. This file's
imports reach Johnson/Goal/. Nothing calls this statement.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K14.RawMineAtK13
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K13.LendRowOfFit
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Goal.Numbers.MadeInScope
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K14 (planAlike_at_head)
open AtFullSide.K14 (rawDueAtK13 rawSpentEAtK13_part0 rawSpentEAtK13_part1 rawCarryAtK13)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- hW (`bookWhole` RETURNS THE BOOK Bk, at the head's own three lists of sendings) IS A PREMISE.
**UNDER THE HEAD: AT THAT BOOK `lendRow` RETURNS AT THE KIND's ROW, AT EVERY RUN's COINS**, in
`CoinsTie`'s own letters. What it returns is bound by that equation alone. CONDITIONAL on h. -/
theorem k13_lendRow_at_head {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[355]? =
        some blk → ∀ k : Coins Bk,
      ∃ c, lendRow Bk
        (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain)
        (k.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.chain) blk.place
        (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X') weights pile h.𝔇.P13).parts 0 = .ok c := by
  intro blk hblk k
  have A := planAlike_at_head h
  have hs : Zp.made.proof = proofSendsFull :=
    VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h)
  have hw := bookWhole_word hW
  rw [hs] at hW
  have hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk := by
    rw [mergesByName_alike A.first, bookWhole_planAlike A]
    exact hW
  have hpl : blk.place = ⟨1, none, 3, .K13⟩ := m3_member_place h hblk
  have hk : k13Place h.𝔇.P13 = ⟨1, none, 3, .K13⟩ := rfl
  rw [hpl, ← hk]
  refine k13_lendRow_of_lists (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) weights pile h.𝔇.P13 hw
    (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) ?_ ?_ ?_ ?_ ?_ k
  · rw [hk, ← hpl]
    exact List.mem_map.2 ⟨blk, List.mem_of_getElem? hblk, rfl⟩
  · intro j hj
    rw [hk]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h0 | rfl
    · obtain rfl : j = 0 := Nat.lt_one_iff.1 h0
      exact (rawDueAtK13 hB).1
    · exact (rawDueAtK13 hB).2
  · rw [hk]
    exact rawSpentEAtK13_part0 hB
  · rw [hk, rawSpentEAtK13_part1 hB, m3_kCol h]
    rfl
  · intro j _
    rw [hk]
    exact rawCarryAtK13 hB j

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_lendRow_at_head
