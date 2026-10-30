-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotOwner.lean: the proofs of the two statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotOwnerStatement.lean, to the letter. Lemmas; none of
the library's goals. Joinings: no new argument.

How. The first: the first lines of `maskRunIsOwners` (MaskLotOwner.lean of this folder) bring the
row's lending to `lend` at the book's spending entries; `lend_head` (Honest/Law/LendHead.lean): its
second half passes the first entry, its first half then gives a cut of the second entry's owner's;
`endCoins_coin` (Honest/SumLaw/More.lean) reads the run's member number 0, which is the run's head
by `indexLotReads` (LotsRuns.lean of this folder); `cut_eAt` (Honest/K2/Law/Reads.lean). The second:
as `maskLotMeets`: `indexLotAnswers`, `lentIff` (LotsPublic.lean), `indexLotAt` (MsgLots.lean), the
first statement at the entry that the test gives.

It stands over the switches' authors' Honest/K2/Part.lean and Law/Reads.lean, for `cut_eAt` and
`eAt_of_lt`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotOwnerStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLots
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsPublic
import Johnson.Desc.ProofFile.Honest.SumLaw.More
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel
import Johnson.Desc.ProofFile.Honest.Law.LendHead
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Model (Reading)
open ProofFile.Honest.SumLaw (endRun endCoins_coin)
open ProofFile.Honest.K2.Reads (cut_eAt eAt_of_lt)

/-- **The end run's member is the owner's element at the entry's start.** -/
theorem endRunIsOwners : EndRunIsOwners := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights k c e hc he
  have h0 := lendRow_cons_ok (p := headMergeDraw) (ps := [headMergeSum P claims weights]) hc
  have h1 := lendRow_cons_ok (p := headMergeSum P claims weights) (ps := []) h0.2
  have h2 := (lendPart_ok h1.1).2.1
  obtain ⟨e₀, es, hes⟩ : ∃ e₀ es, spentE Bk ⟨pl, 1⟩ = e₀ :: e :: es := by
    cases hL : spentE Bk ⟨pl, 1⟩ with
    | nil =>
      rw [hL] at he
      cases he
    | cons a t =>
      cases t with
      | nil =>
        rw [hL] at he
        cases he
      | cons b t' =>
        rw [hL] at he
        obtain rfl : b = e := Option.some.inj he
        exact ⟨a, t', rfl⟩
  have h2' : lend (k.look ch)
      ((runName maskRowRun ⟨headMergePlace P, 1⟩ "sum", ⟨0, ownRun (headMergeShape P.lay.lk)⟩) ::
        [(runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends", ⟨0, 1⟩)])
      (e₀ :: e :: es) = .ok c.2.1.2.1 := by
    rw [← hes]
    exact h2
  have h3 := (lend_head (lend_head h2').2).1
  have hr : (endRun c.2.1).getD 0 zeroE = (endRun c.2.1).headD zeroE := by
    rw [indexLotReads W₀ Rc Xi Tr X P claims weights c]
    rfl
  have h5 : Reading.gl.val ((endRun c.2.1).getD 0 zeroE) =
      c.2.1.2.1.2.1.e ⟨0, Nat.zero_lt_one⟩ :=
    endCoins_coin (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") ⟨1, 1⟩ c.2.1.2.1.2 0
      Nat.zero_lt_one
  rw [← hr, h5]
  exact cut_eAt h3 (eAt_of_lt c.2.1.2.1.2.1 (i := 0) Nat.zero_lt_one)

/-- **Wherever the lot and the sender's text both answer, they answer alike.** -/
theorem indexLotMeets : IndexLotMeets := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n r p o sf el tx hE htx k w hd hd' mask row place y
    y' h1 h2
  have hs : ((k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n r p).txt k w hd mask
      row place).isSome = true := by
    rw [h1]
    rfl
  rw [indexLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n r p k w hd mask row place,
    Bool.and_eq_true] at hs
  obtain ⟨hm, hrow, hpl⟩ := of_decide_eq_true hs.2
  rw [hm, hrow, hpl] at h1 h2
  obtain ⟨c, hc⟩ := (lentIff Bk W₀ Rc Xi Tr X ch pl P claims weights k).2 hs.1
  have hAt := indexLotAt Bk W₀ Rc Xi Tr X ch pl P claims weights n r p k w hd c hc
  obtain rfl := Option.some.inj (h1.symm.trans hAt)
  obtain ⟨e, he, ho, hst, -⟩ := entryRunIs_gives hE
  have a := endRunIsOwners Bk W₀ Rc Xi Tr X ch pl P claims weights k c e hc he
  rw [ho, hst] at a
  exact Except.ok.inj ((htx k w hd' y' h2).symm.trans a)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.endRunIsOwners
#print axioms ProofFile.Honest.K11.indexLotMeets
