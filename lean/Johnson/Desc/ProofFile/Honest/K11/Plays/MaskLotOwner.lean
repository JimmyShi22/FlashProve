-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskLotOwner.lean: the proofs of the two statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/MaskLotOwnerStatement.lean, to the letter. Lemmas; none of
the library's goals. Joinings: no new argument.

How. The first: `lendRow_cons_ok` (Honest/Law/Rule/RowModel.lean) twice brings the row's lending to
the part number 1; `lendPart_ok` (Honest/Law/Rule/PartCell.lean) to `lend` at the book's spending
entries; `lend_head` (Honest/Law/LendHead.lean) to a cut of the owner's; `firstRun_coin`
(Honest/SumLaw/More.lean) reads the run's member; `cut_eAt` (Honest/K2/Law/Reads.lean) carries it to
the owner's number. The second: the lot answers inside its fence alone, and only where the row is
lent (`maskLotAnswers`, `lentIff`, LotsPublic.lean of this folder); there `maskLotAt` (MsgLots.lean)
says what; the first statement at the entry that the test gives; both answers are then the return of
one term.

It stands over the switches' authors' Honest/K2/Part.lean and Law/Reads.lean, for `cut_eAt` and
`eAt_of_lt`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskLotOwnerStatement
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
open ProofFile.Honest.SumLaw (firstRun firstRun_coin firstRun_count)
open ProofFile.Honest.K2.Reads (cut_eAt eAt_of_lt)

/-- **The first run's members are the owner's elements, from the entry's start on.** -/
theorem maskRunIsOwners : MaskRunIsOwners := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights k c e hc he i hi
  have h0 := lendRow_cons_ok (p := headMergeDraw) (ps := [headMergeSum P claims weights]) hc
  have h1 := lendRow_cons_ok (p := headMergeSum P claims weights) (ps := []) h0.2
  have h2 := (lendPart_ok h1.1).2.1
  obtain ⟨es, hes⟩ : ∃ es, spentE Bk ⟨pl, 1⟩ = e :: es := by
    cases hL : spentE Bk ⟨pl, 1⟩ with
    | nil =>
      rw [hL] at he
      cases he
    | cons a t =>
      rw [hL] at he
      obtain rfl : a = e := Option.some.inj he
      exact ⟨t, rfl⟩
  have h2' : lend (k.look ch)
      ((runName maskRowRun ⟨headMergePlace P, 1⟩ "sum", ⟨0, ownRun (headMergeShape P.lay.lk)⟩) ::
        endRuns (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeShape P.lay.lk).ends)
      (e :: es) = .ok c.2.1.2.1 := by
    rw [← hes]
    exact h2
  have h3 := (lend_head h2').1
  have hi' : i < ownRun (headMergeShape P.lay.lk) := by
    have a := firstRunFull W₀ Rc Xi Tr X P claims weights c
    have b : (firstRun c.2.1).length = ownRun (headMergeShape P.lay.lk) := firstRun_count c.2.1
    omega
  rw [firstRun_coin c.2.1 i hi']
  exact cut_eAt h3 (eAt_of_lt _ hi')

/-- **Wherever the lot and the sender's text both answer, they answer alike.** -/
theorem maskLotMeets : MaskLotMeets := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ o sf base L tx hE hL htx k w hd hd' mask row
    place y y' h1 h2
  have hs : ((k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask
      row place).isSome = true := by
    rw [h1]
    rfl
  rw [maskLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k w hd mask row place,
    Bool.and_eq_true] at hs
  obtain ⟨rfl, rfl, hp1, hp2⟩ := of_decide_eq_true hs.2
  obtain ⟨c, hc⟩ := (lentIff Bk W₀ Rc Xi Tr X ch pl P claims weights k).2 hs.1
  have hAt := maskLotAt Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k w hd c hc (place - ν₀)
    (by omega)
  rw [Nat.add_sub_cancel' hp1] at hAt
  obtain rfl := Option.some.inj (h1.symm.trans hAt)
  obtain ⟨e, he, ho, hst, -⟩ := entryRunIs_gives hE
  have a := maskRunIsOwners Bk W₀ Rc Xi Tr X ch pl P claims weights k c e hc he (place - ν₀)
    (by omega)
  rw [ho, hst] at a
  have b := htx k w hd' place y' (by omega) h2
  have en : base + ν₀ + (place - ν₀) = base + place := by omega
  have a' : (k.look ch o).2.eAt (base + place) =
      .ok (Reading.gl.val ((firstRun c.2.1).getD (place - ν₀) zeroE)) := by
    rw [← en]
    exact a
  exact Except.ok.inj (b.symm.trans a')

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.maskRunIsOwners
#print axioms ProofFile.Honest.K11.maskLotMeets
