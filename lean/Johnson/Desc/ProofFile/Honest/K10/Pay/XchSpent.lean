-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSpent.lean: the closing of a segment (K10): what the run is that the closing's part
spends. Where the book gives the part its coins (`closeCoins`, Honest/K10/Fast/Says.lean), the book has just one entry that
names the part as the spender of a block, under the name of the fold's fresh mask's run and of the count 2 k + 1; and the
run's values are that entry's owner's coins, from the entry's start on.

  `spent_lent`     the one entry, and the cut of its owner's coins that the part is handed
  **`spent_value`**  the values of `spentRun` (Honest/K10/Sim.lean), read in the field, number by number: the owner's coins at
                 the entry's start plus the number

By: `lendRow_spends`, `lend_one` (Honest/K14/SplitCoin.lean); `cut_at` (Honest/K12/CutOfBook.lean).

Limits. Who the entry's owner is, and where the block starts, is the book's matter: nothing is said of it here. That the book
gives the part its coins is a premise.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFresh
import Johnson.Desc.ProofFile.Honest.K10.Fast.Says
import Johnson.Desc.ProofFile.Honest.K14.SplitCoin
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (readE readE_ofTriple toE_ofE)
open VerifiableInference.Desc (Place)

variable {V W X : Type}

/-- The one entry of the book by which the closing's part spends, and what the part is handed by it. -/
theorem spent_lent {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {pl : Place}
    {J : CloseJob W} {cc : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins}
    (hcc : closeCoins (V := V) (X := X) Bk rows look pl J = .ok cc) :
    ∃ e : Ahead, ((Bk.ahead.filter fun e => e.spender == ⟨pl, 0⟩).filter (·.once)) = [e] ∧
      e.name = runName foldMaskRun (closeAddr J.pub.par) "fold" ∧ e.count = ⟨0, 2 * J.pub.par.k + 1⟩ ∧
      (look e.owner).2.cut e.start ⟨0, 2 * J.pub.par.k + 1⟩ =
        some ((handSnd cc).2.1 : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit).1 := by
  unfold closeCoins at hcc
  cases hr : lendRow Bk rows look pl ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0 with
  | error e =>
    rw [hr] at hcc
    cases hcc
  | ok r =>
    rw [hr] at hcc
    obtain rfl : r.1 = cc := Except.ok.inj hcc
    have h1 := K14.lendRow_spends hr
    have h2 : lend look [(runName foldMaskRun (closeAddr J.pub.par) "fold", (⟨0, 2 * J.pub.par.k + 1⟩ : Due))]
        ((Bk.ahead.filter fun e => e.spender == ⟨pl, 0⟩).filter (·.once)) = .ok r.1.2.1 := h1
    exact K14.lend_one h2

/-- **The spent run's values are the entry's owner's coins, from the entry's start on.** -/
theorem spent_value {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {pl : Place}
    {J : CloseJob W} {cc : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins}
    (hcc : closeCoins (V := V) (X := X) Bk rows look pl J = .ok cc) :
    ∃ e : Ahead, ((Bk.ahead.filter fun e => e.spender == ⟨pl, 0⟩).filter (·.once)) = [e] ∧
      e.name = runName foldMaskRun (closeAddr J.pub.par) "fold" ∧ e.count = ⟨0, 2 * J.pub.par.k + 1⟩ ∧
      ∀ i, i < 2 * J.pub.par.k + 1 →
        readE (wordsAll (spentRun J (handSnd cc)) i) = (K12.stretchOf (look e.owner).2).e (e.start.e + i) := by
  obtain ⟨e, h1, h2, h3, h4⟩ := spent_lent hcc
  refine ⟨e, h1, h2, h3, fun i hi => ?_⟩
  have hc := K12.Light.cut_at (look e.owner).2 e.start ⟨0, 2 * J.pub.par.k + 1⟩ _ h4 i hi
  rw [← hc]
  unfold wordsAll
  rw [dif_pos hi]
  show readE (OnBytes.E.ofTriple (OnBytes.Slice.ofE
    (((handSnd cc).2.1 : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit).1.e ⟨i, hi⟩))) = _
  rw [readE_ofTriple, toE_ofE]
  unfold K12.stretchOf
  show _ = if h : i < 2 * J.pub.par.k + 1 then _ else _
  rw [dif_pos hi]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.spent_lent
#print axioms ProofFile.Honest.K10.spent_value
