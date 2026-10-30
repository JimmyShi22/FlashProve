-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CoinAtLendings.lean

OF WHAT KIND IT IS. A tie between what one part is handed of a run's values and what another part is
handed of them.

The field coin of `LeftAt` (OnFreeTAtHeadULeft.lean), from two lendings of the frame's and a premise
on the book's entries. One theorem, general in the plan, the book and the readers.

  `coin_at_lendings`: the statement.

By what. The shared rounds' authors' `one_coin` (Honest/K14/SplitCoin.lean: the coin lent to "SPLIT"
is the owner's own coin of a given number) and `coin_there` (Honest/K14/PartsCoin.lean). The left
side's index: the second half of the proof of their `spOneCoin_of_book` (Honest/K14/Holds2.lean),
typed anew at `heldAt` (Sim/ShownAtRun.lean).

Limits.
- he (every entry that the part at "SPLIT" spends once names the second sender as its owner and
  starts at o_sp's first coin) and hs are premises on public data; that a book has such entries is
  not shown here (AtFullSide/K12/CutsAtHead.lean has it at the maker's book, under the head).
- That the frame lends is a premise, twice.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun
import Johnson.Desc.ProofFile.Honest.K14.SplitCoin
import Johnson.Desc.ProofFile.Honest.K14.PartsCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E zeroE TableKey ceilLog2)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Place)
open Desc.K14 (P14)
open Desc.K14.Honest (kappaOf)
open ProofFile.Honest (ProverCoinCounts Addr Due Cs Common Part RowCoins lendRow coinsE Weights)
open ProofFile.Honest.K14 (Ask jobOmega offsetOf takesOf sendPlace liftSend sendingPart Data liftK14
  splitPart msgCoins one_coin coin_there)

/-- **`LeftAt`'s field coin, from the book's entries.** General in the plan, the book and the
readers. Where the frame has lent the part at "SPLIT" its coins cS at a place a, and the second
sending's part its coins cO; every entry of the book that the part at "SPLIT" spends once names that
sender as its owner and starts at o_sp's first coin (he); that coin is among those that the sender
takes (hs); o_sp has no main row and has a mask row: the entry number 0 of o_sp's mask row, as
`heldAt` holds it at cO's coins, is the coin that "SPLIT" spends, read.
OF WHAT KIND IT IS: a tie between what one part is handed of a run's values and what another part is
handed of them. -/
theorem coin_at_lendings {W₀ Rc X₀ : Type} (Q : P14) (hno : Q.par.S.sharedSplit.mainRows = 0)
    (hone : Q.par.S.sharedSplit.maskRows ≠ 0) (A : Data) (wts : W₀ → Weights)
    (wit : Common W₀ Rc TableKey → Ask) {Bk : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Place}
    {cS : RowCoins [(liftK14 A wts (splitPart A) : Part Empty (Common W₀ Rc TableKey) X₀)]}
    (lS : lendRow Bk rows look a
      [(liftK14 A wts (splitPart A) : Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cS)
    {cO : RowCoins [(liftSend wit (sendingPart (jobOmega ⟨Q, 0⟩)) :
      Part Empty (Common W₀ Rc TableKey) X₀)]}
    (lO : lendRow Bk rows look (sendPlace 5) [(liftSend wit (sendingPart (jobOmega ⟨Q, 0⟩)) :
      Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO)
    (he : ∀ e ∈ Bk.ahead, e.spender = ⟨a, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q,
        0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1⟩)
    (hs : offsetOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1 <
      (takesOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort).e)
    (ask : Ask) (csU : Array E) :
    kappaOf (heldAt Q ask csU (coinsE cO.1.1).toArray).cSp Q.par.S.sharedSplit.maskRows 0 =
      rdE.val ((coinsE cS.1.2.1.1).headD zeroE) := by
  have h1 := one_coin A wts lS lO _ he hs
  have hidx : Q.par.S.sharedSplit.mainRows *
        (Q.codes.base.getD Q.par.S.sharedSplit.code default).r +
      (if Q.par.S.sharedSplit.maskRows == 0 then Q.par.S.sharedSplit.answers else 0) +
      0 / 2 ^ ceilLog2 Q.par.S.sharedSplit.maskRows * Q.par.S.sharedSplit.maskRows +
      0 % 2 ^ ceilLog2 Q.par.S.sharedSplit.maskRows = 0 := by
    rw [hno]
    simp [hone]
  rw [coin_there, h1]
  show rdE.val (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE cO.1.1).toArray 1
    (Q.par.S.sharedSplit.mainRows * (Q.codes.base.getD Q.par.S.sharedSplit.code default).r +
      (if Q.par.S.sharedSplit.maskRows == 0 then Q.par.S.sharedSplit.answers else 0) +
      0 / 2 ^ ceilLog2 Q.par.S.sharedSplit.maskRows * Q.par.S.sharedSplit.maskRows +
      0 % 2 ^ ceilLog2 Q.par.S.sharedSplit.maskRows)) = _
  rw [hidx]
  have hs' : offsetOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1 <
      (liftSend wit (sendingPart (jobOmega ⟨Q, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀).takes.e := hs
  unfold msgCoins coinsE
  rw [Nat.add_zero, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_ofFn,
    dif_pos hs']
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.coin_at_lendings
