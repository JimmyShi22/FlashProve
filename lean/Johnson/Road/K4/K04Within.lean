-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Within.lean: WHAT A YES OF THE PUBLIC ITEM "K13.pileWithin" GIVES, AT THE WIDER
MEANING: PROVED. Three statements with their proofs.

WHY. The chain that pins the name of the mask entry that K4's row bears (`Rec.nextEntryIs`) spends
one implication out of the promise: where the public item "K13.pileWithin" holds, every ledger of
the verifier's state is that of some number of takes since it was made (`Rec.EWithin`). In the
assembly `k04_law_at` that was a binder (hWi). At the wider meaning the item's test is
code: `pileWithinC s := ledgersFitC s && rowsWithinC s` (Johnson/Desc/K13/PubK13.lean), by
`pubWide_pileWithin` (:= rfl). So the binder comes down to a sentence on code alone, of
no meaning: a yes of `ledgersFitC` gives `LedgersFit` (`ledgersFit_of_C`),
unfolded to the bottom. It is the forward half of `OwedLedgersC`, which is stated in
Johnson/Desc/K13/Law/OwedWithin.lean and proved in LedgersC.lean beside it (neither imported); the
road is the one that OwedWithin.lean names.

  `nextAtC_eq`: where 0 < m: the test's own count `nextAtC m k` is the laws' `nextAt m k`. By
    `takenNo_eq` (OnBytes/Iop/LedgerPlaces.lean); the rest is unfolding: `ceilLog2` is
    `logUp`, `entryNo m r c` is r + 2 ^ logUp m * c, `freeAt m k` is (k % m, k / m).
  `ledgersFit_of_C`: `ledgersFitC s = true → LedgersFit s.st`: the test's six clauses are
    `LedgerAt`'s, one by one, at k := the free count less what is left.
  `within_mgWide`: `Rec.EWithin (mgWide 𝔇 E Mg)`, AT EVERY 𝔇, E AND Mg.

Limits. `within_mgWide` SPEAKS AT THE WIDER MEANING: it is one side of a bridge:
what holds at it counts only when the bridge is paid. At the composed meaning itself the item is
struck, and `Rec.EWithin` holds there for nothing. The backward half is LedgersC.lean's: here it is
not shown. That "K13.pileWithin" HOLDS anywhere is not shown: this says what a yes gives. Nothing on
soundness.
-/
import Johnson.Road.K4.Rec.NextEntryStatement
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes
open Fmt.Places (entryNo freeAt)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.K13 (nextAtC ledgerAtC ledgersFitC pileWithinC)
open VerifiableInference.Desc.K13.Law (nextAt LedgerAt LedgersFit)
open VerifiableInference.Desc.Sound (MsgT MgData WideData CellsQ mgWide)

/-- Where there is a mask row, the test's own count is the laws'. -/
theorem nextAtC_eq {m : ℕ} (hm : 0 < m) : ∀ k, nextAtC m k = nextAt m k
  | 0 => rfl
  | j + 1 => by
    show entryNo m (freeAt m j).1 (freeAt m j).2 + 1 = takenNo m j + 1
    rw [takenNo_eq hm j]

/-- **A yes of the test on the ledgers gives the laws' word.** -/
theorem ledgersFit_of_C (s : S) (h : ledgersFitC s = true) : LedgersFit s.st := by
  intro o x hx hl
  obtain ⟨l, hl'⟩ := Option.isSome_iff_exists.1 hl
  have h1 := Array.all_eq_true_iff_forall_mem.1 h x (Array.mem_of_getElem? hx)
  rw [hl'] at h1
  simp only [ledgerAtC, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h1
  refine ⟨_, x, l, hx, hl', a1, a2, a3, a4, Nat.add_sub_cancel' a5, ?_⟩
  rw [a6, nextAtC_eq a1]

/-- **At the wider meaning a yes of "K13.pileWithin" gives that every ledger fits.** -/
theorem within_mgWide {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) : Rec.EWithin (mgWide 𝔇 E Mg) := by
  intro a h
  have h1 : pileWithinC a.2 = true := h
  unfold pileWithinC at h1
  exact ledgersFit_of_C a.2 (Bool.and_eq_true_iff.1 h1).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.nextAtC_eq
#print axioms OnBytes.Road.K4.ledgersFit_of_C
#print axioms OnBytes.Road.K4.within_mgWide
