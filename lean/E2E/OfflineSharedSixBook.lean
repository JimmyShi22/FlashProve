-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedSixBook.lean: the three premises on the book that `Good` at the shared chain's six rows
takes (E2E/OfflineSharedSixGood.lean), paid at the written book of the key file and the description's
order of places, in scope.

  `ok_of_spent`        an owner's test (`OwnerTest.ok`, Honest/BookGuard.lean) from its `fits` and its guard
                       at the spenders of the entries that spend of the owner: the test itself goes
                       over every entry's spender
  `own_clear_full`     no entry spends a coin of "LIN point", "LOC", "LIN zeta", "SPLIT" (the kernel)
  `folded_fits_full`, `folded_guard_full`, `omega_fits_full`, `omega_guard_full`   the two halves of the
                       two owners' tests, at the written order (the kernel)
  `split_stretch_full`, `spenders_full`   whose coin "SPLIT" spends, and who spends of the two sendings,
                       by the written book (the kernel)
  `shared_book_paid`   **the three premises**, at a book that equals the written one

A yes of these tests is what the two owners' laws ask of a book; what the laws conclude is `fresh` at
the two sendings, one owner at a time. Nothing on any property.
-/
import AtFullSide.K14.Sim.AtKey
import E2E.OfflineFirstSends

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (place sendPlace maskOwner spOwner OwnClear)
open ProofFile.Honest.Small (noneSpent)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull foldedTestPlace)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK)
open VerifierAndGoals (PublicFiles InScope)

/-- **An owner's test from its `fits` and its guard at the spenders that spend of the owner.** -/
theorem ok_of_spent (t : OwnerTest) (B : ProverCoinCounts) (ord : List Place) (o : Addr)
    (hf : t.fits B ord o = true)
    (hs : ((B.ahead.filter fun e => e.once && e.owner == o).all fun e =>
      guardClearB (t.guard o) B ord o e.spender) = true) : t.ok B ord o = true := by
  unfold OwnerTest.ok
  rw [hf, Bool.true_and, List.all_eq_true]
  intro p _
  by_cases hE : (B.spentBy o p).isEmpty = true
  · rw [hE]
    rfl
  · obtain ⟨e, he⟩ : ∃ e, e ∈ B.spentBy o p := by
      cases h' : B.spentBy o p with
      | nil => rw [h'] at hE; exact absurd rfl hE
      | cons e l => exact ⟨e, List.mem_cons_self⟩
    unfold ProverCoinCounts.spentBy at he
    obtain ⟨h1, h2⟩ := List.mem_filter.1 he
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have h3 := List.all_eq_true.1 hs e (List.mem_filter.2 ⟨h1, by simp [h2.2, h2.1.1]⟩)
    rw [h2.1.2] at h3
    rw [h3, Bool.or_true]

/-- No entry of the written book spends a coin of the four own parts. By evaluation. -/
theorem own_clear_full : atFull (fun K =>
    noneSpent (keyBook K) ⟨place 1, 0⟩ && noneSpent (keyBook K) ⟨place 4, 0⟩ &&
      noneSpent (keyBook K) ⟨place 7, 0⟩ && noneSpent (keyBook K) ⟨place 8, 0⟩) = true := by
  decide +kernel

/-- What else the sending of the folded row asks of the written book. By evaluation. -/
theorem folded_fits_full : atFull (fun K =>
    (maskOwner ⟨QK, 0⟩).fits (keyBook K) writtenOrder ⟨sendPlace 2, 0⟩) = true := by
  decide +kernel

/-- Its guard, at every spender that spends of it. By evaluation. -/
theorem folded_guard_full : atFull (fun K =>
    ((keyBook K).ahead.filter fun e => e.once && e.owner == ⟨sendPlace 2, 0⟩).all fun e =>
      guardClearB ((maskOwner ⟨QK, 0⟩).guard ⟨sendPlace 2, 0⟩) (keyBook K) writtenOrder
        ⟨sendPlace 2, 0⟩ e.spender) = true := by
  decide +kernel

/-- What else the sending of Omega asks of the written book. By evaluation. -/
theorem omega_fits_full : atFull (fun K =>
    (spOwner ⟨QK, 0⟩).fits (keyBook K) writtenOrder ⟨sendPlace 5, 0⟩) = true := by
  decide +kernel

/-- Its guard, at every spender that spends of it. By evaluation. -/
theorem omega_guard_full : atFull (fun K =>
    ((keyBook K).ahead.filter fun e => e.once && e.owner == ⟨sendPlace 5, 0⟩).all fun e =>
      guardClearB ((spOwner ⟨QK, 0⟩).guard ⟨sendPlace 5, 0⟩) (keyBook K) writtenOrder
        ⟨sendPlace 5, 0⟩ e.spender) = true := by
  decide +kernel

/-- **By the written book "SPLIT" spends one coin of the extension field, of the sending of Omega,
once.** By evaluation. -/
theorem split_stretch_full : atFull (fun K =>
    ((keyBook K).ahead.filter fun e => e.spender == ⟨place 8, 0⟩).map
      (fun e => (e.owner, e.once, e.count.f, e.count.e)) == [(⟨sendPlace 5, 0⟩, true, 0, 1)]) =
    true := by
  decide +kernel

/-- **By the written book one entry spends of the sending of the folded row: 15 coins of the extension
field, spent by the first part of the test on the folded row's group; and one of the sending of
Omega: "SPLIT"'s.** By evaluation. -/
theorem spenders_full : atFull (fun K =>
    (((keyBook K).ahead.filter fun e => e.once && e.owner == ⟨sendPlace 2, 0⟩).map
      (fun e => (e.spender, e.count.f, e.count.e)) == [(⟨foldedTestPlace, 0⟩, 0, 15)]) &&
    (((keyBook K).ahead.filter fun e => e.once && e.owner == ⟨sendPlace 5, 0⟩).map
      (fun e => (e.spender, e.count.f, e.count.e)) == [(⟨place 8, 0⟩, 0, 1)])) = true := by
  decide +kernel

/-- **The three premises on the book**, at a book that equals the written one, at the description's
order, in scope. -/
theorem shared_book_paid {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) :
    OwnClear Bk ∧
      (maskOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 2, 0⟩ = true ∧
      (spOwner ⟨QK, 0⟩).ok Bk (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) ⟨sendPlace 5, 0⟩ = true := by
  subst hB
  rw [order_named scope hs.named]
  have h0 := of_atFull own_clear_full hK
  simp only [Bool.and_eq_true] at h0
  exact ⟨⟨h0.1.1.1, h0.1.1.2, h0.1.2, h0.2⟩,
    ok_of_spent _ _ _ _ (of_atFull folded_fits_full hK) (of_atFull folded_guard_full hK),
    ok_of_spent _ _ _ _ (of_atFull omega_fits_full hK) (of_atFull omega_guard_full hK)⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.ok_of_spent
#print axioms AtPublicFiles.OfflineRows.own_clear_full
#print axioms AtPublicFiles.OfflineRows.folded_fits_full
#print axioms AtPublicFiles.OfflineRows.folded_guard_full
#print axioms AtPublicFiles.OfflineRows.omega_fits_full
#print axioms AtPublicFiles.OfflineRows.omega_guard_full
#print axioms AtPublicFiles.OfflineRows.split_stretch_full
#print axioms AtPublicFiles.OfflineRows.spenders_full
#print axioms AtPublicFiles.OfflineRows.shared_book_paid
