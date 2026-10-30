-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastMembers.lean: what the file's rule asks of the key file's last chain, member by member, put together from the
laws of each: `OwesS` and `YesS` at a thread over that chain. A table of the debts; it proves none of the hard ones.

Main names.
  `ridesPast_own`: nothing rides past the own test: every item open in front of it is shut by it.
  `owes_last`: `OwesS`, from `PlaysS` at member 2, `Behind` at all four, `ExchangeS` at 0, `RidesPast` at 0, 1, 3.
  `yes_last`: `YesS`, from `AcceptedS` at each member.

What stays open. Every premise named here. `PlaysS` at 2 is the guarded half's play and the test's own trees.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyRowsLater
import Johnson.Desc.ProofFile.Honest.Thread.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.Last (ItemL)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyThread (lengths row_sources₃ row_end₃ plays_quiet₃ exchange_of_nil)

section general
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ix Tr X P₁ Wt S₂ S₃' : Type}
  (L : LastThread.Letters Bk S₂ S₃' Cl W₀ Rc Ix Tr X P₁ Wt)

/-- **Nothing rides past the own test.** -/
theorem ridesPast_own : RidesPast L.thread 2 := by
  intro k s m E s' ps i v _ _ hi hs _ _
  have ho : fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2 =
      [ItemL.pinI, ItemL.pinV, ItemL.pinO, ItemL.rows] := by decide
  have hh : (LastRows.rows 2).shuts = [ItemL.rows, ItemL.pinV, ItemL.pinI, ItemL.pinO] := by decide
  have hi' : i ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2 := hi
  have hs' : i ∉ (LastRows.rows 2).shuts := hs
  rw [ho] at hi'
  rw [hh] at hs'
  have key : ∀ j : ItemL, j ∈ [ItemL.pinI, ItemL.pinV, ItemL.pinO, ItemL.rows] →
      j ∈ [ItemL.rows, ItemL.pinV, ItemL.pinI, ItemL.pinO] := by
    intro j
    cases j <;> decide
  exact absurd (key i hi') hs'

/-- The own test owes nothing. -/
theorem owes_own : (L.thread.row 2).owes = [] := by
  show (LastRows.rows 2).owes = []
  decide

end general

section key
variable {Bk : ProverCoinCounts} {W₀ Rc X : Type} {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
  (U : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X Xi)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)

/-- **`OwesS` at the last chain.** -/
theorem owes_last (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : U.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hP : PlaysS U Said 2)
    (hB : ∀ b, b < 4 → Behind U b) (hE : ExchangeS U Said 0) (ho₁ : (U.row 1).owes = [])
    (ho₂ : (U.row 2).owes = []) (ho₃ : (U.row 3).owes = []) (hR : ∀ b, b < 4 → RidesPast U b) :
    OwesS U Said := by
  intro b hb
  have hl : U.bs.length = 4 := by
    rw [hbs]
    exact (lengths scope hs.named).2.2
  rw [hl] at hb
  match b, hb with
  | 0, _ =>
    exact ⟨playsS_of _ _ (plays_quiet₃ scope hs.named U hbs 0 (by decide)), behindS_of _ _ (hB 0 (by decide)), hE,
      ridesPastS_of _ _ (hR 0 (by decide))⟩
  | 1, _ => exact row_sources₃ Xs Nr Pl hs scope U hbs (hB 1 (by decide)) ho₁ (hR 1 (by decide)) Said
  | 2, _ =>
    exact ⟨hP, behindS_of _ _ (hB 2 (by decide)), exchangeS_of _ _ (exchange_of_nil _ ho₂),
      ridesPastS_of _ _ (hR 2 (by decide))⟩
  | 3, _ => exact row_end₃ Xs Nr Pl hs scope U hbs (hB 3 (by decide)) ho₃ (hR 3 (by decide)) Said

/-- **`YesS` at the last chain.** -/
theorem yes_last (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : U.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (fl : Nat → (descriptionFromSource Xs Nr Pl).S₃ → List Fmt.Drawn → Option String)
    (hA : ∀ b, b < 4 → AcceptedS U Said fl b) : YesS U Said fl := by
  intro b hb
  have hl : U.bs.length = 4 := by
    rw [hbs]
    exact (lengths scope hs.named).2.2
  rw [hl] at hb
  exact hA b hb

end key

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.ridesPast_own
#print axioms AtPublicFiles.KeyLastChain.owes_own
#print axioms AtPublicFiles.KeyLastChain.owes_last
#print axioms AtPublicFiles.KeyLastChain.yes_last
