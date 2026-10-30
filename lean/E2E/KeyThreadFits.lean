-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyThreadFits.lean: THE KEY FILE's THREE THREADS AS FIRST FILLED (E2E/KeyThreadBase.lean) PASS
THE TESTS WITH CODE ON A THREAD's LETTERS (`Thread.fits`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean), seated at any prover of parts (`seat₁`, `seat₂`,
`seat₃`, E2E/KeyLaid.lean). Statements and proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness,
nothing on what a view shows.

  `fits_first`, `fits_shared`, `fits_last`: GENERAL IN THE DESCRIPTION: where it passes its own
    tests on the plan: at the table's 19, 12 and 4 rows, at every prover of parts and every value of
    `Rest`.
  `lengths`: in scope the key file's own description has 19, 12 and 4 sub-protocols
    (`places_named`, E2E/KeyPlacesNamed.lean).
  **`fits₁`**, **`fits₂`**, **`fits₃`**: IN SCOPE, at the key file's own description: the three
    seated threads pass at their chains' numbers of sub-protocols: the three premises on
    `Thread.fits` of the accept law with the prover of parts laid in (E2E/KeyAcceptProver.lean), at
    these threads.

Limits.
- ALL LIMITS OF E2E/KeyThreadBase.lean: `Thread.fits` = true SHOWS NO CHOICE RIGHT: it would hold at
  a table without any item. What weighs (what an item says, the witness, the trees' tables, the
  debts at every sub-protocol) is not here.
- The three numbers of sub-protocols are the full size's: in scope alone.


-/
import E2E.KeyThreadBase
import E2E.KeyLaid

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest
open AtPublicFiles.KeyLink (seat₁ seat₂ seat₃)

section Threads
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
variable (H : Prover W₀ Rc Xi Ky Tr X₀ X)

/-- The first chain's thread passes, at a description that passes its own tests on the plan, at the
table's number of rows. -/
theorem fits_first (hp : F.planOk = true) (R : Rest Bk F.S₁ (Local W₀ Rc Xi Tr)) :
    (seat₁ F H (keyBase₁ F R)).fits 19 = true :=
  fits_of _ 19 table₁ (fun x hx => lists_of_shaped ((planOk_all hp).1 x hx).2)
    (fun _ h => by cases h) (fun _ h => by cases h) (fun j => (Nat.zero_add _).symm)
    (Nat.le_refl _)

theorem fits_shared (hp : F.planOk = true) (R : Rest Bk F.S₂ (Common W₀ Rc Ky)) :
    (seat₂ F H (keyBase₂ F R)).fits 12 = true :=
  fits_of _ 12 table₂ (fun x hx => lists_of_shaped ((planOk_all hp).2.1 x hx).2)
    (fun _ h => by cases h) (fun _ h => by cases h) (fun j => (Nat.zero_add _).symm)
    (Nat.le_refl _)

theorem fits_last (hp : F.planOk = true) (R : Rest Bk F.S₃ (Local W₀ Rc Xi Tr)) :
    (seat₃ F H (keyBase₃ F R)).fits 4 = true :=
  fits_of _ 4 table₃ (fun x hx => lists_of_shaped ((planOk_all hp).2.2 x hx).2)
    (takenIn_taken _)
    (fun σ hσ => by
      obtain ⟨c, m, rfl⟩ := takenIn_taken _ σ hσ
      show (if c == 0 then sentIn (decl₁ F) m else (decl₁ F).length + sentIn (decl₂ F) m) ≤
        (decl₁ F ++ decl₂ F).length
      rw [List.length_append]
      have a := sentIn_le (decl₁ F) m
      have b := sentIn_le (decl₂ F) m
      split <;> omega)
    (fun j => by
      show ((decl₁ F).length + (decl₂ F).length) + sentIn (decl₃ F) j =
        (decl₁ F ++ decl₂ F).length + sentIn (decl₃ F) j
      rw [List.length_append])
    (by
      show (decl₁ F).length ≤ (decl₁ F ++ decl₂ F).length
      rw [List.length_append]
      exact Nat.le_add_right _ _)

end Threads

/-! ## 5 In scope, at the key file's own description -/

section Scope
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeyInst)
open AtPublicFiles.KeyBook (places_named fullFirst fullShared fullSecond)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

theorem lengths (scope : InScope Z = true) (h : KeyNamed Z Xs N P) :
    (keyFileDescription Xs N P).first.blocksInOrder.length = 19 ∧ (keyFileDescription Xs N P).shared.blocksInOrder.length = 12 ∧
      (keyFileDescription Xs N P).second.blocksInOrder.length = 4 := by
  obtain ⟨r1, r2, r3⟩ := places_named scope h
  have l1 := congrArg List.length r1
  have l2 := congrArg List.length r2
  have l3 := congrArg List.length r3
  unfold rowsOf at l1 l2 l3
  rw [List.length_map] at l1 l2 l3
  exact ⟨l1.trans (by decide), l2.trans (by decide), l3.trans (by decide)⟩

variable (H : Prover W₀ Rc KeyInst Ky Tr X₀ X)

/-- **In scope the first chain's thread passes the tests with code.** -/
theorem fits₁ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (R : Rest Bk (keyFileDescription Xs N P).S₁ (Local W₀ Rc KeyInst Tr)) :
    (seat₁ (keyFileDescription Xs N P) H (keyBase₁ (keyFileDescription Xs N P) R)).fits
      (keyFileDescription Xs N P).first.blocksInOrder.length = true := by
  rw [(lengths scope h).1]
  exact fits_first _ H h.plan R

/-- **The shared chain's.** -/
theorem fits₂ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (R : Rest Bk (keyFileDescription Xs N P).S₂ (Common W₀ Rc Ky)) :
    (seat₂ (keyFileDescription Xs N P) H (keyBase₂ (keyFileDescription Xs N P) R)).fits
      (keyFileDescription Xs N P).shared.blocksInOrder.length = true := by
  rw [(lengths scope h).2.1]
  exact fits_shared _ H h.plan R

/-- **The last chain's.** -/
theorem fits₃ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (R : Rest Bk (keyFileDescription Xs N P).S₃ (Local W₀ Rc KeyInst Tr)) :
    (seat₃ (keyFileDescription Xs N P) H (keyBase₃ (keyFileDescription Xs N P) R)).fits
      (keyFileDescription Xs N P).second.blocksInOrder.length = true := by
  rw [(lengths scope h).2.2]
  exact fits_last _ H h.plan R

end Scope

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.fits_first
#print axioms AtPublicFiles.KeyThread.fits_shared
#print axioms AtPublicFiles.KeyThread.fits_last
#print axioms AtPublicFiles.KeyThread.lengths
#print axioms AtPublicFiles.KeyThread.fits₁
#print axioms AtPublicFiles.KeyThread.fits₂
#print axioms AtPublicFiles.KeyThread.fits₃
