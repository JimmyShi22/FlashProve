--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPaidCells.lean: WHICH OF THE DEBTS AT THE KEY FILE's 35 SUB-PROTOCOLS, ASKED FROM THE PAIR OF
A THREAD AND WHAT IS SAID, ARE PAID BY A CALL AT THE THREAD `laid₁` (E2E/KeyRest.lean) AND A SHARED
THREAD THAT IS QUIET AT ITS ENDS: at all halves, all tables, and ANY letter for what is said.
Statements with their proofs: one call each
of `behindS_of` or `ridesPastS_of` (Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) over
E2E/KeyBehind.lean and E2E/KeyRides.lean. NOTHING IS CLAIMED OF ANY
PROVER.

  **`behindS₁`**: `BehindS` at the first chain's twelve sub-protocols of no kind (numbers 2, 3, 5 to
    9, 11 to 14, 18): in scope, at the X, N, P of which the description at the public files is made
    (`KeySourced`).
  **`ridesPastS₁`**: `RidesPastS` at the same twelve: under `ReadsL L.base.h₁`, a premise on one
    letter of the filling (`LettersOk.readsL`, E2E/KeyRest.lean, has it from `LettersOk`).
  **`behindS₂`**: `BehindS` at the shared chain's numbers 0 and 11, at any thread over that chain
    that is quiet at its ends (`QuietEnds₂`): in scope, under `KeySourced` likewise.

Limits.
- EACH HOLDS ALSO WHERE THE THREAD STANDS AT NOTHING: that the thread stands at any border is shown
  nowhere.
- `ReadsL` is shown of no filling here. `KeySourced` is had only where the gate on the public files
  is open.
- 26 debts: 12, 12 and 2. The law asks six kinds of debt at each of the 35 sub-protocols. Of these
  two kinds nothing is paid here at the others.

-/
import E2E.KeyBehind
import E2E.KeyRides
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open ProofFile.Honest

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **`BehindS` at the first chain's twelve of no kind.** -/
theorem behindS₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18],
      BehindS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) S₁ b :=
  fun b hb => behindS_of _ _ (behind₁ Xs N Pl L w₀ rc x hs scope b hb)

/-- **`RidesPastS` at the same twelve.** -/
theorem ridesPastS₁ (hG : Johnson.RunOne.KeyRows1.ReadsL L.base.h₁)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18],
      RidesPastS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) S₁ b :=
  fun b hb => ridesPastS_of _ _ (ridesPast₁ Xs N Pl L w₀ rc x hG b hb)

/-- `BehindS` at the shared chain's front and end. -/
theorem behindS₂ {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hO : OverShared Xs N Pl T) (hQ : QuietEnds₂ T) (S₂ : Nat → Coins Bk → Mid W Xh → Prop) :
    ∀ b ∈ [0, 11], BehindS T S₂ b :=
  fun b hb => behindS_of _ _ (behind₂ Xs N Pl hs scope hO hQ b hb)

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.behindS₁
#print axioms AtPublicFiles.KeyThread.ridesPastS₁
#print axioms AtPublicFiles.KeyThread.behindS₂
