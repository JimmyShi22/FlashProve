--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMeet.lean: THE THREAD `laid₁` (E2E/KeyRest.lean) AND A SHARED AND A LAST THREAD THAT STAND
WHERE THE RULE ASKS SIT AT THE KEY FILE's DESCRIPTION AND AT ANY PROVER, where their halves are that
prover's; at any tables; in scope. One statement with its proof, by unfolding and three calls.
NOTHING IS CLAIMED OF ANY PROVER.

Why. The laws on the verifier's side of the key file's threads are stated at `laid_i … hs tb`, for
all halves hs and all tables tb (E2E/KeyBehind.lean, which also has: a seated thread, and one whose
tables are laid anew, is such a term). The accept law (E2E/KeyAcceptFamilies.lean) asks of its
threads that they sit. Here the two meet.

  **`sits_laid`**: `Sits (D Xs N Pl) H (laid₁ … H.first tb₁) U U₃`.

By what. The first thread's five equations on its places are by unfolding, and its test with code
is `fits₁` (E2E/KeyThreadFits.lean), stated at the seated base thread: it serves because
`Thread.fits` reads neither the halves nor the tables. The other two threads' places and tests with
code are premises: `sits_two`, `sits_three`, `fits_key`, `fits_last_key` are meant.

Limits.
- All limits of E2E/KeyThreadFits.lean: `Thread.fits` = true shows no choice right.
- In scope alone. The letters of the threads (the filling L, the private input's two parts, the
  instance, the tables) are free.

-/
import E2E.KeyBehind
import E2E.KeyThreadFits

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open ProofFile.Honest
open AtPublicFiles.AtFiles (KeyNamed)
open VerifierAndGoals (PublicFiles InScope)

/-- **The three threads sit**, at any prover's own halves and at any tables. -/
theorem sits_laid {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X₀' X' : Type} {Z : PublicFiles} {Xs : Source}
    {N : H2U.PlaceNums} {Pl : LaterPlaces} (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
    (H : Prover W₀ Rc Xi OnBytes.TableKey Unit X₀' X')
    (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table)
    (U : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀'
      OnBytes.TableKey)
    (h₂ : U.φ = .shared ∧ U.chain = 1 ∧ U.ft = 0 ∧ U.bs = (D Xs N Pl).shared.blocksInOrder ∧
      U.hs = H.shared)
    (hf : U.fits (D Xs N Pl).shared.blocksInOrder.length = true)
    (U₃ : Thread Bk (D Xs N Pl).S₃ (D Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X' Xi)
    (h₃ : U₃.φ = .own ∧ U₃.chain = 2 ∧ U₃.ft = (D Xs N Pl).lastChainFirstTreeNumber ∧
      U₃.bs = (D Xs N Pl).second.blocksInOrder ∧ U₃.hs = H.second)
    (hf₃ : U₃.fits (D Xs N Pl).second.blocksInOrder.length = true) :
    Sits (D Xs N Pl) H (laid₁ Xs N Pl L w₀ rc x H.first tb₁) U U₃ :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, h₂, h₃, fits₁ H scope h (rest₁ Xs N Pl L w₀ rc x), hf, hf₃⟩

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.sits_laid
