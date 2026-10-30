-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsOwnField.lean: THE FIELD `ownTest` OF `KeyOthersPlay` (E2E/OfflineRunsKey.lean), in its own type: `PlaysAtSecond` at
the key file's description, at `keyProver K`, at every input, at the place `ownTestPlace`. In scope, at the written book.

  `ownTest_at_parts`   K a letter whose field `own` is the pair behind the guard (`proverSideOfGuardedSending`, E2E/KeyProverSideOfOwnTest.lean), the job's five
                       letters free
  `ownTest_at_value`   at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean)

By `own_plays_at_parts` (E2E/OfflineRunsOwn.lean); the field `opened` of `MidForm` pays the guard.

Limits. Those of E2E/OfflineRunsOwn.lean. The book is not free: that the two parts' readers agree comes from the written
book's ties. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineRunsOwn
import E2E.OfflineRunsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub Ask)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub ownTestPlace)
open AtPublicFiles.KeyLay (proverSideOfGuardedSending)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- **The field `ownTest`, at `keyProver K`.** -/
theorem ownTest_at_parts {W₀ Rc X₀ X' Wk Wd : Type} {Z : PublicFiles} {K₀ : KeyPub} {Xs : Source}
    {N : H2U.PlaceNums} {Pl : LaterPlaces} {JI JW : ProofFile.Honest.K1.SendJob Wd X'} {A : SendPub}
    {lift : Local W₀ Rc Xi Unit → Wd} {ask : Local W₀ Rc Xi Unit → Ask} {Bk : ProverCoinCounts}
    (hB : Bk = keyBook K₀) (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (K : KeyParts W₀ Rc X₀ X' Wk)
    (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A lift ask) (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtSecond (keyFileDescription Xs N Pl) Bk (keyProver K) own ownTestPlace :=
  fun j b hj hp => own_plays_at_parts hB hK hsrc scope K hown _ (fun _ hm => hm.opened) j b hj hp

/-- **The field `ownTest`, at the offline prover's own senders.** -/
theorem ownTest_at_value {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source)
    (N : H2U.PlaceNums) (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand)
    (inR : W₀ → Bool) (d : W₀) (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF)
    (groups : List (List Nat)) (first : Nat) {Z : PublicFiles} (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts}
    (hB : Bk = keyBook K₀) (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtSecond (keyFileDescription Xs N Pl) Bk
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) own ownTestPlace :=
  ownTest_at_parts hB hK hs scope _ rfl own

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.ownTest_at_parts
#print axioms AtPublicFiles.OfflineRows.ownTest_at_value
