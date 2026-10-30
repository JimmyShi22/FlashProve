-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/KeyFourTests.lean: the key file's four proximity tests laid into its parts
(KeyParts, E2E/KeyProver.lean): the pairs at G_u and G_omega (E2E/KeyPartsHalves.lean), the test on
the ranges (E2E/KeyRangesJob.lean) and the file's own test (E2E/KeyProverSideOfOwnTest.lean).

  withTests                the parts with the four in place
  withTests_rng, _own      what the two fields hold
  keyProver_second_tests   the prover's last chain is the own test

Limits.
- Every other field of the parts stays as K has it; no value of the parts is given.
- All four pairs have free letters and no arm; that a letter is the sender's own is the caller's.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyPartsHalves
import E2E.KeyProverSideOfOwnTest
import E2E.KeyRangesJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open VerifiableInference.Desc.K12 (P12)
open AtPublicFiles.KeyFile (KeyParts keyProver randK14 In1)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega proverSideOfGuardedSending)
open AtPublicFiles.KeyThread (rangesTestJob)
open OnBytes.Slice (GF)
open ProofFile.Honest (Local Placed)
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.K12.Light (askOf)

variable {W₀ Rc X₀ X Wk : Type}

/-- The reader of the shared chain's committed rows, of the own test's input. -/
def askTests (K : KeyParts W₀ Rc X₀ X Wk) : In1 W₀ Rc → ProofFile.Honest.K14.Ask :=
  askOf K.send (fun w => K.weights w.w₀) fun w => randK14 (K.rand w.rc)

/-- The test on the ranges, as a prover's side. -/
def rngTest (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat) :
    Placed (In1 W₀ Rc) (In1 W₀ Rc) X :=
  proverSideOfProximityTest (rangesTestJob Xs N Pl entry groups first)

/-- The file's own test, as a prover's side, at the parts' two sendings. -/
def ownTest (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) :
    Placed (In1 W₀ Rc) (In1 W₀ Rc) X :=
  proverSideOfGuardedSending Xs N Pl K.idx K.w K.send id (askTests K)

/-- **The parts with the four proximity tests in place.** -/
def withTests (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (pU pO : P12) (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
    (first : Nat) : KeyParts W₀ Rc X₀ X Wk :=
  { withTestsOnUAndOmega K pU pO with
    rng := rngTest Xs N Pl entry groups first
    own := ownTest K Xs N Pl }

section
variable (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (pU pO : P12) (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

theorem withTests_rng :
    (withTests K Xs N Pl pU pO entry groups first).rng = rngTest Xs N Pl entry groups first := rfl

theorem withTests_own :
    (withTests K Xs N Pl pU pO entry groups first).own = ownTest K Xs N Pl := rfl

/-- The prover's last chain is the own test. -/
theorem keyProver_second_tests :
    (keyProver (withTests K Xs N Pl pU pO entry groups first)).second = [ownTest K Xs N Pl] := rfl

end

end AtFullSide.K12

#print axioms AtFullSide.K12.askTests
#print axioms AtFullSide.K12.rngTest
#print axioms AtFullSide.K12.ownTest
#print axioms AtFullSide.K12.withTests
#print axioms AtFullSide.K12.withTests_rng
#print axioms AtFullSide.K12.withTests_own
#print axioms AtFullSide.K12.keyProver_second_tests
