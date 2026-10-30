-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnHalf.lean: the premise `hhalf` of `last_done`, where the chain's one half is `proverSideOfGuardedSending`.

  `half_own`.

Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyProverSideOfOwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyLay (jobKWAt proverSideOfGuardedSending)

variable {V W₀ Rc Tr Y Wd : Type} (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : ProofFile.Honest.K14.SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
  (ask : Local W₀ Rc Xi Tr → ProofFile.Honest.K14.Ask)

/-- **The half at the job's place is the guarded half.** -/
theorem half_own (hs : List (Placed V (Local W₀ Rc Xi Tr) Y)) (h : hs = [proverSideOfGuardedSending Xs Nr Pl JI JW A lift ask]) :
    (hs.find? fun g => g.place == (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place) =
      some (proverSideOfProximityTest (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest : Placed V (Local W₀ Rc Xi Tr) Y).needsField := by
  subst h
  have e : (proverSideOfGuardedSending Xs Nr Pl JI JW A lift ask : Placed V (Local W₀ Rc Xi Tr) Y).place =
      (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p.place := rfl
  simp only [List.find?_cons, e, beq_self_eq_true]
  rfl

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.half_own
