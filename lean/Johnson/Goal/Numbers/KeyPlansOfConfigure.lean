-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeyPlansOfConfigure.lean: wherever the planner's routine `configure`
(OnBytes/Params/Configure.lean) returns at the written lines of the full size, at shapes whose
ranges size to the typed sizes of a key of full size, the key file's three plans in what it returns
are the three written priced plans (Johnson/G/PricedKeyLit.lean): all 18950 rounds. The digest and
the caller's bits are letters, and no hash is named.

It is the form of `keyPlansWritten`
(Johnson/Goal/Numbers/KeyAllPlansWritten.lean [not in this library]) at `configure`'s
own yes: that statement goes through the program's planner, which forms the digest by the format's
hash.

Statements and proofs.
  `keyPlans_of_sizes`: if `configure l x cfg bits` returns M, M's sizes of the key file are
    `keyFull` and M's setting is `recordSet`, then M's plans for the key file are the three written
    ones. From `configure_plans` (OnBytes/Plan/PlanListsConfigure.lean) and the three closed
    equations (KeyFirstListed.lean, KeyLaterListed.lean).
  `keyPlans_of_configure`: the same at the lines `recordLines`, from `Plan.keySized recordLines
    x.ranges = some keyFull`. That premise holds of what the proof of the ranges looks up in the
    layout of the ten written sizes (`keySized_returns`,
    Johnson/Goal/PlanValues/KeySizedReturns.lean).
  `keyPriced_of_configure`: so `PricedRounds writtenKFull` holds of M's three plans, and `Desc.keyOk
    M` = true.
No evaluation is made here.

What of OnBytes/Model/ is used: nothing by name.

Limits. One way: from a `configure` that returns. Nothing says that an error bounds a count. Nothing
on soundness.
-/
import Johnson.Goal.Numbers.KeyLaterListed
import Johnson.Goal.Numbers.KeyFirstListed
import OnBytes.Plan.PlanListsConfigure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params OnBytes.Flat.Held Lk6.AtPlan Johnson.G

/-- From the sizes of the key file and the setting: the three plans are the written ones. -/
theorem keyPlans_of_sizes {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : ℕ} {M : Configured}
    (h : configure l x cfg bits = .ok M) (hk : M.sized.key = keyFull)
    (hs : M.sized.set = recordSet) :
    M.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := by
  obtain ⟨_, _, P1, P2, P3, ek, a1, a2, a3, _⟩ := configure_plans h
  rw [hk] at a1
  rw [hk, hs] at a2 a3
  have k1 : P1 = keyThree.A.plan := first_written a1
  have k2 : P2 = keyThree.B.plan := Except.ok.inj (a2.symm.trans shared_written)
  have k3 : P3 = keyThree.C.plan := Except.ok.inj (a3.symm.trans second_written)
  rw [ek, k1, k2, k3]

/-- **At the written lines, from the sizing of the key file.** -/
theorem keyPlans_of_configure {x : Shapes} {cfg : ByteArray} {bits : ℕ} {M : Configured}
    (h : configure recordLines x cfg bits = .ok M)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) :
    M.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] :=
  keyPlans_of_sizes h
    (Option.some.inj ((sized_key (configure_plans h).1).symm.trans hk))
    (sized_link (configure_plans h).1).1

/-- So the prices hold of its three plans, and the key file's own public test says yes. -/
theorem keyPriced_of_configure {x : Shapes} {cfg : ByteArray} {bits : ℕ} {M : Configured}
    (h : configure recordLines x cfg bits = .ok M)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) :
    (∃ K₁ K₂ K₃, M.key = [K₁, K₂, K₃] ∧ PricedRounds writtenKFull K₁ K₂ K₃) ∧
      Desc.keyOk M = true :=
  ⟨⟨_, _, _, keyPlans_of_configure h hk, keyPricedFull⟩,
    keyOk_of_lit key_lit_ok _ (keyPlans_of_configure h hk)⟩

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.keyPlans_of_sizes
#print axioms VerifiableInference.Number.ByRuns.keyPlans_of_configure
#print axioms VerifiableInference.Number.ByRuns.keyPriced_of_configure
