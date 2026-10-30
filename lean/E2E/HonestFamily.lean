-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/HonestFamily.lean: a family of honest provers of one protocol, one for each number of a copy,
with one type of coins and one public abort set for all numbers; and the one honest prover, whose
private input ends with the number, that is made of them. General definitions and equations that
hold by unfolding. Nothing is shown of any prover.

Why. A sentence on one request's honest prover is written with the copy's number fixed in front
(the number is public and is sent in the clear; WHO PICKS IT is not said here: `Family.glue` lays it
inside the private input's type, so by type a caller may let it hang on the index). The statements
on the compiled argument take ONE honest prover whose private input ends with the number. This file
is the step between the two.

  `Family Q Wt`: coins, public abort set; for each number: the external strings, the strategy, the
    rest of the abort set.
  `Family.at n`: the honest prover at the number n. `Family.glue`: the one honest prover, at the
    private input (i, r, e, n).
  `atNumber H n`: an honest prover whose private input ends with a number, at a fixed number.
  `atNumber_glue`: `atNumber Fm.glue n = Fm.at n`: by unfolding.

Limits. Definitions and one equation by unfolding. Beyond the one type of coins and the one public
abort set nothing ties a family's members to each other; nothing ties them to any written prover. No
property is had.


-/
import Iop.InteractiveOracleProof

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Bridge
open Iop

variable {Y : Type} {E : ExtSpec}

/-- A family of honest provers by the copy's number: ONE type of coins and ONE public abort set. -/
structure Family (Q : InteractiveOracleProof Y E) (Wt : Type) where
  Coin : Type
  [finCoin : Fintype Coin]
  [neCoin : Nonempty Coin]
  ext : ℕ → Wt → E.Str
  strat : ℕ → Wt → Y → Coin → Strat Q.shape Unit
  Bad : Set (Rho Q.shape)
  Hid : ℕ → Wt → Y → Set (Rho Q.shape)

attribute [instance] Family.finCoin Family.neCoin

variable {Q : InteractiveOracleProof Y E}

/-- The honest prover at the number n. -/
def Family.at {Wt : Type} (Fm : Family Q Wt) (n : ℕ) : Honest Q Wt where
  Coin := Fm.Coin
  ext := Fm.ext n
  strat := Fm.strat n
  Bad := Fm.Bad
  Hid := Fm.Hid n

/-- The one honest prover whose private input ends with the number. -/
def Family.glue {I RI Sd : Type} (Fm : Family Q (I × RI × Sd)) : Honest Q (I × RI × Sd × ℕ) where
  Coin := Fm.Coin
  ext := fun w => Fm.ext w.2.2.2 (w.1, w.2.1, w.2.2.1)
  strat := fun w => Fm.strat w.2.2.2 (w.1, w.2.1, w.2.2.1)
  Bad := Fm.Bad
  Hid := fun w => Fm.Hid w.2.2.2 (w.1, w.2.1, w.2.2.1)

/-- An honest prover whose private input ends with a number, at a fixed number: the same coins,
strategy and abort sets. -/
def atNumber {I RI Sd : Type} (H : Honest Q (I × RI × Sd × ℕ)) (n : ℕ) :
    Honest Q (I × RI × Sd) where
  Coin := H.Coin
  ext := fun w => H.ext (w.1, w.2.1, w.2.2, n)
  strat := fun w => H.strat (w.1, w.2.1, w.2.2, n)
  Bad := H.Bad
  Hid := fun w => H.Hid (w.1, w.2.1, w.2.2, n)

theorem atNumber_glue {I RI Sd : Type} (Fm : Family Q (I × RI × Sd)) (n : ℕ) :
    atNumber Fm.glue n = Fm.at n := rfl

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.atNumber_glue
