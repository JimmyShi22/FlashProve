-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/QuietLots.lean: the words for a part, a half and a lot that have no second stop.
Definitions alone. Nothing is claimed of any prover here.

  Quiet p      p's second stop never fires, and p states the share 0 for it
  HalfQuiet x  every part of the half x is quiet
  LotQuiet L   every half of the lot L is quiet, at every public part and ground
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest

variable {V W X : Type}

/-- A part whose second stop never fires and whose share for it is 0. -/
def Quiet (p : Part V W X) : Prop :=
  (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0

/-- A half whose parts are all quiet. -/
def HalfQuiet (x : Placed V W X) : Prop := ∀ p ∈ x.parts, Quiet p

/-- A lot whose halves are all quiet, at every public part and ground. -/
def LotQuiet (L : HLot V W X) : Prop := ∀ Z G, ∀ x ∈ L.halves Z G, HalfQuiet x

end P1K8

#print axioms P1K8.Quiet
#print axioms P1K8.HalfQuiet
#print axioms P1K8.LotQuiet
