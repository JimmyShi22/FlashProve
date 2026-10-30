-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CalmLots.lean: the words for a part, a half and a lot that have no first stop.
Definitions alone. Nothing is claimed of any prover here.

  Calm p      p's first stop never fires, and p states the share 0 for it
  HalfCalm x  every part of the half x is quiet
  LotCalm L   every half of the lot L is quiet, at every public part and ground
-/
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest

variable {V W X : Type}

/-- A part whose first stop never fires and whose share for it is 0. -/
def Calm (p : Part V W X) : Prop :=
  (∀ l o, p.bad l o = none) ∧ p.badShare.val = 0

/-- A half whose parts are all quiet. -/
def HalfCalm (x : Placed V W X) : Prop := ∀ p ∈ x.parts, Calm p

/-- A lot whose halves are all quiet, at every public part and ground. -/
def LotCalm (L : HLot V W X) : Prop := ∀ Z G, ∀ x ∈ L.halves Z G, HalfCalm x

end P1K8

#print axioms P1K8.Calm
#print axioms P1K8.HalfCalm
#print axioms P1K8.LotCalm
