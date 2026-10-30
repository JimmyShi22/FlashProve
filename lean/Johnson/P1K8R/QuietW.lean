-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/QuietW.lean: the lot of the message W's side is quiet.
Words: Johnson/P1K8R/QuietLots.lean. The halves are those of Johnson/P1K8R/QuietK1K13.lean.

  wSideNo_quiet   the side at the number off the public part, general in its letters
  wLot_quiet      the lot as the filling with W's lot has it

Limits. A lot with no half is quiet: where the shape has no such message the lot has none. Nothing
is said of a run or of any property of a prover.
-/
import Johnson.P1K8R.QuietK1K13
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile ProofFile.Honest

variable {V W X W₀ : Type}

/-- The message W's side at the number off the public part. -/
theorem wSideNo_quiet (wit : W → K1.PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (D : Pub → Ground → RowDataOf ProofFile.Inst) :
    LotQuiet (K1.wSideNo (V := V) (X := X) wit o D) :=
  fun Z G x hx => wHalves_quiet wit (K1.lotNo o Z) D Z G x hx

/-- **The lot of the message W's side.** -/
theorem wLot_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) :
    LotQuiet (wLotAt (X := X) I o O) :=
  LotQuiet.byPub _ _ fun _ => wSideNo_quiet _ o _

end P1K8

#print axioms P1K8.wSideNo_quiet
#print axioms P1K8.wLot_quiet
