-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/InT.lean: THREE TESTS ON THE RECORD BEHIND K4's BLOCK THAT "THE PUBLIC TEST
formsInT IS
TRUE AT K4's TWO RUNS" ASKS (`InTAsks`' lines mask, oneRow, reads:
Johnson/Road/K4/InT/Statement.lean), EACH EXCHANGED FOR A TEST WITH CODE ON THE PLAN's LETTERS,
UNDER
`RecIs` (Johnson/Road/K4/Rec/Whole.lean). Statements and proofs, by rewriting. GLUE.

  **`mask_plan`**: the mask row's seat is there wherever `maskSeatP` answers.
  **`oneRow_plan`**: `oneRowB A.F i` is `oneRowP` at the plan's looks.
  **`reads_plan`**: `readsThereB A i k` is `readsThereP`.

OBJECT: none of its own. USER: none yet; meant: whoever pays `InTAsks`. LETTERS: A, R, n, m, own, i,
k.

Limits. `RecIs` IS A PREMISE HERE. i IS A LETTER: `InTAsks` asks its lines at the number of the
reads' array AS WHAT WAS HEARD HOLDS IT (o.v.iU3): that this number is the plan's is not said here.
The three tests on the plan have run nowhere. K04_law, the law of K4's block itself, IS NOT PROVED
BY THIS. Nothing on soundness.
-/
import Johnson.Road.K4.InT.Statement
import Johnson.Road.K4.Rec.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open OnBytes.Road.K4.InT (oneRowB readsThereB)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP oneRowP readsThereP atMoment1P oneRow_is)
open VerifiableInference.Desc.K9 (maskSeat atMoment1)

variable {A : Part9} {R : RecPlan} {n m : ℕ}

/-- **The mask row's seat is there**, under `RecIs`, wherever the plan's term answers. -/
theorem mask_plan (h : RecIs A R n m) (own : List (ℕ × ℕ))
    (hp : (maskSeatP R.shape R.d own R.L.places n m).isSome = true) :
    (maskSeat own A).isSome = true := by
  rw [h.maskSeat own]
  exact hp

/-- **"The array has one own row in the ledger"**, under `RecIs`. -/
theorem oneRow_plan (h : RecIs A R n m) (i : ℕ) : oneRowB A.F i = oneRowP (R.d.trees m) i :=
  oneRow_is h.trees i

/-- **"The reads' array is there"**, under `RecIs`. -/
theorem reads_plan (h : RecIs A R n m) (i k : ℕ) :
    readsThereB A i k = readsThereP R.shape R.layout (R.arrs m) m i k := by
  have e : atMoment1 A = atMoment1P R.shape m :=
    funext fun c => funext fun X => h.atMoment1 c X
  unfold readsThereB readsThereP
  rw [h.arrays, h.layout, e]
  try rfl

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.mask_plan
#print axioms OnBytes.Road.K4.Rec.oneRow_plan
#print axioms OnBytes.Road.K4.Rec.reads_plan
