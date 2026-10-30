-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/ColumnAtTheFirstThreadWhole.lean: CONDITIONAL: on the head at the return and on the
maker's return at the base filling. THE FULL SIZE ALONE.

What is here. `column_hX_at_first_thread` (AtFullSide/K4/ColumnAtTheFirstThread.lean) with its one
named test on public data paid: `closing_returns_at_base` (AtFullSide/K4/ClosingAtBase.lean).

  `column_hX_at_first_thread_whole`   **the column hX at K4's twelve members, under h and hA
  alone.**

Not shown here. NO STAND OF THIS THREAD AT ANY BORDER, 0 INCLUDED, IS KNOWN TO US, SO THE STATEMENT
IS NOT KNOWN TO SPEAK AT ANY RUN. Beneath `closing_at_head` lie 25 closed facts by Lean's kernel,
replayed by no independent checker; in these writers' rides the code switch's seven files on the
closing lay compiled and were built in none. Every limit of
AtFullSide/K4/ColumnAtTheFirstThread.lean's head holds here, but that the test is no hypothesis any
more. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import AtFullSide.K4.ColumnAtTheFirstThread
import AtFullSide.K4.ClosingAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread)
open ProofFile.Honest.K1 (LocB)
open AtPublicFiles.AtFiles (FullSizeMatrix)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL: on h and hA. **THE COLUMN hX AT K4's MEMBER OF GROUP g, AT THE FIRST THREAD WITH
THE BASE PROVER's SCRIPT.** An implication from the thread's stand in front and an accepting
step; no stand of this thread at any border is known to us. -/
theorem column_hX_at_first_thread_whole (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) {g : ℕ} (hg : g < 12) :
    ∀ i ∈ ((firstThread h ⟨theScript h, numbers⟩ w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h ⟨theScript h, numbers⟩ w) Said (28 * g + 4) i :=
  column_hX_at_first_thread h hA (closing_returns_at_base h hA) numbers w Said hg

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.column_hX_at_first_thread_whole
