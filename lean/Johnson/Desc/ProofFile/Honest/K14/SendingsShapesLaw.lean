-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsShapesLaw.lean: the one public test on the two sendings'
shapes (sendingsFit, Honest/K14/SendingsShapes.lean) gives the premises on shapes that this kind's
laws on the two sendings take. WHO TAKES THEM: exchange_fit, here, calls sendShapes_of_fit; nothing
else in the library calls any of the four yet.

  sendShapes_of_fit   it gives SendShapes (Honest/K14/SendingsShows.lean)
  free_of_fit     it gives that o_sp has a free entry
  lengths_of_fit  it gives that every code's message length is a power of two
  exchange_fit    so Exchange at both sendings, at the term fullOver O
                  (Honest/K14/Thread2Full.lean), from Plan2, the test, and that no two messages have
                  one tenant

Where the test is paid: not here. It holds in scope under LaidAt (sendings_of_laid,
Honest/K14/SendingsAtHead.lean), at the written sizes (shapesFit_written,
Honest/K14/SharedAheadOwners.lean) and at the plans of sendingsFit_key and sendingsFit_real
(Honest/K14/SendingsShapesAt.lean).
What is not claimed. What
Thread2Full.lean's head says of its sentences holds of exchange_fit: it is a sentence UNDER the
thread's sentence Thr, and what it is worth hangs on O's other fields. Nothing on a verifier's
decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open Desc.K14 (P14)

variable {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- The test gives SendShapes. -/
theorem sendShapes_of_fit (h : sendingsFit Q = true) : SendShapes Q := by
  unfold sendingsFit at h
  simp only [Bool.and_eq_true] at h
  exact sendShapes_of Q h.1.2

/-- The test gives that o_sp has a free entry. -/
theorem free_of_fit (h : sendingsFit Q = true) :
    0 < Send.freeMaskEntries Q.S.sharedSplit.maskRows
      (Q.codes.mask.getD Q.S.sharedSplit.maskCode default).ell Q.S.sharedSplit.answers := by
  unfold sendingsFit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The test gives that every code's message length is a power of two. -/
theorem lengths_of_fit (h : sendingsFit Q = true) :
    VerifiableInference.Desc.Own.lengthsFit Q.codes = true := by
  unfold sendingsFit sendShapeFits at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2.1.1

/-- **Exchange at both sendings, with the test for the premise on shapes.** UNDER Thr. -/
theorem exchange_fit {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (hQ : Plan2 Q sentU layO)
    (h : sendingsFit Q = true) (hN : Function.Injective O.N.tenant) (Cl : Type) :
    Exchange (letters2 Q sentU (fullOver O Q weights rand) Cl).thread 2 ∧
      Exchange (letters2 Q sentU (fullOver O Q weights rand) Cl).thread 5 :=
  exchange_full O weights rand hQ (sendShapes_of_fit h) hN Cl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendShapes_of_fit
#print axioms ProofFile.Honest.K14.free_of_fit
#print axioms ProofFile.Honest.K14.lengths_of_fit
#print axioms ProofFile.Honest.K14.exchange_fit
