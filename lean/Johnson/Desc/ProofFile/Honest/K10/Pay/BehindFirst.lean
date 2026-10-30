-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/BehindFirst.lean: the closing of each of the 25 segments at the first thread at a return of the maker (`firstThread`,
Honest/Thread/TheFirstThread.lean): two of the five statements that a sub-protocol owes at its border.

  `k10_of_firstClauses`, `firstClauses_of_k10`   at a place of the kind K10 the thread's clause of `keeps` is `K10Keeps` with
                     "the open claims on linear forms pass their tests behind" beside it
  **`ridesPastS_closing_first`**   `RidesPastS` at the border 14 l + `IM.nAt l` + 5
  **`behindS_closing_first`**      `BehindS` there

Premises: l < 25, and h, the head at the return, which carries proofs: the library's head `P5J.AtMgA` at the return's public
part, and that the maker returns A at some filling. The thread's parts, the run's input and Said are letters.

Limits. That a head at a return exists is not shown here. That the thread's invariant holds of any run is not shown; where it holds of none both say nothing. The full size and
the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.BehindCs
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Place KindName)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (K10Keeps)
open P5J (TS)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- At a place of the kind K10 the thread's clause of `keeps` gives `K10Keeps`. -/
theorem k10_of_firstClauses (h : HeadAtReturn files A) (p : Place) (s s' : TS)
    (hk : p.kind = KindName.K10) (hc : kpBy (firstClauses h) p s s') : K10Keeps s s' := by
  -- The clause is a tower of conjunctions with `K10Keeps` innermost on the left.
  exact ((kpBy_at _ hk s s').1 hc).1.1.1.1.1

/-- And it is given by `K10Keeps` with the tests on the open claims on linear forms behind. -/
theorem firstClauses_of_k10 (h : HeadAtReturn files A) (p : Place) (s s' : TS)
    (hk : p.kind = KindName.K10) (K : K10Keeps s s') (hf : formsBehind h.head.𝔇.pubD p s') :
    kpBy (firstClauses h) p s s' := by
  exact (kpBy_at _ hk s s').2 ⟨⟨⟨⟨⟨K, hf⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- **WHAT RIDES PAST A CLOSING, AT THE FIRST THREAD.** -/
theorem ridesPastS_closing_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25) :
    RidesPastS (firstThread h parts w) Said (14 * l + IM.nAt l + 5) :=
  ridesPastS_at_closing h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (k10_of_firstClauses h) Said hl

/-- **BEHIND A CLOSING's STEP, AT THE FIRST THREAD.** -/
theorem behindS_closing_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25) :
    BehindS (firstThread h parts w) Said (14 * l + IM.nAt l + 5) :=
  behindS_closing_head_form h.head A.H parts.script _ _ _ _ _ _ _ _ _ _ w hl
    (fun p s s' _ _ hp hk K hF => firstClauses_of_k10 h p s s' hk K
      (formsBehind_of_form h.head A.H parts.script _ _ _ _ _ _ _ _ _ w hp hF)) Said

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10_of_firstClauses
#print axioms ProofFile.Honest.K10.firstClauses_of_k10
#print axioms ProofFile.Honest.K10.ridesPastS_closing_first
#print axioms ProofFile.Honest.K10.behindS_closing_first
