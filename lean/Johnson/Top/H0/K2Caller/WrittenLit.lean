-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenLit.lean: the test `SwRow.writtenOK` of WrittenMeets.lean at the
written records of LitRows.lean: it says yes at each of the 5 and the 25 (WrittenLitSmall.lean,
WrittenLitFull.lean: evaluations in Lean's kernel). So the bound of WrittenMeets.lean holds at each.
  written_small_at, written_full_at: `Letters.writtenBelow` at each written record
That the test can say no at these records is WrittenCanFail.lean's and WrittenCanFailFull.lean's.
Limits: written numbers. Those of WrittenMeets.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenLitSmall
import Johnson.Top.H0.K2Caller.WrittenLitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params Iop
open _root_.Run (PQ.RD ckP)
open _root_.Run.PQ (uL)
open scoped ENNReal

/-- **At the 5 switches of the small example.** -/
theorem written_small_at (F : Type) (r : SwRow) (hr : r ∈ tableSmallLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableSmallLit_ok r hr))) (ds : List PQ.RD)
    (hd : WrittenAs r.set .request ds r.specs) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds) (OnBytes.Flat.Held.wsOf ds (allRead ds))
      (Cb.Pv.SendLocRide.R X.caller).shape (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  Letters.writtenBelow F (List.all_eq_true.1 tableSmallLit_ok r hr)
    (List.all_eq_true.1 small_written_ok r hr) X ds hd

/-- **At the 25 switches of the full example.** -/
theorem written_full_at (F : Type) (r : SwRow) (hr : r ∈ tableFullLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))) (ds : List PQ.RD)
    (hd : WrittenAs r.set .request ds r.specs) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds) (OnBytes.Flat.Held.wsOf ds (allRead ds))
      (Cb.Pv.SendLocRide.R X.caller).shape (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) :=
  Letters.writtenBelow F (List.all_eq_true.1 tableFullLit_ok r hr)
    (List.all_eq_true.1 full_written_ok r hr) X ds hd

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.small_written_ok
#print axioms VerifiableInference.Desc.First.K2Caller.full_written_ok
#print axioms VerifiableInference.Desc.First.K2Caller.written_small_at
#print axioms VerifiableInference.Desc.First.K2Caller.written_full_at
