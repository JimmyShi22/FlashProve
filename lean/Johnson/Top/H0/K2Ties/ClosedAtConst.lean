-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/ClosedAtConst.lean: code switching: TWO NAMED TESTS ON THE PLAN ACCEPT AT THE
CONSTANT's OWN LETTERS: where the constant's parameters are the written values. A joining: the two
closed facts are others'. NO SUB-PROTOCOL IMPORTS THIS FILE.
  keptAlign_congr   the test keptAlignB (Johnson/P5T/KeptAlign.lean) reads the
                    numbering arr and, of the numbers, keptOf and sent alone
  keptAlign_const   it accepts at the constant's arr and numbers, at all 25: by align25_full
                    (Johnson/Top/H0/K2Caller/ClosedAt25.lean: by Lean's kernel)
  seats25_const     the test seats25B (Johnson/Top/H0/K2Caller/SeatFitsPlan.lean)
                    accepts at the constant's tenants and codes and the 25 written typed rows: by
                    seats25_full (K2Caller/SeatFitsFull.lean: by Lean's kernel)
CALLED BESIDE: AtWritten (K2Ties/WrittenAt.lean) · PlanWritten.codes_written
(Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean).
LIMITS. The full size alone. AtWritten stands under the first pinned test's accept. The negative
tests stand with the closed facts, in their own files. No soundness is claimed.

-/
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Top.H0.K2Caller.ClosedAt25
import Johnson.Top.H0.K2Caller.SeatFitsFull
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.K2Caller (tableFullLit seats25B seats25_full align25_full)
open P5J (TS)

theorem keptAlign_congr {arr arr' : ℕ → ℕ → ℕ} {N N' : Numbers} {n : ℕ} (ha : arr = arr')
    (hk : N.keptOf = N'.keptOf) (hs : N.sent = N'.sent) :
    P5T.keptAlignB arr N n = P5T.keptAlignB arr' N' n := by
  unfold P5T.keptAlignB
  simp only [ha, hk, hs]

/-- **By place, the old and the new copy of a kept oracle message have one number**, at the
constant's letters. -/
theorem keptAlign_const {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) :
    P5T.keptAlignB (P5J.At.arr Zp) (P5J.At.N Zp cF) 25 = true := by
  rw [keptAlign_congr A.arr A.keptOf A.sent]
  exact align25_full

/-- **The typed rows' shapes are the plan's tenants'**, at the constant's letters. -/
theorem seats25_const {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) :
    seats25B (P5J.At.pseats Zp) (P5J.At.cs Zp) tableFullLit = true := by
  rw [A.pseats, A.cs, VerifiableInference.PlanWritten.codes_written]
  exact seats25_full

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.keptAlign_congr
#print axioms VerifiableInference.Desc.First.K2Ties.keptAlign_const
#print axioms VerifiableInference.Desc.First.K2Ties.seats25_const
