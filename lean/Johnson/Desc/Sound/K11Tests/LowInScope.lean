-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/LowInScope.lean: THE TEST WITH CODE lowAtB N open346 base
(Johnson/Top/H0/MergeLaw/FenceAtBase.lean: "every sampled tenant whose pin is open at the border 346
has its tree among those that the written rows in front of 346 tell") SAYS YES AT ALL PUBLIC FILES
IN THE GOALS' SCOPE, UNDER THE FIRST ENTRY PIN, at the first table's numbers in their own form. It
is the field low of a named condition in other files (Johnson/K11R/) for the merge of the claims on
the committed table (kind K11). Statements and proofs. Four closed facts are by Lean's kernel.

  low_written    at the written core of the numbers (P5T.N0Full) the test says yes
  low_reads      WHAT IT COMPARES THERE: six sampled tenants, in the trees 1, 73, 73, 73, 74, 75: so
                 the test does not pass idly
  low_tight      the negative test: THERE IS NO SLACK: the base is 76 (base346_is); at 75 it says no
  low_blind      WHAT IT DOES NOT SEE: no pin of the committed table's message W and no pin of a
                 kept message is open at 346: of the numbers' fields w and keptOf it says nothing
  low_of_core    the test reads of the numbers four fields alone: sent, keptOf, index, w
  low_in_scope   MAIN

hy IS A PREMISE: the first entry pin (in the entry tests' first thirteen rows). It is not paid here.
s, t, n, ps, told are general: the test does not read what withRows and withTold lay.

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on a
verifier's state. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.FenceAtBase
import Johnson.HB.LLHARD.IdxBelowWritten
import Johnson.P5T.PlanSeatsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item Numbers sampledIn)
open VerifiableInference.Desc.First.MergeLaw (lowAtB open346 treesInFront)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.K13.Law (sampledIn_core)

/-- **At the written core the test says yes.** By the kernel. -/
theorem low_written : lowAtB P5T.N0Full open346 (treesInFront cutFirstFull 346) = true := by
  decide +kernel

/-- What it compares there: six sampled tenants. By the kernel. -/
theorem low_reads : sampledIn P5T.N0Full open346 =
    [(1, 0), (73, 0), (73, 1), (73, 2), (74, 0), (75, 0)] := by decide +kernel

/-- The negative test: one lower than the written base it says no. By the kernel. -/
theorem low_tight : lowAtB P5T.N0Full open346 75 = false := by decide +kernel

/-- What it does not see: no pin of W's and no pin of a kept message is open at 346. By the
kernel. -/
theorem low_blind : (open346.any fun i =>
    match i with
    | .pinV => true
    | .pinKept _ => true
    | _ => false) = false := by decide +kernel

/-- The test reads four fields of the numbers. -/
theorem low_of_core {N N' : Numbers} (h1 : N.sent = N'.sent) (h2 : N.keptOf = N'.keptOf)
    (h3 : N.index = N'.index) (h4 : N.w = N'.w) (O : List Item) (base : ℕ) :
    lowAtB N O base = lowAtB N' O base := by
  unfold lowAtB
  rw [sampledIn_core h1 h2 h3 h4 O]

/-- **THE TEST SAYS YES IN SCOPE, UNDER THE FIRST PIN.** -/
theorem low_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D} {r}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) (s : OnBytes.Params.ReqShape)
    (t : ℕ → ℕ) (n : ℕ) (ps : List Place) (told : List (List Oracle)) :
    lowAtB (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told) open346
      (treesInFront cutFirstFull 346) = true := by
  rw [(P5T.seats_in_scope hW h hy hl).2.2]
  exact (low_of_core (N' := P5T.N0Full) rfl rfl rfl rfl _ _).trans low_written

end LT28.K11Tests

#print axioms LT28.K11Tests.low_written
#print axioms LT28.K11Tests.low_reads
#print axioms LT28.K11Tests.low_tight
#print axioms LT28.K11Tests.low_blind
#print axioms LT28.K11Tests.low_of_core
#print axioms LT28.K11Tests.low_in_scope
