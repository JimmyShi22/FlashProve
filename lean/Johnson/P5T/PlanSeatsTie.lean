-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSeatsTie.lean: the seats and the core of the numbers of the table of joints, made at
a public part Z of the IOP as written in Lean, ARE the written ones
(Johnson/P5T/PlanSeatsFull.lean). Two statements with their proofs; nothing is evaluated.

  `seats_written`: under three equations on Z: `planSeats Z Z.D.1 = psFull`,
    `planSeatsAll Z Z.D = seatsAllFull`, `numbersOf (planSeats Z Z.D.1) = N0Full`. The step from
    `Z.D`, which the makers are handed, to `Z.plans` is `pubBy_entries`
    (Johnson/Goal/Numbers/PlanWrittenPlans.lean).
  `seats_in_scope`: **the same in the goals' scope**, from four premises: the scope; the public part
    is made; the verifier's test `madePinnedAt` accepts; the value is laid.

THE THREE EQUATIONS, EACH WITH ITS PAYER: `Z.made.proof = proofSendsFull`: `sends_in_scope` ·
`Z.first.shape = shapeFull`: `first_written_in_scope` with `request_shape_written` ·
`Z.plans = esFull`: `plans_written`, which asks that the value is laid: THIS THIRD ONE IS NO PART OF
`madePinnedAt`: it rests on the entry tests' row 1, on the declared rounds.

Can the premises be met? Only where the public part is made, the test accepts and the value is laid:
the reference run's to show; no theorem. Limits. The core alone: what is laid over it reads the
first chain's sub-protocols. Nothing on soundness.
-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (pubBy_entries plans_written request_shape_written
  madePinnedAt)
open VerifiableInference.PlanWritten.Joined (sends_in_scope first_written_in_scope)

/-- **The seats and the core of the numbers at a public part are the written ones**, under three
equations on that public part. Nothing is evaluated. -/
theorem seats_written {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubBy made st pol lay KL = .ok Z) (hs : Z.made.proof = proofSendsFull)
    (hf : Z.first.shape = shapeFull) (hp : Z.plans = esFull) :
    planSeats Z Z.D.1 = psFull ∧ planSeatsAll Z Z.D = seatsAllFull ∧
      numbersOf (planSeats Z Z.D.1) = N0Full := by
  obtain ⟨d1, d2, d3⟩ := pubBy_entries h
  have e : (Z.D.1.map (·.entry), Z.D.2.1.map (·.entry), Z.D.2.2.map (·.entry)) = esFull :=
    (Prod.ext d1 (Prod.ext d2 d3)).trans hp
  have e1 : Z.D.1.map (·.entry) = esFull.1 := congrArg (·.1) e
  have a : planSeats Z Z.D.1 = psFull := by
    rw [planSeats_at, hs, hf, e1]
    exact psFull_is
  refine ⟨a, ?_, by rw [a]; rfl⟩
  rw [planSeatsAll_at, hs, hf, e]
  exact seatsAllFull_is

/-- **In the goals' scope**, where the public part is made, the verifier's test on the sizes, the
lists of rounds and the sendings accepts, and the value is laid. -/
theorem seats_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D} {r}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    planSeats Z Z.D.1 = psFull ∧ planSeatsAll Z Z.D = seatsAllFull ∧
      numbersOf (planSeats Z Z.D.1) = N0Full := by
  have hZ : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts W.pol W.lay W.KL = .ok Z := h
  obtain ⟨Z', hZ', p1, p2, p3⟩ := plans_written hW hl
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  exact seats_written hZ (sends_in_scope hW h hy)
    ((first_written_in_scope hW h hy).2.2.1.trans request_shape_written)
    (Prod.ext p1 (Prod.ext p2 p3))

end P5T

#print axioms P5T.seats_written
#print axioms P5T.seats_in_scope
