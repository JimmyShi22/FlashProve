-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/WrittenOfPins.lean: the twelve equations of Written Z x
(Johnson/Goal/Numbers/WrittenAtZ.lean) at the public part
Z that the written description itself makes (ProofFile.pubBy), from what other files' laws give in the
goals' scope: five of the twelve are struck; one comes down to a closed sentence on the written
entries; six are left, each with a named payer.
  entries₁_of_plans, entries₂_of_plans: where the plan's own entries are the written lists'
      (plans_written: Johnson/Goal/Numbers/PlanWrittenPlans.lean): the two stretches
  pubBy_cuts: what pubBy returns has, as its table of steps, cutOf of the first plan's entries
  startOf, fromOf_eq, start_of_cuts: so the number of the round at which the batching starts is a
      function of the plan's own entries alone
  setAt_eq: the written setting setAt (Johnson/Desc/K12/Law/Sizes/StagesFull.lean) is recordSet
  written_of_pins: Written Z x, at Z := what pubBy returns, from: AtFull Z.p.chains.made
      (Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean; in scope by other files' laws), the two
      equations on the plans, AND: start: A CLOSED SENTENCE: (cutOf ‹the written entries›).map
      startOf = some 48270; rows, lin, slots (the first chain's parameters as read back), codes,
      shape (the sized proof): booked to the door's two pins; before (a message is fixed before the
      point): the block's own test on the plan asks it

What is not claimed. THE CLOSED SENTENCE start: true by a run whose print is not in this library
(the value: 48270); Lean's kernel does not walk it: cutOf takes the length of lists of 48,293 names
by a recursion that is not a loop, too deep for the kernel; a law on cutOf (the steps in front take
just the rounds in front) would pay it: typed by nobody. The five and the one. That AtFull or the
plans' equations hold: other files' laws. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.WrittenAtZ
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (Cut cutOf)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K13.Law (stretch)
open H2K.Sizes (AtFull)
open H2K.Member (setAt)

theorem entries₁_of_plans {es : List Fmt.Entry} (h : es = dryProofFull.1.map (·.1.entry))
    (i n : ℕ) : (es.drop i).take n = (stretch dryProofFull.1 i n).map (·.1) := by
  subst h
  unfold stretch
  rw [List.map_map, ← List.map_drop, ← List.map_take]
  rfl

theorem entries₂_of_plans {es : List Fmt.Entry} (h : es = dryProofFull.2.1.map (·.1.entry))
    (n : ℕ) : es.take n = (dryProofFull.2.1.take n).map (·.1.entry) := by
  subst h
  rw [← List.map_take]

/-- **The table of steps in what pubBy returns.** -/
theorem pubBy_cuts {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubBy made st pol lay KL = .ok Z) : cutOf Z.plans.1 = some Z.cuts := by
  unfold ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := exc_bind h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨D, _, h⟩ := exc_bind h
    obtain ⟨told, _, h⟩ := exc_bind h
    obtain ⟨depth, _, h⟩ := exc_bind h
    obtain ⟨cuts, hc, h⟩ := exc_bind h
    obtain ⟨s₀, _, h⟩ := exc_bind h
    cases h
    show cutOf m.p.chains.proof.first.given.rounds = some cuts
    cases hq : cutOf m.p.chains.proof.first.given.rounds with
    | none =>
      rw [hq] at hc
      cases hc
    | some c =>
      rw [hq] at hc
      exact congrArg some (Except.ok.inj hc)

/-- The number of the rounds before the step "M.0.call"; 0 where there is none. -/
def startOf (C : List Cut) : ℕ :=
  (if (C.any fun c => c.look == "M.0.call") = true then
    some ((C.takeWhile fun c => c.look != "M.0.call").foldl (fun n c => n + c.take) 0)
  else none).getD 0

theorem fromOf_eq (Z : ProofFile.Pub) : VerifiableInference.Desc.K13.fromOf Z = startOf Z.cuts := rfl

/-- So the number hangs on the plan's own entries alone. -/
theorem start_of_cuts {Z : ProofFile.Pub} (hc : cutOf Z.plans.1 = some Z.cuts) :
    (cutOf Z.plans.1).map startOf = some (VerifiableInference.Desc.K13.fromOf Z) := by
  rw [hc, fromOf_eq]
  rfl

theorem setAt_eq : setAt = recordSet := by decide +kernel

/-- **Written at the description's own public part**, from other files' laws and five premises.
-/
theorem written_of_pins {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubBy made st pol lay KL = .ok Z) (hA : AtFull Z.p.chains.made)
    (h1 : Z.plans.1 = dryProofFull.1.map (·.1.entry))
    (h2 : Z.plans.2.1 = dryProofFull.2.1.map (·.1.entry)) {x : LinSized}
    (hx : realSized = some (x, codesFull2))
    (rows : Z.first.pendingRows = 13) (lin : Z.first.lin = x.shape)
    (slots : 2 ^ Z.first.binding.logLeaves ≤ 64)
    (start : (cutOf (dryProofFull.1.map (·.1.entry))).map startOf = some 48270)
    (codes : Z.p.chains.made.sized.proof.codes = codesFull2)
    (shape : Z.p.chains.made.sized.proof.batch.shape = x.shape)
    (before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ []) :
    Written Z x :=
  have hs : VerifiableInference.Desc.K13.fromOf Z = 48270 := by
    have e := start_of_cuts (pubBy_cuts hZ)
    rw [h1, start] at e
    exact (Option.some.inj e).symm
  have e1 := entries₁_of_plans h1 48270 (2 + x.shape.kCol)
  ⟨rows, lin, work_of_entries hx hs e1, hA.setP.trans setAt_eq, codes, shape, hA.later, hs, e1,
    entries₂_of_plans h2 8, before, slots⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.entries₁_of_plans
#print axioms Desc.K14.Law.entries₂_of_plans
#print axioms Desc.K14.Law.pubBy_cuts
#print axioms Desc.K14.Law.start_of_cuts
#print axioms Desc.K14.Law.setAt_eq
#print axioms Desc.K14.Law.written_of_pins
