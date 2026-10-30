-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Written/MadeOfSized.lean: six of the seven written priced plans follow from the written
sizes. Wherever the planner's routine `configure` (OnBytes/Params/Configure.lean) returns a record
whose sizes are `writtenSized` (Johnson/Goal/Written/Made.lean), at whatever lines, shapes, digest
and bits, that record's plans for the key file and the entry file, and its second and third plan for
the proof file, are the written ones. No hash is named, and the digest is a letter.

How. By `configure_plans` (OnBytes/Plan/PlanListsConfigure.lean) and `configure_proofPlans`
(OnBytes/Plan/PlanListsProof.lean) each of the seven plans is what one routine returns at the
record's own sizes. At the written sizes six of these calls have closed arguments. Lean's kernel
evaluates five of them whole, and of the key file's first the list of its rounds, and holds each
against the written plan: the setting, and all seven fields of every round. One of the six
evaluations is made here; the others are in the files named below.

Definitions.
  `samePlan k P Q`: a test with code: two plans have one setting and, in one walk, the same rounds.
  `SixOfSized`: the closed statement.
Statements.
  `samePlan_eq`: a yes gives P = Q. A tool.
  `entry_written`: the planner's routine for an entry file at the written link returns
    `pricedEntryFull`: a closed equation. The five others: for the key file `first_written`
    (Johnson/Goal/Numbers/KeyFirstListed.lean), `shared_written`, `second_written`
    (Johnson/Goal/Numbers/KeyLaterListed.lean); for the proof file `proof_shared_written`,
    `proof_second_written` (Johnson/Desc/Ok/NumberPrices/ProofLaterListed.lean).
  `sixOfSized : SixOfSized`. By an evaluation in Lean's kernel (`decide +kernel`): `ride_entry`.

What of OnBytes/Model/ is used: nothing by name.

Limits. The proof file's first plan is not reached: its routine reads the sub-proofs' own routines,
which are no part of the sizes. That `configure` returns, and that it returns these sizes, is a
premise: for the key file's sizes it is a theorem in the goals' scope (`key_eq_at_scope`,
Johnson/Goal/PlanValues/KeyFullAtScope.lean), which speaks of the program's planner and so of the
format's hash by name; for the proof file's it is shown nowhere. The proof file's written plans
stand on prints of the library's own planner (see the head of
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean). `entry_written` has a like in another file of the
library, over other imports. Nothing says that an error bounds a count. Nothing on soundness.

-/
import Johnson.Goal.Written.Made
import Johnson.Goal.Numbers.KeyLaterListed
import Johnson.Goal.Numbers.KeyFirstListed
import Johnson.Desc.Ok.NumberPrices.ProofLaterListed
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference VerifiableInference.Number.ByRuns VerifiableInference.PlanWritten
open OnBytes OnBytes.Params Johnson.G Johnson.G.Runs Johnson.G.MadeFree Lk6.AtPlan

/-- Two plans have one setting and, in one walk, the same rounds. -/
def samePlan (k : ℕ) (P Q : Planned) : Bool :=
  decide (P.set = Q.set) &&
    sameBy sameRound k (P.rounds.map fun r => (1, r)) (Q.rounds.map fun r => (1, r))

theorem samePlan_eq {k : ℕ} {P Q : Planned} (h : samePlan k P Q = true) : P = Q := by
  have c := Bool.and_eq_true_iff.1 h
  have e1 : P.set = Q.set := of_decide_eq_true c.1
  have f := (sameBy_sound sameRound k _ _ c.2).imp fun _ _ H => sameRound_eq H
  rw [expand_ones, expand_ones] at f
  have e2 : P.rounds = Q.rounds := eq_of_forall2 f
  obtain ⟨s, rs⟩ := P
  obtain ⟨t, qs⟩ := Q
  have e1' : s = t := e1
  have e2' : rs = qs := e2
  rw [e1', e2']

/-! ## A closed equation -/

set_option maxRecDepth 1000000 in
theorem ride_entry :
    ((finishHeld recordSet .once (linkPlan writtenLink)).toOption.any fun P =>
      samePlan 200 P pricedEntryFull) = true := by
  decide +kernel

/-- **Its routine for an entry file, at the written link, returns the entry file's written
plan.** -/
theorem entry_written :
    finishHeld recordSet .once (linkPlan writtenLink) = .ok pricedEntryFull := by
  have h := ride_entry
  cases hP : finishHeld recordSet .once (linkPlan writtenLink) with
  | error e =>
    rw [hP] at h
    cases h
  | ok P =>
    rw [hP] at h
    have h' : samePlan 200 P pricedEntryFull = true := h
    rw [samePlan_eq h']

/-! ## Six of the seven plans follow from the sizes -/

/-- Wherever `configure` returns a record with the written sizes, six of its seven plans are the
written ones. -/
def SixOfSized : Prop :=
  ∀ (l : Lines) (x : Shapes) (cfg : ByteArray) (bits : ℕ) (made : Configured),
    configure l x cfg bits = .ok made → made.sized = writtenSized →
      made.key = writtenMade.key ∧ made.entry = writtenMade.entry ∧
        ∃ F, made.proof = [F, proofThree.B.plan, proofThree.C.plan] ∧
          firstPlan proofSizedFull x.sub = .ok F

/-- **It holds.** -/
theorem sixOfSized : SixOfSized := by
  intro l x cfg bits made h hs
  obtain ⟨_, _, P1, P2, P3, ek, a1, a2, a3, ae⟩ := configure_plans h
  obtain ⟨F, S2, S3, ep, b1, b2, b3⟩ := configure_proofPlans h
  rw [hs] at a1 a2 a3 ae b1 b2 b3
  have k1 : P1 = keyThree.A.plan := first_written a1
  have k2 : P2 = keyThree.B.plan := Except.ok.inj (a2.symm.trans shared_written)
  have k3 : P3 = keyThree.C.plan := Except.ok.inj (a3.symm.trans second_written)
  have ke : made.entry = pricedEntryFull := Except.ok.inj (ae.symm.trans entry_written)
  have p2 : S2 = proofThree.B.plan := Except.ok.inj (b2.symm.trans proof_shared_written)
  have p3 : S3 = proofThree.C.plan := Except.ok.inj (b3.symm.trans proof_second_written)
  refine ⟨?_, ke, F, ?_, b1⟩
  · rw [ek, k1, k2, k3]
    rfl
  · rw [ep, p2, p3]

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.samePlan_eq
#print axioms VerifiableInference.PlanWritten.Joined.ride_entry
#print axioms VerifiableInference.PlanWritten.Joined.entry_written
#print axioms VerifiableInference.PlanWritten.Joined.sixOfSized
