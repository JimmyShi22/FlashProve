-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8Ok.lean: the clauses of `Fmt.Spec.ok`, each under a name, so that no proof has to take the
conjunction apart by place.

A description (`Spec`, Fmt/Rules8.lean) is an argument that the reader of a proof file
(`readChain`) takes beside the file's bytes. `Spec.ok` has the conditions on it that do not look at
a file; where it is false the reader refuses every file.

Why: Fmt/Rules8.lean's `Spec.ok` is one long conjunction of truth values. Whoever reads a clause off
it by its place (the third from the end) has to move whenever a clause is added, wherever it is put.
Here each clause is a theorem "S.ok = true → the clause". When a clause is added, this file alone
follows. The rule numbers are those of the format page (docs/format/FORMAT.md, which comes with the
programs).
No Mathlib.

1. What the file contains. Statements and proofs.

2. What is checked when the file compiles. Only the proofs.

3. Theorems. All but the last two under `h : S.ok = true`.
   `ok_small`: R2.7: within the hash's bounds (`Spec.small`).
   `ok_params`: R4.3: the parameter bytes begin with the version, this plan and this configuration's
     digest.
   `ok_plan`, `ok_entries`: the plan is in order (`Plan.ok`, Fmt/Rules4.lean); the rounds' entries
     are the plan's (`Plan.rounds`).
   `ok_fits`: R6.2: every entry has its kind's draws and no others.
   `ok_rand`: given random bytes are 32.
   `ok_cfg`: the configuration's digest has 32 bytes.
   `ok_round`: a chain has a round.
   `ok_count`, `ok_trees`: R7.13: the count of the trees, and every opened tree's number, stay below
     2^16.
   `ok_shapes`: a tree of the chain's own that is opened more than once has one shape
     (`Spec.ownShapes`).
   `ok_rounds`: every round meets the conditions of `Round.ok` (`roundsOk`, Fmt/Rules8.lean).
   `ok_depth`: R7.16: no opened tree is deeper than 48.
   `ok_salt`: R7.3: the salts' length is one that the format admits.
   `ok_iff`: `Spec.ok` is the conjunction of these fourteen, as propositions.
   Of one round, under `Round.ok`: `Round.ok_sealed_work`: R5.3: a seal has no work.

4. What is not claimed. Anything about a file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8

namespace Fmt
namespace Spec8

/-- the fourteen clauses, as one proposition -/
def All (S : Spec) : Prop :=
  S.small = true ∧
  (S.params.extract 0 (paramsBytes S.plan S.cfg []).size == paramsBytes S.plan S.cfg []) = true ∧
  S.plan.ok = true ∧
  (S.rounds.map (·.entry) == S.plan.rounds) = true ∧
  (S.rounds.all fun r => r.entry.fits r.kind S.plan.samples) = true ∧
  (match S.rand with
    | .given b => b.size == 32
    | _ => true) = true ∧
  (S.cfg.size == 32) = true ∧
  (!S.rounds.isEmpty) = true ∧
  S.firstTree + ((S.rounds.map (·.entry.roots)).sum) < 2 ^ 16 ∧
  (S.rounds.all fun r => r.opens.all fun o => decide (o.1.tree < 2 ^ 16)) = true ∧
  (S.ownShapes.all fun x => S.shapeOf x.1 == some x.2) = true ∧
  roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds = true ∧
  (S.rounds.all fun r => r.opens.all fun o => depthOK o.1.a) = true ∧
  saltLenOK S.plan.salt = true

def ok_iff : Prop := ∀ S : Spec, S.ok = true ↔ All S

end Spec8

theorem ok_iff : Spec8.ok_iff := by
  intro S
  unfold Spec.ok Spec8.All
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact Iff.rfl

section
variable {S : Spec} (h : S.ok = true)
include h

theorem ok_small : S.small = true := ((ok_iff S).mp h).1
theorem ok_params :
    (S.params.extract 0 (paramsBytes S.plan S.cfg []).size == paramsBytes S.plan S.cfg []) = true :=
  ((ok_iff S).mp h).2.1
theorem ok_plan : S.plan.ok = true := ((ok_iff S).mp h).2.2.1
theorem ok_entries : (S.rounds.map (·.entry) == S.plan.rounds) = true := ((ok_iff S).mp h).2.2.2.1
theorem ok_fits : (S.rounds.all fun r => r.entry.fits r.kind S.plan.samples) = true :=
  ((ok_iff S).mp h).2.2.2.2.1
theorem ok_rand : (match S.rand with
    | .given b => b.size == 32
    | _ => true) = true := ((ok_iff S).mp h).2.2.2.2.2.1
theorem ok_cfg : (S.cfg.size == 32) = true := ((ok_iff S).mp h).2.2.2.2.2.2.1
theorem ok_round : (!S.rounds.isEmpty) = true := ((ok_iff S).mp h).2.2.2.2.2.2.2.1
theorem ok_count : S.firstTree + ((S.rounds.map (·.entry.roots)).sum) < 2 ^ 16 :=
  ((ok_iff S).mp h).2.2.2.2.2.2.2.2.1
theorem ok_trees : (S.rounds.all fun r => r.opens.all fun o => decide (o.1.tree < 2 ^ 16)) = true :=
  ((ok_iff S).mp h).2.2.2.2.2.2.2.2.2.1
theorem ok_shapes : (S.ownShapes.all fun x => S.shapeOf x.1 == some x.2) = true :=
  ((ok_iff S).mp h).2.2.2.2.2.2.2.2.2.2.1
theorem ok_rounds : roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds = true :=
  ((ok_iff S).mp h).2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_depth : (S.rounds.all fun r => r.opens.all fun o => depthOK o.1.a) = true :=
  ((ok_iff S).mp h).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem ok_salt : saltLenOK S.plan.salt = true := ((ok_iff S).mp h).2.2.2.2.2.2.2.2.2.2.2.2.2

end

/-- R5.3, off `Round.ok`: a round in order whose verifier's message is a seal has no work. -/
theorem Round.ok_sealed_work {P : Plan} {noRand : Bool} {firstTree : Nat} {after : Bool}
    {sent : Nat} {r : Round} (h : r.ok P noRand firstTree after sent = true)
    (hk : r.kind = .sealed) : r.entry.work = 0 := by
  unfold Round.ok at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, -, c, -⟩ := h
  rw [hk] at c
  simpa using c

end Fmt
