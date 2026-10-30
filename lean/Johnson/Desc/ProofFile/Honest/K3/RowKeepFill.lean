-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowKeepFill.lean: the two letters of the row that passes its tables
on (`Keeps`, Honest/K3/RowKeep.lean), filled: the jobs with a kept state of the five sorts of stage,
and the maker of the store; and the lot's letters at this filling. Definitions with code, and two
theorems on which stage has which job.

Terms. Honest/K3/GLOSSARY.md.

What is defined.
  `fastKeeps R row a`: at each stage that is a masked sumcheck the job with a kept state whose
    earlier job is `jobOfAt` at `fastJobs a.face row`; none at a stage that sends nothing; the store
    is `storeAt R row a`. Here row stays a letter: the table's row, of the shift and the row's
    number.
  `fastFillKeep row wit`: the lot's letters (`FillKeep`, Honest/K3/LotKeep.lean): at each site
    `fastKeeps` at `theReads`, at the site's rows and at the site's place. The rows and the reader
    of the chain's input stay letters.

What is shown.
  `fastKeeps_none`: at a stage without a call there is no job.
  `fastKeeps_some`: at a stage with the call k there is a job, and its earlier job is `jobOfAt` at
    that stage and at k.

Hypotheses that remain. `h`: the stage has no call (in `fastKeeps_none`), or the call k (in
`fastKeeps_some`).

Imported. The five sorts' files and Honest/K3/StoreMake.lean; Honest/K3/LotRow.lean for `theReads`.
The frame's files lie beneath them.

Users. Honest/K3/LotInstKeep.lean; Honest/K3/Law/Keep/SameRounds.lean. Meant for a filling of the
honest prover.

Limits. Nothing here says that the jobs meet `KeepJob.FaithfulOn` or that the store holds what the
jobs would make: see the sorts' files and Honest/K3/Law/Keep/. `Fast.rowOfFace` is not laid for row
here: one run by Lean's evaluator at a site of the release's small example took 316,783 ms for 64
rows of it (synthetic cells; the run's print is not in the library).

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepTab
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepTie
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepLeaves
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepBits
import Johnson.Desc.ProofFile.Honest.K3.StoreMake
import Johnson.Desc.ProofFile.Honest.K3.LotKeep
import Johnson.Desc.ProofFile.Honest.K3.LotRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)
open VerifiableInference.Desc.Part.MaskedSum (Call)

/-- **The row's two letters, filled.** -/
def fastKeeps (R : Reads) (row : E → Nat → E) (a : At) : Keeps :=
  { job := fun
      | .tie 0 => some (tie0Keep R row a)
      | .tie (s + 1) => some (tieKeep R row a s)
      | .split i => some (splitKeep R row a i)
      | .key i k => some (keyKeep R row a i k)
      | .tab l => some (tabKeep R row a l)
      | .leaves => some (leavesKeep R row a)
      | .bits => some (bitsKeep R row a)
      | _ => none
    store := storeAt R row a }

/-- At a stage without a call there is no job. -/
theorem fastKeeps_none (R : Reads) (row : E → Nat → E) (a : At) (s : Stage)
    (h : s.call a.face = none) : (fastKeeps R row a).job s = none := by
  cases s with
  | tie n => cases n <;> simp [Stage.call] at h
  | split i => simp [Stage.call] at h
  | key i k => simp [Stage.call] at h
  | tab l => simp [Stage.call] at h
  | leaves => simp [Stage.call] at h
  | bits => simp [Stage.call] at h
  | shift => rfl
  | alpha => rfl
  | join => rfl
  | keyLine i k => rfl
  | tabLine l => rfl
  | zero => rfl

/-- At a stage with the call k there is a job, and its earlier job is `jobOfAt` at that stage and at
k. -/
theorem fastKeeps_some (R : Reads) (row : E → Nat → E) (a : At) (s : Stage) (k : Call)
    (h : s.call a.face = some k) :
    ∃ J, (fastKeeps R row a).job s = some J ∧
      J.base = jobOfAt R (fastJobs a.face row).asked a s k := by
  cases s with
  | tie n =>
    cases n with
    | zero => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
    | succ n => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | split i => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | key i k' => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | tab l => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | leaves => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | bits => obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩
  | shift => simp [Stage.call] at h
  | alpha => simp [Stage.call] at h
  | join => simp [Stage.call] at h
  | keyLine i k' => simp [Stage.call] at h
  | tabLine l => simp [Stage.call] at h
  | zero => simp [Stage.call] at h

/-- **The lot's letters at this filling.** Here row gives each site's table, and wit each site's
reader of the chain's input. -/
def fastFillKeep {W : Type} (row : Site → E → Nat → E) (wit : Site → W → Ask) : FillKeep W :=
  { keeps := fun s => fastKeeps theReads (row s) s.at_
    wit := wit }

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.fastKeeps_none
#print axioms ProofFile.Honest.K3.fastKeeps_some
