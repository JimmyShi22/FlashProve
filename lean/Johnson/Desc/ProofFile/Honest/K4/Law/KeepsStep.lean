-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/KeepsStep.lean: CONDITIONAL. Two definitions of propositions,
and statements with their proofs.

What is here. K4's CLAUSE OF A THREAD's PARAMETER `keeps` WITH «NO MARK BEHIND» INSIDE IT, AND THAT
CLAUSE FROM THE WHOLE MEMBER's ACCEPTING STEP. K4 is the sub-protocol of the feed-forward layers'
own rounds.

  `K4KeepsM s s'`   `K4Keeps s s'` (Law/Keeps.lean) and s'.failed = none. It takes no parameter: the
      clause is one for all of K4's places.
  `K4NoMark T b`   a hypothesis: where the member number b of T's flat list steps to s', s' bears no
      mark.
  `k4_keepsM_step`   **under `K4Sits` (Law/Sits.lean) and K4NoMark: wherever the member's own step
      accepts from s to s' (`StepYes`, Johnson/Top/H0/Walk/Reach.lean): K4KeepsM s s'.**
  `keepsM_st_out`, `keepsM_pending`, `keepsM_reply`   what the clause gives to whoever carries a
      sentence on the state past the member: the statement and what goes out are as they were: so
      the number of pending rows and the reply.

Called: `k4_keeps` (Law/Keeps.lean, handed in with this file).

Kin. Another kind's clause with «no mark» inside: `K13Keeps`
(Johnson/Desc/K13/Honest/KeepsM3.lean).

Not shown here. That the two hypotheses hold at a description: Law/SitsAt.lean draws both from one
equation on the member. WHAT THE CLAUSE DOES NOT GIVE: s'.here = s.here: K4's step lays the ledger
and what it has heard into the open layers' segment.
Following import lines, and stopping unopened at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its imports reach 2
modules under Johnson/Bridge/ and none of the others; what lies behind these is not counted. Nothing
on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Keeps
import Johnson.Desc.ProofFile.Honest.K4.Law.Sits
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Claim First.S)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **K4's clause of keeps, with «no mark behind» inside.** This defines a proposition on two
states; the definition claims nothing. -/
def K4KeepsM (s s' : First.S) : Prop := K4Keeps s s' ∧ s'.failed = none

/-- **Behind the member's step the state bears no mark.** This defines a hypothesis; the definition
claims nothing. -/
def K4NoMark (T : Thread Bk First.S Claim V W X Pb) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ s rs cols s' n, blk.step T.ft s rs cols = .ok (s', n) →
    s'.failed = none

/-- **The clause, from the whole member's accepting step.** CONDITIONAL: on the two hypotheses on
the member. -/
theorem k4_keepsM_step {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {p : Par}
    (hSit : K4Sits T b p) (hM : K4NoMark T b) :
    ∀ blk, T.bs[b]? = some blk → ∀ s s', StepYes T.ft blk s s' → K4KeepsM s s' := by
  intro blk hblk s s' hy
  obtain ⟨R, c, _, e⟩ := hy
  obtain ⟨_, hd⟩ := hSit blk hblk s R c s' _ e
  exact ⟨k4_keeps hd, hM blk hblk s R c s' _ e⟩

/-- The statement and what goes out are as they were. -/
theorem keepsM_st_out {s s' : First.S} (h : K4KeepsM s s') : s'.st = s.st ∧ s'.out = s.out :=
  ⟨h.1.1.st, h.1.1.out⟩

/-- As many rows are pending as were. -/
theorem keepsM_pending {s s' : First.S} (h : K4KeepsM s s') :
    s'.out.pending.length = s.out.pending.length := by
  rw [h.1.1.out]

/-- The reply is as it was. -/
theorem keepsM_reply {s s' : First.S} (h : K4KeepsM s s') : s'.out.reply = s.out.reply := by
  rw [h.1.1.out]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4KeepsM
#print axioms ProofFile.Honest.K4.K4NoMark
#print axioms ProofFile.Honest.K4.k4_keepsM_step
#print axioms ProofFile.Honest.K4.keepsM_st_out
#print axioms ProofFile.Honest.K4.keepsM_pending
#print axioms ProofFile.Honest.K4.keepsM_reply
