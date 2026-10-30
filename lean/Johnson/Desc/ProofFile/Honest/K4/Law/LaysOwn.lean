-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LaysOwn.lean

Limits. CONDITIONAL: on the seat (`K4Sits`): `k4Sits_head` (Law/SeatedHead.lean) has the seat at the
first chain's thread under the library's hypothesis `AtMgA` and `LaidK4`. The threads' own list of
clauses (`csHead`, Honest/Thread/CsHead.lean) holds this clause at each group g < 12, from the
border 28 g + 5 to the border 28 g + 10. THAT IT STAYS past the members behind K4's (`StaysBy`) is
not shown: it hangs on these members' clauses of keeps. It says that something has been heard,
nothing of what. Nothing on soundness, on completeness or on any other property.
No property is claimed.

What is here. A clause for a thread's parameter rides, in the frame's own form (`RiderCl`,
Honest/Thread/Riders.lean): the state holds what the layers' own rounds (kind K4) have heard. And
that K4's member lays it. A definition, and three statements with their proofs.

Which member lays it: K4's, the member number b. Who is meant to spend it, and where last: as
Law/FreeSlotRun.lean has it, K4's own run behind the batching, "free-slot", rejects where nothing
has been heard, and its statement asks of the state behind a segment's batching that something has
been: so that is the last border at which the clause is spent.

  `riderOwn lo hi`: from the border lo to the border hi: the state's reading own? returns something.
  `riderOwn_iff`: that sentence is: own?.isSome = true.
  `k4_lays_own`: the member number b lays riderOwn lo hi, in the frame's form LaysAt: at every lo
      and hi: whoever lays the thread chooses them.
  `k4_laysS_own`: the same in the form LaysAtS: a call of the frame's `laysAtS_of`.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.KeepsStep
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block OpenedColumn Claim First.S)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **What K4 has heard is there**, from the border lo to the border hi. This defines a clause; the
definition claims nothing. -/
def riderOwn (lo hi : Nat) : RiderCl W First.S :=
  ⟨lo, hi, fun _ _ s => ∃ o, s.own? = some o⟩

/-- The clause's sentence, as a test: the reading own? is there. -/
theorem riderOwn_iff (lo hi c : Nat) (w : W) (s : First.S) :
    (riderOwn (W := W) lo hi).prop c w s ↔ s.own?.isSome = true :=
  Option.isSome_iff_exists.symm

variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {p : Par}

/-- **K4's member lays that clause**, at every lo and hi. CONDITIONAL: on the seat. -/
theorem k4_lays_own (hSit : K4Sits T b p) (lo hi : Nat) : LaysAt T b (riderOwn lo hi) := by
  intro blk hblk k s m E ds y cols s' _ _ hS
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨-, _, _, o, -, -, ho, -⟩ := k4_keeps hdec
  exact ⟨o, ho⟩

/-- The same from the pair of the thread's sentence and what has been said. -/
theorem k4_laysS_own (Said : Nat → Coins Bk → Mid W X → Prop) (hSit : K4Sits T b p)
    (lo hi : Nat) : LaysAtS T Said b (riderOwn lo hi) :=
  laysAtS_of T Said (k4_lays_own hSit lo hi)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.riderOwn_iff
#print axioms ProofFile.Honest.K4.k4_lays_own
#print axioms ProofFile.Honest.K4.k4_laysS_own
