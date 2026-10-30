-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/GateOfConfigure.lean: where the planner `OnBytes.Params.configure` returns a value, the four
tests that it runs on the public numbers have all said "nothing is missed". Definitions,
statements and proofs. General in the frame lines, the shapes and the value: no size, no public
file.

The setting. `configure l x cfg bits` (OnBytes/Params/Configure.lean) makes, from the frame lines l
and the shapes x, the sizes and the plans of all chains. Before it returns it asks four tests
(OnBytes/Params/Gate.lean, OnBytes/Plan/RangesGate.lean) and rejects where one says "missed":
`missedInTheLinks`, `missedInTheRanges`, `missedOnTheTable`, `missedInTheChecks`. These four render
the programs' ten conditions on the numbers of random entries, of mask entries and others.

Two of the library's names. A "plan" (`Planned`) is a chain's list of rounds with each round's error
bound. "The planner" is, here, the routine `configure` that makes these lists.

What is shown.
  `batchGate`, `onceGate`, `keyParts`: names for the two arguments of the test on the table, as they
    stand in `configure`'s text.
  `Gates l x made …`: the value's six plans are these six, and the four tests say "nothing missed".
  `AsMade`, `asMade_of_configure`: what the four tests do not say and the planner's making does,
    from the library's lemmas on the planner: whose settings the sizes bear, which test on the table
    is a one-time test, and that the key's one-time plan is the routine's own value.
  **`gates_of_configure`**: `configure l x cfg bits = .ok made` gives `Gates` at the value's own
    plans.

Limits.
- It says what the planner ASKED. It holds of every value that the planner returns, and of nothing
  where the planner rejects. That the planner returns a value at any l and x is not shown here.
- The four tests compare numbers that the planner derived itself. What they achieve is not treated:
  nothing on hiding follows from this file.
- The other rejections of `configure` (the key's public values, four conditions on the first chain's
  reader, the security bits) are walked past and not kept.

`Gates` and `AsMade` may be read as part of a goal (that the planner's tests were passed). They
count as none.


-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Plan.PlanListsProof
import OnBytes.Plan.PlanListsConfigure
import OnBytes.Plan.PlanListsKey
import Johnson.Desc.Last.ShapeNoSplit

set_option autoImplicit false

namespace AtPublicFiles.Gate
open OnBytes OnBytes.Params

/-- What the planner's test reads of the test on the table in a batch. -/
def batchGate (x : Shapes) (z : Sized) (shared second : Planned) : TableGate :=
  ⟨z.proof.batch, z.proof.codes, shared, second, x.sub.pendingRows, 0⟩

/-- The parts of all lookups of the key's proof of the ranges. -/
def keyParts (z : Sized) : Nat := sumT (z.key.ranges.x.lookups.map (·.parts.length))

/-- What it reads of the committer's own test on the table. -/
def onceGate (z : Sized) (keyShared keySecond : Planned) : TableGate :=
  ⟨z.key.once, z.key.codes, keyShared, keySecond,
    if keyParts z != 0 then keyParts z else 1, keyParts z⟩

/-- **The planner's four tests have said "nothing is missed"**, at a value made and its
six plans of a proof's and a key's chains. -/
structure Gates (l : Lines) (x : Shapes) (made : Configured)
    (first shared second oneTime keyShared keySecond : Planned) : Prop where
  proof : made.proof = [first, shared, second]
  key : made.key = [oneTime, keyShared, keySecond]
  links : missedInTheLinks l made.sized.proof x.sub first = .ok false
  ranges : Plan.missedInTheRanges made.sized.key = false
  table : missedOnTheTable l (batchGate x made.sized shared second)
    (onceGate made.sized keyShared keySecond) made.sized.link made.sized.entryCodes made.entry =
      false
  checks : missedInTheChecks l x.rangeChecks made.sized.key.once.shape.fold.columns
    made.sized.link.shape.columnsFirst made.sized.proof.batch.batches = false

/-- **What the planner returns has passed the four tests.** -/
theorem gates_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    ∃ first shared second oneTime keyShared keySecond,
      Gates l x made first shared second oneTime keyShared keySecond := by
  unfold configure at h
  obtain ⟨z, -, h₁⟩ := exc_bind h
  clear h
  obtain ⟨proof, -, h₂⟩ := exc_bind h₁
  clear h₁
  obtain ⟨oneTime, -, h₃⟩ := exc_bind h₂
  clear h₂
  obtain ⟨keyShared, -, h₄⟩ := exc_bind h₃
  clear h₃
  obtain ⟨keySecond, -, h₅⟩ := exc_bind h₄
  clear h₄
  obtain ⟨entry, -, h⟩ := exc_bind h₅
  clear h₅
  split at h
  · rename_i first shared second
    obtain ⟨b, hb, h⟩ := exc_bind h
    obtain ⟨g₁, h⟩ := VerifiableInference.Desc.Last.exc_guard_not h
    obtain ⟨g₂, h⟩ := VerifiableInference.Desc.Last.exc_guard_not h
    obtain ⟨g₃, h⟩ := VerifiableInference.Desc.Last.exc_guard_not h
    obtain ⟨g₄, h⟩ := VerifiableInference.Desc.Last.exc_guard_not h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    refine ⟨first, shared, second, oneTime, keyShared, keySecond, rfl, rfl, ?_,
      eq_false_of_ne_true g₂, eq_false_of_ne_true g₃, eq_false_of_ne_true g₄⟩
    rw [← eq_false_of_ne_true g₁]
    exact hb
  · cases h

/-- A plan that was finished and held was finished. -/
theorem finish_of_held {s : Setting} {c : Scope} {y : Planning Unit} {P : Planned}
    (h : finishHeld s c y = .ok P) : finish s c y = .ok P := by
  unfold finishHeld at h
  obtain ⟨q, hq, h⟩ := exc_bind h
  split at h
  · cases h
    exact hq
  · cases h

/-- **What the four tests do not say, and the planner's making does**: the sizes are those that the
planner derives from l and x; both files' settings are the lines'; the test on the table of a proof
is no one-time test, that of a key is one; and the plan of the key's one-time chain is what the
planner's routine returns on the key's sizes. -/
structure AsMade (l : Lines) (x : Shapes) (made : Configured) (oneTime : Planned) : Prop where
  sizes : sized l x = .ok made.sized
  proofSet : made.sized.proof.set = settingOf l
  keySet : made.sized.key.set = settingOf l
  batchMany : made.sized.proof.batch.lines.oneTime = false
  onceOne : made.sized.key.once.lines.oneTime = true
  oneTimePlanned :
    finish made.sized.key.set .once (Plan.oneTimeRounds made.sized.key) = .ok oneTime

/-- From the library's lemmas on the planner. -/
theorem asMade_of_configure {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made)
    {oneTime keyShared keySecond : Planned} (hk : made.key = [oneTime, keyShared, keySecond]) :
    AsMade l x made oneTime := by
  obtain ⟨hz, -, P1, P2, P3, e, h1, -, -, -⟩ := configure_plans h
  obtain ⟨-, s1, s2⟩ := configure_proof_sizes h
  obtain ⟨k1, k2⟩ := Plan.keySized_oneTime (sized_key hz)
  have e1 : P1 = oneTime := by
    rw [hk] at e
    exact (List.cons.inj e).1.symm
  subst e1
  exact ⟨hz, s1, k2, s2, k1, finish_of_held h1⟩

end AtPublicFiles.Gate

#print axioms AtPublicFiles.Gate.gates_of_configure
#print axioms AtPublicFiles.Gate.asMade_of_configure
