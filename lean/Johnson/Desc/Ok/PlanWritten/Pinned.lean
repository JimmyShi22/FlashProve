-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/Pinned.lean: over Johnson/Desc/Ok/PlanWritten/Rounds.lean: the laws of a
second test on what the planner has made, beside `planIsWritten`: `planPinnedFull`: AT THE FULL
SIZE's KEY the six lists of rounds and the stored table's depth are the written ones; AT EVERY OTHER
KEY IT SAYS YES.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL AT THE PLANNER: rules for all m, or for all files.
None speaks of a description of the protocol.

Why. `planIsWritten` says no at every plan but the two written sets, so a description that asked it
would refuse every run at another small example. Theorems at the written numbers are claimed in the
goals' scope alone, and there the key is the full size's (`key_in_scope`,
Johnson/Goal/Numbers/PlanWrittenScope.lean). So a test that pins the plan at that key alone gives in
scope what `planIsWritten` gives, and turns nothing at another key.

Definitions, statements and proofs.
  `planPinnedFull m` (defined in Johnson/Desc/Ok/PlanWritten/Test.lean): if `keyOf m = fullKey` then
    `planIs (dryKeyFull, dryProofFull) 32 m`, else true.
  `pinnedFull_yes`: at the full size's key a yes says: the rounds are the six written lists of the
    full size and the depth is 32. `pinnedFull_of_full`: the way back, AT ANY KEY: these rounds and
    this depth give a yes. `pinnedFull_other`: at another key it says yes.
    `planPinnedFull_atDigest`: it does not hang on the digest. By definition.
    `pinnedFull_of_written`: where `planIsWritten` says yes, it says yes: it is the laxer of the
    two.
  TEETH, all at the full size's key. `pinnedFull_no`: it says no wherever the rounds and the depth
    are not these. `pinnedFull_plant`: A PLANT IS REFUSED: if the rounds of m are the written lists
    with one number changed, it says no. `pinnedFull_shallow`: with 31 for one number of the key
    file's shape it says no. `pinnedFull_refusal`: where the rounds are not made it says no.
  `pinnedFull_of_ok`: a yes of the test at three files (`roundsOk` at the written lists and 32: the
    first answer of a ride of Johnson/Desc/Ok/PlanWritten/Rounds.lean) gives: `madeOf` returns, at
    the format's own digest, and `planPinnedFull` says yes of what it returns.
  `pinnedLines`, `ridePinned note pol lay KL`: FOR A RUN: three named Bools, with ONE call of the
    planner: the test itself, of what is made at 32 zero bytes; that the key is the full size's; the
    plant: the test at `shallow m`. `of_ridePinned`: what the answers true, true give.

What of OnBytes/Model/ and OnBytes/Tie/ is used: no more than
Johnson/Desc/Ok/PlanWritten/Rounds.lean names.

Limits. WHAT BINDS THE KEY: `keyOf m` reads three fields of the strict scan of the parameter file in
the planner's public part (`m.p.X.P.h`); of an m that `madeOfAt` returns they are the scan of the
PUBLIC parameter file (`Tie.plannedAt_scan`, OnBytes/Tie/PlanAtPolicy.lean): no byte of a key file,
an entry file or a proof file is read. IT PINS NOTHING OUTSIDE THE FULL SIZE's KEY: at another key
it says yes of every m, also where the rounds are not made. IF IT IS LAID AMONG A DESCRIPTION's
TESTS ON ITS PLAN, that description accepts, at the sizes L = 48, d = 5120, V = 202048, only a plan
whose six lists of rounds and stored table's depth are the written ones; at other sizes it is what
it was, and nothing is proved there. It is laid nowhere by this file. What it does not compare at
the full size's key: as in Johnson/Desc/Ok/PlanWritten/Rounds.lean (each plan's six settings, the
entry RECORD, the entry file's rounds, the errors' numbers, sizes and codes but for the depth), and
of what was made beside the plans: the planner's public part but for the three sizes, the links, the
seven strings of parameter bytes, and that the plans as read back are the plans as made. No second
witness: the written lists were printed from this library's own planner. The teeth's premises on m
are shown of no m that a planner made. The ride was run by nobody known to this file. Nothing on
soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number

/-- **At the full size's key a yes says: the six written lists of the full size, and the depth
32.** -/
theorem pinnedFull_yes {m : Made} (hk : keyOf m = fullKey) (h : planPinnedFull m = true) :
    roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32 := by
  unfold planPinnedFull at h
  rw [if_pos hk] at h
  exact (planIs_iff _ _ m).1 h

/-- The way back, at any key. -/
theorem pinnedFull_of_full {m : Made} (hr : roundsAt m = .ok (dryKeyFull, dryProofFull))
    (hd : depthOf m = .ok 32) : planPinnedFull m = true := by
  unfold planPinnedFull
  split
  · exact (planIs_iff _ _ m).2 ⟨hr, hd⟩
  · rfl

/-- At another key it says yes. -/
theorem pinnedFull_other {m : Made} (hk : keyOf m ≠ fullKey) : planPinnedFull m = true := by
  unfold planPinnedFull
  rw [if_neg hk]

/-- It does not hang on the digest. By definition. -/
theorem planPinnedFull_atDigest (m : Made) (c : ByteArray) :
    planPinnedFull (atDigest m c) = planPinnedFull m := rfl

/-- Where `planIsWritten` says yes, it says yes. -/
theorem pinnedFull_of_written {m : Made} (h : planIsWritten m = true) :
    planPinnedFull m = true := by
  by_cases hk : keyOf m = fullKey
  · exact pinnedFull_of_full (full_of_yes hk h).1 (full_of_yes hk h).2
  · exact pinnedFull_other hk

/-- At the full size's key it says no wherever the rounds and the depth are not these. -/
theorem pinnedFull_no {m : Made} (hk : keyOf m = fullKey)
    (hn : ¬ (roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32)) :
    planPinnedFull m = false := by
  cases h : planPinnedFull m with
  | false => rfl
  | true => exact absurd (pinnedFull_yes hk h) hn

/-- **A tooth: A PLANT IS REFUSED**, at the full size's key. -/
theorem pinnedFull_plant {m : Made} (hk : keyOf m = fullKey) (h : roundsAt m = .ok bentWork) :
    planPinnedFull m = false :=
  pinnedFull_no hk fun x => bent_ne.1 (Except.ok.inj (h.symm.trans x.1))

/-- A tooth: with 31 for one number of the key file's shape, at the full size's key. -/
theorem pinnedFull_shallow {m : Made} (hk : keyOf m = fullKey) :
    planPinnedFull (shallow m) = false :=
  pinnedFull_no (m := shallow m) hk fun x => by
    have e : (32 : ℕ) = 31 := depthOf_val x.2
    exact absurd e (by decide)

/-- A tooth: where the rounds are not made, at the full size's key. -/
theorem pinnedFull_refusal {m : Made} {e : String} (hk : keyOf m = fullKey)
    (h : roundsAt m = .error e) : planPinnedFull m = false :=
  pinnedFull_no hk fun x => by
    have c := h.symm.trans x.1
    cases c

/-- **A yes of the test at three files gives a yes of `planPinnedFull` of what `madeOf`
returns.** -/
theorem pinnedFull_of_ok {pol lay KL : ByteArray}
    (h : roundsOk (dryKeyFull, dryProofFull) 32 pol lay KL = true) :
    ∃ m, madeOf pol lay KL = .ok m ∧ planPinnedFull m = true := by
  obtain ⟨m, hm, hp⟩ := planIs_own (roundsAre_of_ok h)
  exact ⟨m, hm, pinnedFull_of_full ((planIs_iff _ _ m).1 hp).1 ((planIs_iff _ _ m).1 hp).2⟩

/-! ## A ride for this test -/

/-- Of what is made: the test; that the key is the full size's; the plant (the test at `shallow m`).
At a refusal all three are false, and the first line holds the refusal's words. -/
def pinnedLines (note : String) (r : Except String Made) : List (String × Bool) :=
  match r with
  | .ok m =>
    [(note ++ ": to say true: planPinnedFull of what is made at 32 zero bytes", planPinnedFull m),
      ("to say true: its key is the full size's", decide (keyOf m = fullKey)),
      ("the plant, to say false: planPinnedFull with 31 for one number of the key file's shape",
        planPinnedFull (shallow m))]
  | .error e => [(note ++ ": refused: " ++ e, false), ("the key", false), ("the plant", false)]

/-- **FOR A RUN**: three named Bools, with one call of the planner. note: a string that the first
line gives back (why: the head of Johnson/Desc/Ok/PlanWritten/Rounds.lean). -/
@[noinline] def ridePinned (note : String) (pol lay KL : ByteArray) : List (String × Bool) :=
  pinnedLines note (madeOfAt pol lay KL Fmt.zero32)

/-- **What a ride with the answers true, true gives**: something is made at the anchor, it has the
full size's key, the test says yes of it, so its rounds are the six written lists and its depth is
32. The third answer is then foretold by `pinnedFull_shallow`. -/
theorem of_ridePinned {note : String} {pol lay KL : ByteArray}
    (h : ((ridePinned note pol lay KL).map Prod.snd).take 2 = [true, true]) :
    ∃ m, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ keyOf m = fullKey ∧ planPinnedFull m = true ∧
      roundsAt m = .ok (dryKeyFull, dryProofFull) ∧ depthOf m = .ok 32 := by
  unfold ridePinned pinnedLines at h
  split at h
  · rename_i m hm
    obtain ⟨h1, h⟩ := List.cons.inj h
    obtain ⟨h2, _⟩ := List.cons.inj h
    exact ⟨m, hm, of_decide_eq_true h2, h1, pinnedFull_yes (of_decide_eq_true h2) h1⟩
  · obtain ⟨h1, _⟩ := List.cons.inj h
    cases h1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.of_ridePinned
#print axioms VerifiableInference.PlanWritten.pinnedFull_yes
#print axioms VerifiableInference.PlanWritten.pinnedFull_of_full
#print axioms VerifiableInference.PlanWritten.pinnedFull_other
#print axioms VerifiableInference.PlanWritten.planPinnedFull_atDigest
#print axioms VerifiableInference.PlanWritten.pinnedFull_of_written
#print axioms VerifiableInference.PlanWritten.pinnedFull_no
#print axioms VerifiableInference.PlanWritten.pinnedFull_plant
#print axioms VerifiableInference.PlanWritten.pinnedFull_shallow
#print axioms VerifiableInference.PlanWritten.pinnedFull_refusal
#print axioms VerifiableInference.PlanWritten.pinnedFull_of_ok
