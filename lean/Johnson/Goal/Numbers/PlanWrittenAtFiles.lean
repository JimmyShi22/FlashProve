-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenAtFiles.lean: over Johnson/Desc/Ok/PlanWritten/Rounds.lean: the
statement of Johnson/Desc/Ok/PlanWritten/Rounds.lean, closed, at the two named sets of public files
(`VerifierAndGoals.storedPublicFiles`, `VerifierAndGoals.zGap`, Ladder/Stored.lean); a second parameter file for each set, at which
the statement is to be false; and what a run has to ask. Statements: they are not proved.

Row or tool. `RoundsWrittenAtBoth` speaks of the planner's text and of written values at the stored
full-size files, and of no description of the protocol. It is a tool at the planner, and becomes a
row's statement only with a tie that is typed nowhere: that the one written description takes its
rounds from `declKOf`, `declPOf` of what `madeOfAt` returns. All else here is a tool.

Definitions, statements and proofs.
  `RoundsWrittenAtBoth`: the closed statement: at the stored full-size public files, and at the same
    three files with the other policy: at every digest of 32 bytes the rounds that are computed from
    the files are the library's six written lists, and the stored table's depth is 32.
  `bentLines`, `bentOf pol`: the second parameter file: pol with its first 32 lines replaced by the
    stored 32 lines in which "work positions 20 28 32" reads "work positions 20 29 32": one bit of
    work more before the draws of positions of the rounds that a batch shares. One byte turns.
  `NotWrittenAtBent`: closed: at each set with its second parameter file all is made at the anchor
    and the statement is false. (Without the first clause it would hold also where the planner
    refuses.) `PinnedAtBoth`: closed: at each set `madeOf` returns, and `planIsWritten` says yes of
    what it returns.
  `rideFull note`, `rideGap note`: for a run: `ride` (Johnson/Desc/Ok/PlanWritten/Rounds.lean) at
    the two sets: fourteen named Bools each. note is any string; the first line gives it back.
  `both_of_rides`: if the first answer of both is true, the closed statement holds. `all_of_rides`:
    if the first eleven answers of both are `foretold`, then also `PinnedAtBoth` and
    `NotWrittenAtBent`.
  `roundsOf_full`, `roundsOf_gap`: from the closed statement: `roundsOf` at each set returns the six
    written lists: at the first set that is the premise under which the member for the base case's
    law stands at the stored full-size files. `pinned_both`: from the closed statement: `madeOf`
    returns at each set, and `planIsWritten` says yes of what it returns if that has the full size's
    key (that it has: Johnson/Goal/Numbers/PlanWrittenScope.lean, `pinned_of_written`). `data_both`:
    from the closed statement: at every digest of 32 bytes the computed data of both files are
    `dataAt` of the written lists at the depth 32 (in the form of
    Johnson/Flat/Dec/FitAtWritten.lean: Johnson/Desc/Ok/PlanWritten/AtDesc.lean,
    `computed_written`).

Why this line was turned, and what is foretold. `Params.close` (OnBytes/Params/Planner.lean) writes
into a round's entry the bits of work that the setting has for the kind of the round's error and for
its scope, whether or not the round needs them; `settingOf` (OnBytes/Params/Setting.lean) takes them
for the draws of positions from this line. In the written lists the rounds of positions bear 32 in
the key file's three chains, 20 in the proof file's first and second chain and 28 in its shared
chain: the line's third, first and second number. So where the planner returns at the second file,
the shared chain's rounds of positions bear 29, and both tests say no. By reading; no theorem.
Whether the planner returns there is not known to this file. For it: more work asks for no more
positions (`scopePositions`, OnBytes/Params/Group.lean); 29 is below the 32 bits that the model's
reader lets through (`frameWords`, OnBytes/Model/Config.lean); and the head of
Johnson/G/RoundsOfPlanGuard.lean tells of evaluations outside the build at eleven further parameter
files of the small example, one of them without work before the positions, at which the planner
returned. If it refuses, control 5 is idle, its line says so with the refusal's words, and no
control here bends a file. Whether the other five lists turn (fewer positions may turn sizes that
other chains take over) is not foretold.

What a ride costs. Each ride calls the planner twice (at the set's parameter file and at the second
one), so the two rides call it four times. After each call the rounds are made twice from what was
made. Each ride compares lists of the long chains' length some twelve times over.

Limits. Not proved, and no run of it is known. A yes in a run is evidence and no proof:
it trusts Lean's evaluator, and with compiled code Lean's compiler, the C compiler and the linking.
What a like test on the other road took at the full size: the head of
Ask/EntryFiresFull.lean [not in this library]. All
limits of Johnson/Desc/Ok/PlanWritten/Rounds.lean, above all: a yes is a check of copying and of a
fitted rule against this library's own planner, no second witness, and nothing is held against the
C++ planner's rows; each plan's six settings, the entry record, the planner's records with the
errors' numbers, and the sizes and codes but for the one depth are not compared; the second road
alone; not the entry file's rounds; the form compared is the written form, not the declared form
that a reader of a file takes. That `VerifierAndGoals.storedPublicFiles` spells the shipped files is not tested in this
library (the head of Ladder/Stored.lean). The second parameter files lie outside the goals' scope,
which fixes the first 32 lines: control 5 shows that the tests can say no at a file at which the
planner returns, at one line and one number of it, and nothing of other lines. At other public files
in the goals' scope nothing is said. No ride at the small example. Nothing on soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Rounds
import Ladder.Stored

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open OnBytes.Maker (WholeD dataAt)
open OnBytes.Tie.Pv.Plan (textOf)

/-- **THE CLOSED STATEMENT**, at the two named sets of public files. -/
def RoundsWrittenAtBoth : Prop :=
  RoundsWritten VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL ∧
    RoundsWritten VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL

/-- The stored parameter file's first 32 lines with one number of the line on the work before the
draws of positions turned: 29 for 28. -/
def bentLines : List String :=
  VerifierAndGoals.lines32.map fun l =>
    if l == "work positions 20 28 32" then "work positions 20 29 32" else l

/-- A parameter file that begins with the stored 32 lines, with `bentLines` in their place. -/
def bentOf (pol : ByteArray) : ByteArray :=
  textOf bentLines ++ pol.extract (textOf VerifierAndGoals.lines32).size pol.size

/-- CLOSED: at each set with its second parameter file ALL IS MADE at the anchor, with short
strings, and the statement is false. (The statement is false also where the planner refuses: the
first clause shuts that out.) -/
def NotWrittenAtBent : Prop :=
  (returnsOk (bentOf VerifierAndGoals.storedPublicFiles.pol) VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = true ∧
      ¬ RoundsWritten (bentOf VerifierAndGoals.storedPublicFiles.pol) VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL) ∧
    (returnsOk (bentOf VerifierAndGoals.zGap.pol) VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL = true ∧
      ¬ RoundsWritten (bentOf VerifierAndGoals.zGap.pol) VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL)

/-- CLOSED: at each set `madeOf` returns, and `planIsWritten` says yes of what it returns. -/
def PinnedAtBoth : Prop :=
  (∃ m, madeOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok m ∧
      planIsWritten m = true) ∧
    ∃ m, madeOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL = .ok m ∧ planIsWritten m = true

/-- FOR A RUN, at the stored full-size public files. -/
def rideFull (note : String) : List (String × Bool) :=
  ride note VerifierAndGoals.storedPublicFiles.pol (bentOf VerifierAndGoals.storedPublicFiles.pol) VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL

/-- FOR A RUN, at the same three files with the other policy. -/
def rideGap (note : String) : List (String × Bool) :=
  ride note VerifierAndGoals.zGap.pol (bentOf VerifierAndGoals.zGap.pol) VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL

/-- **If the first answer of both rides is true, the closed statement holds.** -/
theorem both_of_rides {s t : String} (hF : ((rideFull s).map Prod.snd).head? = some true)
    (hG : ((rideGap t).map Prod.snd).head? = some true) : RoundsWrittenAtBoth := by
  unfold rideFull at hF
  unfold rideGap at hG
  rw [ride_head] at hF hG
  exact ⟨roundsAre_of_ok (Option.some.inj hF), roundsAre_of_ok (Option.some.inj hG)⟩

/-- **If the first eleven answers of both rides are the foretold ones, the closed statement holds,
`PinnedAtBoth` holds, and at the second parameter files all is made and the statement is false.** -/
theorem all_of_rides {s t : String} (hF : ((rideFull s).map Prod.snd).take 11 = foretold)
    (hG : ((rideGap t).map Prod.snd).take 11 = foretold) :
    RoundsWrittenAtBoth ∧ PinnedAtBoth ∧ NotWrittenAtBent :=
  ⟨⟨(of_ride hF).1, (of_ride hG).1⟩, ⟨(of_ride hF).2.1, (of_ride hG).2.1⟩, (of_ride hF).2.2,
    (of_ride hG).2.2⟩

/-- From the closed statement: the rounds on the road through `madeOf`, at the first set. -/
theorem roundsOf_full (h : RoundsWrittenAtBoth) :
    roundsOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok (dryKeyFull, dryProofFull) :=
  roundsOf_of_are h.1

/-- The like at the second set. -/
theorem roundsOf_gap (h : RoundsWrittenAtBoth) :
    roundsOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL = .ok (dryKeyFull, dryProofFull) :=
  roundsOf_of_are h.2

/-- From the closed statement: `madeOf` returns at each set, and `planIsWritten` says yes of what it
returns if that has the full size's key. -/
theorem pinned_both (h : RoundsWrittenAtBoth) :
    (∃ m, madeOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok m ∧
        (keyOf m = fullKey → planIsWritten m = true)) ∧
      ∃ m, madeOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL = .ok m ∧
        (keyOf m = fullKey → planIsWritten m = true) :=
  ⟨(planIs_own h.1).imp fun m x =>
      ⟨x.1, fun k => yes_of_full k ((planIs_iff _ _ m).1 x.2).1 ((planIs_iff _ _ m).1 x.2).2⟩,
    (planIs_own h.2).imp fun m x =>
      ⟨x.1, fun k => yes_of_full k ((planIs_iff _ _ m).1 x.2).1 ((planIs_iff _ _ m).1 x.2).2⟩⟩

/-- From the closed statement: at every digest of 32 bytes the computed data of both files, at each
set, are `dataAt` of the written lists at the depth 32. That `dataAt` is there the data of these
lists, and not of three empty ones: Johnson/Desc/Ok/PlanWritten/AtDesc.lean (`computed_written`). -/
theorem data_both (h : RoundsWrittenAtBoth) (c : ByteArray) (hc : c.size = 32) :
    (∃ m, madeOfAt VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL c = .ok m ∧
        dataKAt m = .ok (WholeD.of 32 (dataAt 32 (some dryKeyFull))) ∧
        dataPAt m = .ok (WholeD.of 32 (dataAt 32 (some dryProofFull)))) ∧
      ∃ m, madeOfAt VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL c = .ok m ∧
        dataKAt m = .ok (WholeD.of 32 (dataAt 32 (some dryKeyFull))) ∧
        dataPAt m = .ok (WholeD.of 32 (dataAt 32 (some dryProofFull))) :=
  ⟨data_of_are h.1 c hc, data_of_are h.2 c hc⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.both_of_rides
#print axioms VerifiableInference.PlanWritten.all_of_rides
#print axioms VerifiableInference.PlanWritten.roundsOf_full
#print axioms VerifiableInference.PlanWritten.roundsOf_gap
#print axioms VerifiableInference.PlanWritten.pinned_both
#print axioms VerifiableInference.PlanWritten.data_both
