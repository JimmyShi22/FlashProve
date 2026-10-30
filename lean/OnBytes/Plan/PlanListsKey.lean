-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/PlanListsKey.lean: the whole plan of a key's one-time chain, as a list.

The like of OnBytes/Params/PlanListsChains.lean for the first of a key's three chains
(`oneTimePlan`, OnBytes/Plan/KeyOneTime.lean); the other two are a shared chain and a second chain,
which that file treats. The list has one named part for each block, in the order of
`oneTimeRounds`: the entry for the table's record; the sending of the index-mask
message; the proof of the ranges (the sending of the multiplicities, one part for each lookup, the
proximity test and, if several rows are left on the table, their joining); the first part of the
test on the table; and SEAL, the list's last member. For every sizing of a key: nothing is
evaluated.

Main definitions: `sendList`, `rangesListAt`, `rangesList`, `linFirstList`, `oneTimeListAt`,
`oneTimeList`.
Main theorems: `runs_rangesPlan`, `runs_linPlanFirst`, `runs_oneTimeRounds`, `oneTimePlan_rounds`,
`oneTimePlan_is`, `keySized_oneTime`, `keySized_requests`.
What is not claimed: that the plan is finished or holds: that is the hypothesis of
`oneTimePlan_rounds` and `oneTimePlan_is`. The converse: that a plan whose described rounds hold is
finished or holds. Of the routines' own tests only the two values that had to be there and
`sizedFits` are kept; nothing of a lookup's tests. That the program's blocks state these rounds in a
dry run. Nothing on the kinds of written rounds: an entry of a plan has none. Nothing on the C++
planner, of which OnBytes/Params/ and OnBytes/Plan/ are renderings. For proofs only; the program,
that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.PlanListsChains
import OnBytes.Plan.KeyOneTime

set_option autoImplicit false

namespace OnBytes.Plan

open OnBytes.Params

/-- The two rounds of the sending of oracle messages: the seeds of their samples, and the answers.
-/
def sendList (s : Setting) (o : List SampleSize) (roots : Nat) : List RoundSpec :=
  [sendSeed s o roots,
    .silent "SEND answer" (24 * (s.samples * o.length)) (s.samples * o.length)]

/-- The rounds of the proof of the ranges, at n trees of the message of the multiplicities. -/
def rangesListAt (s : Setting) (c : Scope) (codes : Codes) (z : RangesSized) (n : Nat) :
    List RoundSpec :=
  sendList s [⟨cubeBitsOf codes z.x.message.shape, [z.test.first]⟩] n ++
    (((lookupSizes z.x z.matrix).map (lookupList s)).flatten ++
      (ioppList s c z.test.stages (Wf.rowsBatched z.x z.matrix)
          (if z.x.choice.masksRide then 0 else 1) z.x.choice.masksRide ++
        (if 1 < z.pending then
          .said "BAT-sigma" .field (powersError s z.pending)
              { drawE := 1, rows := z.pending, priced := .asSaid } 0 0 0 ::
            pscList s { degree := List.replicate z.matrix.kCol 3, withY := false }
        else [])))

/-- The rounds of the proof of the ranges. Written as empty where the number of trees does not
follow; the plan is then refused. -/
def rangesList (s : Setting) (c : Scope) (codes : Codes) (z : RangesSized) : List RoundSpec :=
  ((treesOf codes (Wf.messageOf z.x)).map (rangesListAt s c codes z)).getD []

/-- The rounds of the first part of the test on the table. Written as empty where the plans' sizes
do not follow; the plan is then refused. -/
def linFirstList (s : Setting) (codes : Codes) (x : LinSized) : List RoundSpec :=
  ((linSizeOf codes x).map fun L => sendList s (L.w :: L.besideW) L.rootsW).getD []

/-- The entries of the plan of a key's one-time chain, at n trees of the message of the
multiplicities and at the sizes L that the plans of the test on the table read. SEAL is the last. -/
def oneTimeListAt (z : KeySized) (n : Nat) (L : LinSize) : List RoundSpec :=
  recordList z.set z.once.table ++
    (sendList z.set [⟨cubeBitsOf z.codes z.once.input.shape, [z.once.own.first]⟩] 1 ++
      (rangesListAt z.set .once z.codes z.ranges n ++
        (sendList z.set (L.w :: L.besideW) L.rootsW ++ [sealRound])))

/-- The entries of the plan of a key's one-time chain. -/
def oneTimeList (z : KeySized) : List RoundSpec :=
  recordList z.set z.once.table ++
    (sendList z.set [⟨cubeBitsOf z.codes z.once.input.shape, [z.once.own.first]⟩] 1 ++
      (rangesList z.set .once z.codes z.ranges ++
        (linFirstList z.set z.codes z.once ++ [sealRound])))

section
variable {s : Setting} {c : Scope}

/-- The proof of the ranges. -/
theorem runs_rangesPlan (codes : Codes) (z : RangesSized) :
    Runs s c 0 0 0 (rangesPlan codes z) () (rangesList s c codes z) 0 0 0 := by
  unfold rangesPlan rangesList
  refine runs_must (L := rangesListAt s c codes z) ?_
  intro n
  exact Runs.cast (runs_bind (runs_send _ n) (runs_bind (runs_forEach runs_lookup _)
    (runs_bind (runs_needs _ _ 0 0 0) (runs_bind (runs_iopp _ _ _ _)
      (runs_ite (v := ()) (w := ()) (fun _ => runs_batt _ _) (fun _ => runs_pure () 0 0 0))))))
    (by simp [rangesListAt, sendList])

/-- The first part of the test on the table. -/
theorem runs_linPlanFirst (codes : Codes) (x : LinSized) :
    Runs s c 0 0 0 (linPlanFirst codes x) () (linFirstList s codes x) 0 0 0 := by
  unfold linPlanFirst linFirstList
  refine runs_must (L := fun L : LinSize => sendList s (L.w :: L.besideW) L.rootsW) ?_
  intro L
  unfold planLinFirst
  exact runs_send _ _

end

/-- The rounds of a key's one-time chain. -/
theorem runs_oneTimeRounds (z : KeySized) :
    Runs z.set .once 0 0 0 (oneTimeRounds z) () (oneTimeList z) 0 0 0 := by
  unfold oneTimeRounds
  exact runs_bind (runs_record _ 0 0 0) (runs_bind (runs_send _ 1)
    (runs_bind (runs_rangesPlan _ _) (runs_bind (runs_linPlanFirst _ _) runs_seal)))

/-- What the routine of the proof of the ranges has found: the number of trees was there; and the
stages that the proof of the ranges runs are as many as those that are priced, and each names the
priced stage's codes and numbers of rows (`sizedFits`). -/
theorem knows_rangesPlan {s : Setting} {c : Scope} (codes : Codes) (z : RangesSized) :
    Knows s c 0 0 0 (rangesPlan codes z)
      (∃ n, treesOf codes (Wf.messageOf z.x) = some n ∧
        sizedFits codes z.x.stages z.test.stages = true) := by
  unfold rangesPlan
  refine knows_must fun n => ?_
  exact knows_snd (runs_send _ n) (knows_snd (runs_forEach runs_lookup _)
    (knows_fst (knows_needs _ _ 0 0 0)))

/-- What the routine of the first part of the test on the table has found: the sizes that the plans
read were there. -/
theorem knows_linPlanFirst {s : Setting} {c : Scope} (codes : Codes) (x : LinSized) :
    Knows s c 0 0 0 (linPlanFirst codes x) (∃ L, linSizeOf codes x = some L) := by
  unfold linPlanFirst
  exact (knows_must (F := fun _ => True) fun L => knows_true _ 0 0 0).mono
    fun ⟨L, hL, _⟩ => ⟨L, hL⟩

/-- The plan of a key's one-time chain: `PlanIs` at `oneTimeList`. -/
theorem oneTimePlan_rounds {z : KeySized} {P : Planned} (h : oneTimePlan z = .ok P) :
    PlanIs P z.set .once (oneTimeList z) :=
  planIs_of (runs_oneTimeRounds z) h

/-- The plan of a key's one-time chain, with the two values that had to be there: the number n of
trees of the message of the multiplicities and the sizes L that the plans of the test on the table
read. `sizedFits` holds of the stages that the proof of the ranges runs and those that are priced;
and the list is written at n and L. -/
theorem oneTimePlan_is {z : KeySized} {P : Planned} (h : oneTimePlan z = .ok P) :
    ∃ n L, treesOf z.codes (Wf.messageOf z.ranges.x) = some n ∧
      linSizeOf z.codes z.once = some L ∧
      sizedFits z.codes z.ranges.x.stages z.ranges.test.stages = true ∧
      PlanIs P z.set .once (oneTimeListAt z n L) := by
  have k : Knows z.set .once 0 0 0 (oneTimeRounds z)
      ((∃ n, treesOf z.codes (Wf.messageOf z.ranges.x) = some n ∧
        sizedFits z.codes z.ranges.x.stages z.ranges.test.stages = true) ∧
        ∃ L, linSizeOf z.codes z.once = some L) := by
    unfold oneTimeRounds
    refine knows_snd (runs_record _ 0 0 0) (knows_snd (runs_send _ 1) (Knows.and ?_ ?_))
    · exact knows_fst (knows_rangesPlan _ _)
    · exact knows_snd (runs_rangesPlan _ _) (knows_fst (knows_linPlanFirst _ _))
  obtain ⟨⟨n, hn, hf⟩, L, hL⟩ := finishHeld_knows k h
  refine ⟨n, L, hn, hL, hf, ?_⟩
  have := oneTimePlan_rounds h
  unfold oneTimeList rangesList linFirstList at this
  rw [hn, hL] at this
  exact this

/-- The sizes of a key's chains: the test on the table is the committer's one-time test, and the
setting is the lines'. With the first, the scope `if x.lines.oneTime then .once else …` in
`sharedPlan_is` and `secondPlan_is` (OnBytes/Params/PlanListsChains.lean) is `.once` at x := z.once:
`keyShared_is`, `keySecond_is` (OnBytes/Plan/PlanListsKeyMembers.lean). -/
theorem keySized_oneTime {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) : z.once.lines.oneTime = true ∧ z.set = settingOf l := by
  unfold keySized at h
  extract_lets at h
  obtain ⟨T, _, h⟩ := opt_bind h
  obtain ⟨L, _, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, _, h⟩ := opt_bind h
  cases h
  refine ⟨?_, rfl⟩
  show once.lines.oneTime = true
  rw [linSized_lines ho]
  rfl

/-- The committer's one-time test is a batch of one request. -/
theorem keySized_requests {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) : z.once.lines.requests = 1 := by
  unfold keySized at h
  extract_lets at h
  obtain ⟨T, _, h⟩ := opt_bind h
  obtain ⟨L, _, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, _, h⟩ := opt_bind h
  cases h
  show once.lines.requests = 1
  rw [linSized_lines ho]
  rfl

end OnBytes.Plan

#print axioms OnBytes.Plan.keySized_requests
#print axioms OnBytes.Plan.oneTimePlan_is
#print axioms OnBytes.Plan.keySized_oneTime
#print axioms OnBytes.Plan.runs_rangesPlan
#print axioms OnBytes.Plan.runs_oneTimeRounds
#print axioms OnBytes.Plan.oneTimePlan_rounds
