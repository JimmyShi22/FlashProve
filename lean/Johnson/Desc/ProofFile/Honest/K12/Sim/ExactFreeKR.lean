-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFreeKR.lean: `exact_free` (Sim/ExactFree.lean) at the
written place of the key file's test on the ranges, at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean): the frame's own sentence `exact` at that test's
second member, at a condition no clause of which speaks of the part's own challenges, with every tie
on public numbers paid by the kernel's own evaluation. It is stated at a state on entry that is made
of the plan's public part, not shown to be the verifier's. No job is defined here: J and Js are free
parameters. No property is claimed: whether a run of the key file's chain meets `OnFree` is not
shown. General in the face φ (`Face`), the side σ, the two jobs J and Js and the numbers chain and
firstTree. Sim/ExactSide.lean calls `exact_free_KR`. Definitions, statements and proofs.

Terms. Those of the head of Sim/ExactFree.lean; in short: the frame is
Johnson/Desc/ProofFile/Honest/Frame.lean with Honest/Side.lean. `exact` is a field of its structure
`Good`, and `ExactMember` (Honest/Small/Field.lean) is that field's text at one member. A place
(`P12`) holds the numbers of a proximity test; the written place is the closed term `piKRFull`. A
job J (`TestJob`, Honest/K12/Test.lean) is what a caller supplies for its test, and the simulators'
job Js (`SimJob`, Sim/Sims.lean) is what a caller says of its test to the simulators. A job's letter
is one of its fields, and a job stands at the place that its field `p` holds. The first part has the
test's first `firstLen` rounds (Honest/K12/Parts.lean); the part is the second part, which has all
the others, and the second member is `restMember J Js` (Sim/Row.lean). Rounds are counted from 0.
The condition is `onFree`, which is `OnFree` in the type of the frame's `On` (both:
Sim/ExactFree.lean). A tie is a field of one of the two hypotheses of `exact_free`: `PubTies`
(Sim/ExactPlan.lean) and `OpenTie` (Sim/ExactFree.lean). To pay a tie is to prove it. A member of a
condition is a choice of values at which it holds. The fresh table is the first fold's. An opening
is a tree's shape (`Fmt.Shape`, with the depth `a`) paired with its source (`Fmt.TreeSource`). A number
is a print's word where the print of a run of Lean's evaluator is trusted for it.

  `exact_free_KR`: the statement. Asked of the two jobs' public letters: both stand at the place ·
    both say that the fresh table has come earlier · the simulators' job names that tree. That tree
    is `oKR`. In Lean, under the five hypotheses listed below: `ExactMember φ σ chain firstTree` at
    `On` := `onFree φ J Js codesKeyFull chain oKR`, at `bud` := `budOpened J.p.nums.stages`
    (Sim/ExactPlan.lean) and at the member `restMember J Js`; at a state on entry that is made of
    the plan's public part, not shown to be the verifier's
  `opensKR`: a definition: the trees that the part's round number 1 is declared to open: the field
    `opens` of round number 1 of `laidOf piKRFull` (Johnson/Desc/K12/Law/ReadsK.lean) without its
    first `firstLen` rounds; the empty list where there is no such round
  `oKR`: a definition: the first of them; a written default where the list is empty
  `open_KR`: it is the only one: `opensKR` has length 1; and there is such a round
  `openDepth_KR`: it has the first stage's depth: `oKR.1.a` is `(sgOf s).C.a` at the place's first
    stage s (`sgOf`: Johnson/Desc/K12/Law/ChainOf.lean)

By what. `exact_free_KR` is `exact_free` at the table of codes `codesKeyFull`
(Johnson/Desc/K12/Law/PlacesKeyFull.lean) and at the opening `oKR`. `PubTies` comes from
`pubTies_KR` (Sim/ExactAtKR.lean) at hJ, hfr, hp and ho. Of `OpenTie`, the field `decl` comes from
`open_KR` and the field `depth` from `openDepth_KR`, each after rewriting by hJ, and the field
`opens` is hop. `open_KR` and `openDepth_KR` are evaluations in Lean's kernel (`decide +kernel`).

Hypotheses. `exact_free_KR` has five, next to those inside `ExactMember`:
  hJ: `J.p = piKRFull`: the job's place is the written place
  hfr: `J.fresh.isNone = false`: the job names a sender of the first fold's fresh table
  hp: `Js.p = J.p`: the two jobs have the same place
  ho: `Js.own = false`: the field of Js for "the first fold sends its own fresh table" is false
  hop: `Js.opens` has one entry, made of `srcOf chain oKR.2` (the frame) and `oKR.1.a`

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: `J.rec₀` is a field of the free parameter J, and none of the five hypotheses speaks of
  it; the clause `door` of `OnFree` compares it with `Js.rec₀`, a field of the free parameter Js.
- It is shown at no job that is played.
- Those of Sim/ExactFree.lean and Sim/ExactAtKR.lean: `OnFree` has no member here: where it has none
  the sentence says nothing.
- `OnFree` has no value that meets it in the library, at this place or at any other.
- Numbers of the place are a print's word (the limits of
  Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean name them), and `oKR`, the one declared opening, is
  one of them: the clause "one tree" and the tree that the simulators' job names rest on it. The
  clause "one tree" is "the first reading round opens one tree" in `reachL` (Sim/Reach.lean) and the
  field `decl` of `OpenTie`. That `oKR` is the one entry of `piKRFull.nums.first` is by reading
  `roundsOfNums` (Johnson/Desc/K12/TestEntries.lean): no theorem here says so.
- At the level of oracle messages: no root, salt or hash. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFree
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactAtKR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Pub (sgOf)
open H2K.Member (piKRFull codesKeyFull)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-- The trees that the second part's round number 1 is declared to open, at the place; the empty
list where there is no such round. -/
def opensKR : List (Fmt.Shape × Fmt.TreeSource) :=
  ((((laidOf piKRFull).drop (firstLen piKRFull.nums.stages))[1]?).map (·.1.opens)).getD []

/-- The first of them; where the list is empty, the written default `(⟨0, 0, false, 0⟩, .own 0)`. -/
def oKR : Fmt.Shape × Fmt.TreeSource := opensKR.headD (⟨0, 0, false, 0⟩, .own 0)

theorem open_KR : opensKR.length = 1 ∧
    (((laidOf piKRFull).drop (firstLen piKRFull.nums.stages))[1]?).isSome = true := by
  decide +kernel

theorem openDepth_KR : oKR.1.a = (sgOf (piKRFull.nums.stages.headD default)).C.a := by
  decide +kernel

/-- **The frame's sentence at the second member of the key file's test on the ranges, at a condition
that reads none of the part's own challenges.** It is stated at a state on entry that is made of the
plan's public part, not shown to be the verifier's. At `On` := `onFree` at `codesKeyFull` and `oKR`,
and at `bud` := `budOpened`. The five hypotheses: see the head. -/
theorem exact_free_KR (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hp : Js.p = J.p)
    (ho : Js.own = false)
    (hop : Js.opens = [((srcOf chain oKR.2).1, (srcOf chain oKR.2).2, oKR.1.a)]) :
    ExactMember φ σ chain firstTree (onFree φ J Js codesKeyFull chain oKR)
      (budOpened J.p.nums.stages) (restMember J Js) := by
  refine exact_free φ σ J Js codesKeyFull chain firstTree oKR (pubTies_KR J Js hJ hfr hp ho)
    ⟨?_, ?_, hop⟩
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 open_KR.2
    refine ⟨d, ?_, ?_⟩
    · show ((laidOf J.p).drop (firstLen J.p.nums.stages))[1]? = some d
      rw [hJ]
      exact hd
    · have e : opensKR = d.1.opens := by
        unfold opensKR
        rw [hd]
        rfl
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 open_KR.1
      have e2 : oKR = x := by
        unfold oKR
        rw [hx]
        rfl
      rw [← e, hx, e2]
  · unfold TestJob.s₀
    rw [hJ]
    exact openDepth_KR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.open_KR
#print axioms ProofFile.Honest.K12.openDepth_KR
#print axioms ProofFile.Honest.K12.exact_free_KR
#print axioms ProofFile.Honest.K12.opensKR
#print axioms ProofFile.Honest.K12.oKR
