-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactSide.lean: the frame's sentence `exact` at every member
of a seated side of a proximity test: the side that is taken off a description's own list at the
test's place, with the row of the two parts and their simulators' forms (`testSide`, Sim/Row.lean),
has just the two members that are written out; at the first the sentence holds by
Sim/ExactFirst.lean, at the second by Sim/ExactFree.lean: at one `On` (`onFree`: nothing at the
first part, `OnFree` at the second) and one `bud` (`budOpened`). Where the first fold's fresh table
has come earlier. It is stated at a state on entry that is made of the plan's public part, not shown
to be the verifier's. No property is claimed: the sentence at the second member is as empty as its
condition. General in the face φ (`Face`), the list bs of sub-protocols, the two jobs J and Js, the
table of codes K, the numbers chain and firstTree, the opening o and the list fs of falls.
Sim/FirstSeatAtHead.lean, among others, calls `members_of_seat`. Statements and proofs.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with Side.lean next to it. `exact` is a
field of its structure `Good` (Side.lean); `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) is that field's text at one member, and "the
sentence" is that proposition. A side (`Side`) is a description's sub-protocol (`block`) with a row:
a list of the prover's parts (`Part`), each paired with a term of type `Sim`, its simulator's form.
A seated side is one that `Side.seated` returns: its sub-protocol is the first in the list bs that
is at the given place (`Place`: where a sub-protocol is in a description). A member (`Member`) is
one part of the row with its number, from 0, its declared rounds with their oracle messages, and its
`Sim`; `Side.members` deals the sub-protocol's rounds out along the row, to each part as many as it
has moves. The two members that are written out are `firstMember J Js` and `restMember J Js`
(Sim/Row.lean). A job J (`TestJob`, …/K12/Test.lean) is what a caller supplies for its test, and the
simulators' job Js (`SimJob`, Sim/Sims.lean) is what it says of the test to the simulators. `J.p`
(`P12`) holds the test's parameters, among them its place `J.p.place` and its list of stages
`J.p.nums.stages` (`Fmt.M1.Stage`); a written place is a `P12` written out as a closed term, and a
place of a file is the place of a test in one of the files that the library describes, such as the
key file. `J.laid` (Test.lean), which unfolds to `laidOf J.p` (Johnson/Desc/K12/Law/ReadsK.lean),
lists the declared rounds, each with its oracle messages. `On` and `bud`, the two letters in the
entry on `exact_side`, are the last two parameters of `Good`: a condition at a part's start, and
which positions may be read at given challenges. The first fold's fresh table has come earlier where
`J.fresh.isNone = false`. An opening o is a tree's shape (`Fmt.Shape`) paired with its source
(`Fmt.TreeSource`). A letter is a free parameter, or a field that the caller fills. A tie is a
condition that a statement takes as a hypothesis; the public ties are the fields of `PubTies`
(Sim/ExactPlan.lean), `OpenTie` (Sim/ExactFree.lean) and `FirstPub` (Sim/ExactFirst.lean). Paid:
proved. Laid: built. Empty: vacuous. A member of a condition is a choice of values at which it
holds. What the spent run is, and what each of the two sentences says: the heads of
Sim/ExactFirst.lean and Sim/ExactFree.lean.

  `exact_side`: the statement: "∀ u ∈ σ.members, ExactMember … u": the text of the field `exact` of
    the frame's structure, at these two letters; at a state on entry that is made of the plan's
    public part, not shown to be the verifier's
  `exact_side_KR`: the same at the written place of the key file's test on the ranges, every tie on
    public numbers paid by the kernel's own evaluation; at a state on entry that is made of the
    plan's public part, not shown to be the verifier's. The place is `piKRFull`
    (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), K is `codesKeyFull` and o is `oKR`
    (Sim/ExactFreeKR.lean)
  `members_of_seat`: the side's members are the two that are written out:
    `σ.members = [firstMember J Js, restMember J Js]` for a side σ that `testSide bs J Js fs`
    returns. Under three hypotheses: the sub-protocol's rounds with their oracle messages are the
    job's (hl) · two stages or more (hst) · the place has as many declared rounds as the two parts
    have moves (hc)
  `firstPub_of_ties`: the second member's public ties give the first's: `PubTies J Js K` and
    `J.fresh.isNone = false` give `FirstPub J Js`
  `len_movesFrom`: the list `movesFrom J rd a n` (…/K12/Parts.lean) has n moves

By what. `members_of_seat` unfolds `testSide` and `Side.seated`, takes the two parts' numbers of
moves, `firstLen` and `restLen`, from `first_moves` and `rest_moves` with `len_movesFrom`, and
unfolds `membersOf` (Side.lean); by hc, the first `restLen` of the rounds that the first part leaves
are all of them. `firstLen` is in …/K12/Parts.lean, the three others in …/K12/HalfSteps.lean.
`exact_side` takes the list of stages from `reach_gives` (Sim/Reach.lean), rewrites by
`members_of_seat`, and calls `exact_first` (Sim/ExactFirst.lean) at `firstPub_of_ties` and
`exact_free` (Sim/ExactFree.lean). `exact_side_KR` goes the same way, with `pubTies_KR`
(Sim/ExactAtKR.lean), `exact_first_KR` (Sim/ExactFirstKR.lean) and `exact_free_KR`
(Sim/ExactFreeKR.lean).

Hypotheses. `exact_side` has five, next to those inside `ExactMember`:
  `hσ : testSide bs J Js fs = some σ`: bs has a sub-protocol at the test's place, and σ is made of
    the first such one, the row `testPairs J Js` (Sim/Row.lean) and the falls of fs at that place
  `hl`: that sub-protocol's rounds, zipped with its lists of oracle messages, are `J.laid`
  `T : PubTies J Js K`: eight fields on public numbers and on the two jobs' public fields, listed in
    the head of Sim/ExactPlan.lean. Its field `reach` gives three stages or more and
    `J.p.nums.ownMask = false` (`reach_gives`); its field `count` is hc of `members_of_seat`
  `To : OpenTie J Js chain o`: three fields, listed in the head of Sim/ExactFree.lean
  `hfr : J.fresh.isNone = false`: the job says that the first fold's fresh table has come earlier
`exact_side_KR` has seven: hσ, hl and hfr as above, and:
  `hJ : J.p = piKRFull`: the job is at the written place
  `hp : Js.p = J.p`, `ho : Js.own = false`: the simulators' job is at the same place and says the
    same of the table
  `hop`: `Js.opens` has one entry, made of `srcOf chain oKR.2` and `oKR.1.a`

Limits.
- It is stated at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: the job's state on entry is a field of the free parameter J (`TestJob`), and nothing
  here compares it with a verifier's state; the clause `door` of `OnFree` compares it with the field
  of the same name of Js.
- Those of Sim/ExactFirst.lean at the first member, and those of Sim/ExactFree.lean at the second.
- It is one field of the structure, at an `On` and a `bud` of this folder's own: not those of
  Sim/Spec.lean. Those are `testOn` and `testBud` (Sim/Row.lean).
- `OnFree` has no member at a place of a file. `OnFree` has no value that meets it in the library:
  nothing in the library shows that the sentence at the second member is not vacuous.
- That a job which is played meets the hypotheses is not shown: J and Js are free parameters.
- It speaks of the parts `firstPart` and `restPart` (…/K12/Parts.lean), of which `testPairs` makes
  the row, not of halves with a guard in front.
- The two members' sentences stand side by side: nothing joins them: the first samples the spent run
  afresh, the second holds the same coins fixed; the owner's sentence (the field `fresh`) is not
  touched.
- `members_of_seat` is not `Spec.members` (Sim/Spec.lean), which has neither the hypothesis on the
  stages nor the one on the count.
- That a description has a sub-protocol at the place whose rounds are the job's is a hypothesis (hσ,
  hl).
- One tree in front. `OpenTie` asks that the second part's round number 1 is declared to open just
  one tree, and the clause `tree` of `OnFree` that the job's list of trees has one entry.
- At the level of oracle messages: no root, salt or hash.
- fs, the chain's falls (`Fall`, Side.lean), which `Side.seated` takes with a row, is a free
  parameter; no proof reads the side's field `fall`.
- At the key file's place (`exact_side_KR`): eight ties are proved by evaluation in Lean's kernel:
  `reach_KR_full` (Sim/ReachAt.lean), `planB_KR` (…/K12/AtKeyRanges.lean), `formPubB_KR`
  (…/K12/FormPubAt.lean), `count_KRs`, `rounds_KR`, `tables_KR` (Sim/ExactAtKR.lean), `open_KR`,
  `openDepth_KR` (Sim/ExactFreeKR.lean). Seven are hypotheses: the side (hσ) · the rounds (hl) · the
  place (hJ) · the three on the two jobs' public fields (hfr, hp, ho) · the declared opening (hop).
  The one declared opening, `oKR`, is one of the numbers of the place that are a print's word: for
  these the print of a run of Lean's evaluator is trusted
  (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean, Limits, which names them). No job is laid there; it
  counts nothing. J and Js are free parameters.
- No seated side is given by name here. That the five hypotheses of `exact_side` hold together is
  not shown here.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFreeKR
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstKR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Member (piKRFull codesKeyFull)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-- As many moves as rounds: the list has n moves. -/
theorem len_movesFrom {C : Type} (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) :
    (movesFrom J rd a n).length = n := by
  unfold movesFrom
  rw [List.length_map, List.length_range]

/-- **The side's members are the two that are written out.** hl: the sub-protocol's rounds with
their oracle messages are the job's. hst: two stages or more. hc: the place has as many declared
rounds as the two parts have moves. -/
theorem members_of_seat (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb)
    (fs : List (Fall S)) (σ : Side S Cl V W X Pb) (hσ : testSide bs J Js fs = some σ)
    (hl : σ.block.rounds.zip σ.block.oracles = J.laid) (s t : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hc : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages) :
    σ.members = [firstMember J Js, restMember J Js] := by
  unfold testSide Side.seated at hσ
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages :=
    (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages :=
    (congrArg List.length (rest_moves J s t rest hst)).trans (len_movesFrom J _ _ _)
  have hl' : b.rounds.zip b.oracles = J.laid := hl
  show membersOf (testPairs J Js) 0 (b.rounds.zip b.oracles) = _
  rw [hl']
  show [(⟨0, J.laid.take (firstPart J : Part V W X).moves.length, firstPart J, firstSim Js⟩ :
      Member V W X Pb),
    ⟨1, (J.laid.drop (firstPart J : Part V W X).moves.length).take
      (restPart J : Part V W X).moves.length, restPart J, restSim Js⟩] = _
  have e : (J.laid.drop (firstLen J.p.nums.stages)).take (restLen J.p.nums.stages) =
      J.laid.drop (firstLen J.p.nums.stages) := List.take_of_length_le (by
    rw [List.length_drop]
    show (laidOf J.p).length - _ ≤ _
    omega)
  rw [l1, l2, e]
  rfl

/-- The second member's public ties give the first's: `PubTies` and hfr give `FirstPub`. -/
theorem firstPub_of_ties {J : TestJob W X} {Js : SimJob Pb} {K : Codes} (T : PubTies J Js K)
    (hfr : J.fresh.isNone = false) : FirstPub J Js :=
  ⟨T.place, by rw [T.own, hfr], T.form, by rw [T.count]; exact Nat.le_add_right _ _, T.tables⟩

/-- **The frame's sentence at every member of the seated side.** It is stated at a state on entry
that is made of the plan's public part, not shown to be the verifier's. Under `PubTies`, `OpenTie`
and hfr, at `On` := `onFree` and `bud` := `budOpened`. The sentence at the second member is as empty
as its condition `OnFree`; nothing joins the two members' sentences. Limits: the file's head. -/
theorem exact_side (φ : Face V W Pb) (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb)
    (K : Codes) (chain firstTree : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (fs : List (Fall S))
    (σ : Side S Cl V W X Pb) (hσ : testSide bs J Js fs = some σ)
    (hl : σ.block.rounds.zip σ.block.oracles = J.laid) (T : PubTies J Js K)
    (To : OpenTie J Js chain o) (hfr : J.fresh.isNone = false) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree (onFree φ J Js K chain o)
      (budOpened J.p.nums.stages) u := by
  obtain ⟨a, next, nx', rest', hst, -, -, -, -⟩ := reach_gives J.p T.reach
  rw [members_of_seat bs J Js fs σ hσ hl a next (nx' :: rest') hst T.count]
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact exact_first φ σ J Js chain firstTree _ _ hfr (firstPub_of_ties T hfr)
  · exact exact_free φ σ J Js K chain firstTree o T To

/-- **The same at the key file's test on the ranges.** It is stated at a state on entry that is made
of the plan's public part, not shown to be the verifier's. No job is laid there; it counts nothing.
The sentence at the second member is as empty as its condition `OnFree`. -/
theorem exact_side_KR (φ : Face V W Pb) (bs : List (Block S Cl)) (J : TestJob W X)
    (Js : SimJob Pb) (chain firstTree : ℕ) (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (hσ : testSide bs J Js fs = some σ) (hl : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hp : Js.p = J.p) (ho : Js.own = false)
    (hop : Js.opens = [((srcOf chain oKR.2).1, (srcOf chain oKR.2).2, oKR.1.a)]) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree (onFree φ J Js codesKeyFull chain oKR)
      (budOpened J.p.nums.stages) u := by
  obtain ⟨a, next, nx', rest', hst, -, -, -, -⟩ :=
    reach_gives J.p (pubTies_KR J Js hJ hfr hp ho).reach
  rw [members_of_seat bs J Js fs σ hσ hl a next (nx' :: rest') hst
    (pubTies_KR J Js hJ hfr hp ho).count]
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact exact_first_KR φ σ J Js chain firstTree _ _ hJ hfr hp ho
  · exact exact_free_KR φ σ J Js chain firstTree hJ hfr hp ho hop

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.len_movesFrom
#print axioms ProofFile.Honest.K12.members_of_seat
#print axioms ProofFile.Honest.K12.firstPub_of_ties
#print axioms ProofFile.Honest.K12.exact_side
#print axioms ProofFile.Honest.K12.exact_side_KR
