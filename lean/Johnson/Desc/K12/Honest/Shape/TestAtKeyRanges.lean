-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestAtKeyRanges.lean: the first stage's public tests at one place of a
proximity test: the ranges' test of the key file at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean). Evaluated is what reads only the plan and the codes:
three closed facts, two of them by an evaluation in Lean's kernel, the third from the first. Before
them, the arguments that `doorB` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean) and `firstB`
(Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean) leave free are defined as functions of a place,
for whoever evaluates `doorB`, `firstB` or `testCore` (Johnson/Desc/K12/Honest/Shape/TestCore.lean)
at a shape. The definitions are general in the place.

Terms, as in the head of TestSwitchPub.lean. A place, or plan, is p (`P12`,
Johnson/Desc/K12/Frame.lean: the numbers of the place of a test). A stage is given twice: as
`Fmt.M1.Stage` (its numbers) and as `IoppStage` (OnBytes/Params/Items.lean: its two codes by their
numbers in the table of codes, with k and h). The parts of a test are the front, the batching, in
each stage but the last the fold, the switch and the batching after it, and the base case. The frame
is the test's own (`proximityTestKind`, `stagesFrom`, Johnson/Desc/K12/Frame.lean), not the frame for an honest
side (Johnson/Desc/ProofFile/Honest/Frame.lean): it cuts the declared rounds (`Fmt.DeclaredRound`) among
the parts. A shape is `TestSh` (Johnson/Desc/K12/Honest/Shape/Test.lean: the shape of the structure
inside a test); the core's shape is its field `core` (`CoreSh`,
Johnson/Desc/Ground/Shape/Core.lean). The door is the word of TestDoor.lean for the front, the
batching, the frame's question after it and the first fold. "In front of" means before, in the order
of the parts.

  `switchPubB_KR`: `switchPubB` (TestSwitchPub.lean) is true at `piKRFull`, at the key file's table
    of codes (`codesKeyFull`, Johnson/Desc/K12/Law/PlacesKeyFull.lean), at `j := 0` and at the
    values of the functions below at `piKRFull`, each in the argument in which `firstOf` passes it
    to `firstB` and `firstB` to `switchPubB`
  `switchPub_KR`: so `SwitchPub` (Johnson/Desc/K12/Honest/Shape/TestSwitch.lean) holds at the same
    arguments
  `cuts_KR`: at `piKRFull`: `batCut` (Johnson/Prover/Link/FormBat.lean) is true at `cutBOf`;
    `foldCut` (Johnson/Prover/Link/FormFold.lean) is true at k of the first stage and `cutFOf`;
    `cutSOf` has two elements
  `doorOf`, `firstOf`: definitions: `doorB` and `firstB` at a place p and a shape a, with every
    other argument supplied by the functions below at p. The two rounds of the switch are the first
    and the second element of `cutSOf p`
  `frontSh`: a definition: a shape in front of a test, of the core's shape, the group's number and
    the mask's message. In Lean: `⟨c, g, .nothing, mask⟩`; `testCore` takes the same three arguments
    after the place
  `cutBOf`, `cutFOf`, `cutSOf`: definitions: of the list of declared rounds that
    `H2U.roundsOfNums p.nums` (Johnson/Desc/K12/TestEntries.lean) returns: the first round, for the
    batching; the next 1 + k rounds, k of `curOf p`, for the first fold; the next two, for the first
    switch. They are not the frame's cut by any lemma: see the first limit
  `curOf`, `nxtOf`: definitions: the first and the second element of `p.nums.stages`
  `idxOf`: a definition: the first element of `p.idx`: the numbers of the first stage's two codes
  `nextOf`: a definition: the second stage as an `IoppStage`: the second element of `p.idx`, with k
    and h of `nxtOf p`
  `lastOf`: a definition: whether `p.nums.stages` has exactly two elements: whether the first switch
    goes into the last stage

By what. `switchPubB_KR` and `cuts_KR` are closed by `decide +kernel`. `switchPub_KR` is
`switchPub_of` (TestSwitchPub.lean) at `switchPubB_KR`.

Limits.
- `cutBOf`, `cutFOf` and `cutSOf` cut `(H2U.roundsOfNums p.nums).getD []`. The frame cuts
  `rs.zip p.oracles`, rs being what `H2U.roundsOfNums p.nums` returns, by the same counts, and gives
  a part the first components. By reading, the two agree where `p.oracles` is at least as long as
  rs, and not in general: `zip` stops at the shorter list. No lemma ties the three functions to the
  frame's cut, at `piKRFull` or elsewhere. At `piKRFull` the block's test on the plan, which has the
  clause `p.oracles.length == rs.length`, passes (`piKRFull_planOk`, PlaceKeyRangesFull.lean).
- The plan's half only: `doorB` and `firstB` also read the shape in front of the test, which is not
  here. Neither `doorOf` nor `firstOf` is evaluated here; at a written shape:
  Johnson/Desc/K12/Honest/Shape/TestAtKeyRangesShape.lean. Inside `firstB`, `switchPubB` is at the
  shape's own codes (`a.core.st.codes`); here it is at `codesKeyFull`.
- `cuts_KR` has `foldCut`, which is a clause of `firstB` where the shape's field `mask` is `some`.
  `foldCutOwn` (Johnson/Desc/K12/Honest/OwnFold.lean), the clause in the other case, is not
  evaluated. The statement has no clause on a mask; `piKRFull.nums.ownMask` is `false` by the
  definition of `piKRFull`.
- Where a list is too short the functions return a fixed value: `default` for a stage or a declared
  round, `(0, 0)` for a pair of code numbers, `[]` for the rounds where `H2U.roundsOfNums` returns
  nothing, as it does at fewer than two stages. `lastOf` is false at a plan of one stage, where
  there is no switch. No lemma here says what `doorOf` or `firstOf` answers at such a place.
- No theorem here uses `switchPub_KR` or `cuts_KR`, and there is no negative test: none of the tests
  is shown to be false at any argument here.
- "Public" is a word of these comments, for the plan, the codes, the declared rounds and the shape.
  No statement in Lean here says that any of them is public.
- All limits of PlaceKeyRangesFull.lean hold here too. Among them: the numbers of the closed place
  were copied by a program from the printed output of a run of Lean's evaluator, and by that file's
  head three numbers rest on printed output only: `first` and `free`, which `H2U.roundsOfNums`
  reads, and `start`, a field of `nKRFull`. That a description makes this place at any public files
  is stated neither there nor here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestSwitchPub
import Johnson.Desc.K12.Law.PlaceKeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open Johnson.Prover.Link (batCut foldCut)
open H2K.Member (piKRFull codesKeyFull)

/-! ## 1 The arguments of the tests as functions of a place -/

/-- The first stage: the first element of `p.nums.stages`; `default` where there is none. -/
def curOf (p : P12) : Fmt.M1.Stage := p.nums.stages.headD default
/-- The second stage: the second element of `p.nums.stages`; `default` where there is none. -/
def nxtOf (p : P12) : Fmt.M1.Stage := p.nums.stages.getD 1 default
/-- The numbers of the first stage's two codes: the first element of `p.idx`, else `(0, 0)`. -/
def idxOf (p : P12) : Nat × Nat := p.idx.headD (0, 0)

/-- The second stage in the form `IoppStage`: its two codes by their numbers, the second element of
`p.idx` (else `(0, 0)`), with k and h of `nxtOf p`. -/
def nextOf (p : P12) : IoppStage :=
  ⟨(p.idx.getD 1 (0, 0)).1, (p.idx.getD 1 (0, 0)).2, (nxtOf p).k, (nxtOf p).h⟩

/-- The first switch goes into the last stage: `p.nums.stages` has exactly two elements. -/
def lastOf (p : P12) : Bool := p.nums.stages.length == 2

/-- The batching's declared round: the first of the rounds that `H2U.roundsOfNums p.nums` returns;
`[]` where it returns nothing. The frame (`proximityTestKind`, Johnson/Desc/K12/Frame.lean) cuts these rounds
zipped with `p.oracles`: by reading, the same where `p.oracles` is at least as long as the rounds;
no lemma ties the two. -/
def cutBOf (p : P12) : List Fmt.DeclaredRound := ((H2U.roundsOfNums p.nums).getD []).take 1

/-- The first fold's declared rounds: the 1 + k rounds after the first of the same list, k of
`curOf p`. Not tied to the frame's cut by any lemma: as at `cutBOf`. -/
def cutFOf (p : P12) : List Fmt.DeclaredRound :=
  (((H2U.roundsOfNums p.nums).getD []).drop 1).take (1 + (curOf p).k)

/-- The first switch's two declared rounds: the next two of the same list; fewer where the list is
shorter. Not tied to the frame's cut by any lemma: as at `cutBOf`. -/
def cutSOf (p : P12) : List Fmt.DeclaredRound :=
  (((H2U.roundsOfNums p.nums).getD []).drop (1 + (1 + (curOf p).k))).take 2

/-- A shape in front of a test: the field `pass` is `.nothing`; c, g and mask are the other three
fields. -/
def frontSh (c : CoreSh) (g : Nat) (mask : Option Nat) : TestSh := ⟨c, g, .nothing, mask⟩

/-- `doorB` at a place p and a shape a, with every other argument supplied by the functions above at
p. -/
def doorOf (p : P12) (a : TestSh) : Bool :=
  doorB p (curOf p) (nxtOf p) (cutBOf p) (idxOf p) ((nextOf p).code, (nextOf p).maskCode) a

/-- `firstB` at a place p and a shape a, with every other argument supplied by the functions above
at p. -/
def firstOf (p : P12) (a : TestSh) : Bool :=
  firstB p (curOf p) (nxtOf p) (cutBOf p) (cutFOf p) (idxOf p) (nextOf p) (lastOf p)
    ((cutSOf p).headD default) ((cutSOf p).getD 1 default) a

/-! ## 2 At the ranges' test of the key file, at the full size -/

theorem switchPubB_KR : switchPubB piKRFull codesKeyFull 0 (curOf piKRFull) (nxtOf piKRFull)
    (lastOf piKRFull) ⟨(idxOf piKRFull).1, (idxOf piKRFull).2, (curOf piKRFull).k,
      (curOf piKRFull).h⟩ (nextOf piKRFull) ((cutSOf piKRFull).headD default)
    ((cutSOf piKRFull).getD 1 default) = true := by decide +kernel

/-- **What is public at the first switch holds at the place**: `SwitchPub` at `piKRFull`, at
`codesKeyFull` and at the arguments of `switchPubB_KR`. -/
theorem switchPub_KR : SwitchPub piKRFull codesKeyFull 0 (curOf piKRFull) (nxtOf piKRFull)
    (lastOf piKRFull) ⟨(idxOf piKRFull).1, (idxOf piKRFull).2, (curOf piKRFull).k,
      (curOf piKRFull).h⟩ (nextOf piKRFull) ((cutSOf piKRFull).headD default)
    ((cutSOf piKRFull).getD 1 default) := switchPub_of switchPubB_KR

/-- The tests on the plan's cuts pass: the mask has come at this place. In Lean: `batCut` at
`cutBOf`, `foldCut` at `cutFOf`, and `cutSOf` has two elements. `foldCut` is a clause of `firstB`
where the shape's field `mask` is `some`; the statement has no clause on a mask. That these cuts are
the frame's is not stated: see `cutBOf`. -/
theorem cuts_KR : batCut (cutBOf piKRFull) = true ∧
    foldCut (curOf piKRFull).k (cutFOf piKRFull) = true ∧ (cutSOf piKRFull).length = 2 := by
  decide +kernel

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.switchPubB_KR
#print axioms ProofFile.Honest.Sh.switchPub_KR
#print axioms ProofFile.Honest.Sh.cuts_KR
#print axioms ProofFile.Honest.Sh.curOf
#print axioms ProofFile.Honest.Sh.nxtOf
#print axioms ProofFile.Honest.Sh.idxOf
#print axioms ProofFile.Honest.Sh.nextOf
#print axioms ProofFile.Honest.Sh.lastOf
#print axioms ProofFile.Honest.Sh.cutBOf
#print axioms ProofFile.Honest.Sh.cutFOf
#print axioms ProofFile.Honest.Sh.cutSOf
#print axioms ProofFile.Honest.Sh.frontSh
#print axioms ProofFile.Honest.Sh.doorOf
#print axioms ProofFile.Honest.Sh.firstOf
