-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OpensFitB.lean: `OpensFit` (ColsTerm.lean in this folder: the
openings that a proximity test's rounds declare are the term's, one by one: round, depth, source) as
a test with code, `opensFitB`, a function with values in Bool; the theorem that `OpensFit` holds
where the test is true (`opensFit_of_B`), at every job; and the test's "true" at three places, by
evaluation in Lean's kernel: two small made-up ones and the written place of the key file's test on
the ranges at the full size. `OpensFit` is a hypothesis of `cols_term` (ColsTerm.lean). At the three
places the declared rounds are those of the test's block: so the test compares the term's own count
of rounds and of trees sent with the rounds that the description's text computes from the place's
numbers. Definitions with code, statements and proofs, and evaluations (`#guard`).

In the list: a place (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a proximity test,
among them its stages (`Fmt.M1.Stage`, Fmt/M1Types.lean), the list `p.nums.stages`. A job
(`TestJob`, Test.lean in this folder) is what a caller supplies for its test, among it the place
`J.p` and the field `J.fresh`: who sent the first fold's fresh table. Where it is `none`, the first
fold sends its own table; otherwise the fresh table has come earlier. The term is `testAll`
(Test.lean). Its openings are `opensTest stages depths` (ColsTerm.lean): each is a round's number, a
tree's depth and the tree's origin (`From`, TermOpens.lean in this folder): `old k`, the job's tree
number k, or `sent r`, the tree that the test's round number r sends. A source (`Fmt.TreeSource`,
Decl/Declared.lean) is the name by which a declared round (`Fmt.DeclaredRound`, same file) opens a tree;
`own n` is tree number n of those that this chain sends. The declared openings are
`planOpens decls 0` (PlanOpens.lean in this folder). The test's block is `proximityTestKind guardedProximityTestParts p`
(Johnson/Desc/K12/Frame.lean, JoinGuarded.lean); its field `rounds` is taken from the list
`H2U.roundsOfNums p.nums` (Johnson/Desc/K12/TestEntries.lean).

  `opensFit_of_B`: at every job J and at all decls, depths, src₀ and sent: if `opensFitB` is true at
    `J.fresh.isNone`, at the stages `J.p.nums.stages` and at these four, then
    `OpensFit J decls depths (fun k => src₀.getD k (.own 0)) sent` holds
  `opensFit_KR`: at every job J with `J.p = piKRFull` (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean)
    whose fresh table has come earlier (`J.fresh.isNone = false`): `OpensFit` at the block's
    declared rounds, the depths [22], the sources [`own 1`] and 2 trees sent before the test
  `opensFitB_KR`: the test is true at `false`, at the stages and the block's declared rounds of
    `piKRFull` and at these depths, sources and count
  `opensFit_toy`: `OpensFit` at the job `Toy.J` (Toy.lean in this folder), at its block's declared
    rounds, the depths [4], the sources [`own 0`] and 1 tree sent before the test
  `opensFit_came`: `OpensFit` at the job `(ToyCame.came 0).J` (ToyCame.lean in this folder), at its
    block's declared rounds, the depths [5, 5, 4, 4], the sources [`own 0`, `own 1`, `own 2`,
    `own 3`] and 4 trees sent before the test
  `opensFitB own stages decls depths src₀ sent`: a definition: the test. Its arguments: whether the
    first fold sends its own table · the stages · the declared rounds · the depths and the sources
    of the job's trees, as lists · how many trees the chain has sent before the test. It is true
    where three things hold. The declared openings are the term's, one by one, with each origin
    replaced by its source by `srcOfB`. No declared round has a stored part. Every opening of the
    term with the origin `old k` has k below the length of depths, and its depth is entry k of
    depths; every one with the origin `sent r` has r below the number of declared rounds, and
    `depthOf own stages r` is `some`
  `srcOfB own stages src₀ sent`: a definition: an origin's source: `srcBy` (ColsTerm.lean) with
    code, at a list of sources. `old k` has entry k of src₀, and `own 0` where src₀ has no entry k;
    `sent r` has `own (sent + c)`, where c counts the rounds below r at which `depthOf` is `some`
  `depthOf own stages i`: a definition: the depth of the tree that round number i sends, if any:
    the text of `depthAt` (Test.lean), with own and stages for `J.fresh.isNone` and the job's stages

By what. `opensFit_of_B` unfolds the test, turns `&&`, `decide` and `List.all` into propositions by
`simp only`, and gives the four fields of `OpensFit` one by one. At the job's values `srcOfB` is
`srcBy` by `rfl` at each of the two origins: there `depthOf` is `depthAt`, and the count is
`sentBefore` (SentTables.lean in this folder). No lemma of another file of the library is called.
That the test is true is proved three times by `decide +kernel`: in `opensFitB_KR`, and inside
`opensFit_toy` and `opensFit_came`, which are `opensFit_of_B` at it. `opensFit_KR` rewrites by its
two hypotheses and is `opensFit_of_B` at `opensFitB_KR`.

What the `#guard` lines evaluate, by Lean's evaluator. Four negative tests at the key file's place,
each with one argument of `opensFitB_KR` changed, at which the test is false: another count of
trees sent before the test (3) · another depth (21) · another source for the job's tree (`own 0`) ·
`true` for "the first fold sends its own table". And one evaluation at which it is true: at the
place of ToyTrees.lean in this folder (`ToyTrees.p`), whose first fold sends its own table, at the
depths [5, 4, 4], the sources [`own 0`, `own 1`, `own 2`] and 2 trees sent before the test: there
the fresh table's tree is listed with the source that the rounds declare.

Limits.
- `opensFitB` is a function of its six arguments. It reads no state, no coin and no input.
- Only one direction is proved: where the test is true, `OpensFit` holds. That the test is true
  wherever `OpensFit` holds is not stated.
- This file proves `OpensFit` at three values only: `Toy.J`, `(ToyCame.came 0).J`, and every job
  with `J.p = piKRFull` whose fresh table has come earlier. All three are in the case in which the
  fresh table has come earlier. In the case in which the first fold sends its own table there is one
  `#guard` only, at `ToyTrees.p`: no theorem, and so no value here that meets `OpensFit`. At no
  other place does this file prove `OpensFit` or evaluate the test.
- Where the first fold sends its own table the test can be true, but `cols_term` does not apply
  there: its other hypothesis `OldAt` (ColsTerm.lean) asks that every tree of the job was sent
  before the test, and the fresh table's tree is sent in it.
- The depths, the sources and the count of trees sent are arguments; at the three places they are
  values written in this file. That the depths are those of the job's trees (the hypothesis hdep of
  `cols_term`), that these trees are at these sources (`OldAt`), and that the chain has sent so
  many trees before the test is not stated here.
- No clause of `opensFitB` compares the length of src₀ with that of depths: where src₀ is the
  shorter, the source `own 0` is taken for the trees that it does not list.
- The limits of Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean hold. Some of that place's numbers are
  a print's word: for these the print of a run of Lean's evaluator is trusted; that file's limits
  name them. Two of them are the fields `first` and `free` of `piKRFull.nums`, from which
  `H2U.roundsOfNums` takes the trees that the first round of positions opens and the sources of the
  trees that the test sends: it is with these that `opensFitB_KR` compares the depth 22, the source
  `own 1` and the count 2. That a description makes this place at any public files is not stated
  here.
- The places of Toy.lean, ToyCame.lean and ToyTrees.lean are small and made up.
- A `#guard` is an evaluation by Lean's evaluator, outside the kernel: it leaves no theorem.
- All four negative tests are at the key file's place; none changes the stages or the declared
  rounds.
- Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm
import Johnson.Desc.ProofFile.Honest.K12.ToyCame
import Johnson.Desc.K12.Law.PlaceKeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member (piKRFull)

variable {W X : Type}

/-- The depth of the tree that round number i sends, if any: the text of `depthAt` (Test.lean), with
own and stages for `J.fresh.isNone` and the job's stages. -/
def depthOf (own : Bool) (stages : List Fmt.M1.Stage) (i : ℕ) : Option ℕ :=
  (none :: depths own stages).getD i none

/-- An origin's source, with code: `srcBy` (ColsTerm.lean) at a list of sources. Where src₀ has no
entry k, `old k` has the source `own 0`. -/
def srcOfB (own : Bool) (stages : List Fmt.M1.Stage) (src₀ : List Fmt.TreeSource) (sent : ℕ) :
    From → Fmt.TreeSource
  | .old k => src₀.getD k (.own 0)
  | .sent r => .own (sent + ((List.range r).filter fun i => (depthOf own stages i).isSome).length)

/-- **`OpensFit` as a test.** own: whether the first fold sends its own table. depths, src₀: the
depths and the sources of the job's trees. sent: how many trees the chain has sent before the
test. -/
def opensFitB (own : Bool) (stages : List Fmt.M1.Stage) (decls : List Fmt.DeclaredRound)
    (depths : List ℕ) (src₀ : List Fmt.TreeSource) (sent : ℕ) : Bool :=
  decide (planOpens decls 0 =
    (opensTest stages depths).map fun x => (x.1, x.2.1, srcOfB own stages src₀ sent x.2.2)) &&
  decls.all (·.stored.isEmpty) &&
  (opensTest stages depths).all fun x =>
    match x.2.2 with
    | .old k => decide (k < depths.length) && decide (x.2.1 = depths.getD k 0)
    | .sent r => decide (r < decls.length) && (depthOf own stages r).isSome

theorem opensFit_of_B (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : List Fmt.TreeSource) (sent : ℕ)
    (h : opensFitB J.fresh.isNone J.p.nums.stages decls depths src₀ sent = true) :
    OpensFit J decls depths (fun k => src₀.getD k (.own 0)) sent := by
  unfold opensFitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, fun d hd => List.isEmpty_iff.1 (h2 d hd), fun x hx k hk => ?_, fun x hx r hr => ?_⟩
  · rw [h1]
    refine List.map_congr_left fun x _ => ?_
    cases x.2.2 <;> rfl
  · have := h3 x hx
    rw [hk] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := h3 x hx
    rw [hr] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

/-- At the job of Toy.lean, whose fresh table has come earlier. -/
theorem opensFit_toy : OpensFit Toy.J (proximityTestKind guardedProximityTestParts Toy.J.p : Block T12 Unit).rounds [4]
    (fun k => [Fmt.TreeSource.own 0].getD k (.own 0)) 1 :=
  opensFit_of_B _ _ _ _ _ (by decide +kernel)

/-- At the job of ToyCame.lean, whose fresh table has come earlier. -/
theorem opensFit_came : OpensFit (ToyCame.came 0).J
    (proximityTestKind guardedProximityTestParts (ToyCame.came 0).J.p : Block T12 Unit).rounds [5, 5, 4, 4]
    (fun k => [Fmt.TreeSource.own 0, .own 1, .own 2, .own 3].getD k (.own 0)) 4 :=
  opensFit_of_B _ _ _ _ _ (by decide +kernel)

theorem opensFitB_KR : opensFitB false piKRFull.nums.stages
    (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds [22] [.own 1] 2 = true := by decide +kernel

/-- **At the written place of the key file's test on the ranges:** at every job with this place
whose fresh table has come earlier. -/
theorem opensFit_KR (J : TestJob W X) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) :
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds [22]
      (fun k => [Fmt.TreeSource.own 1].getD k (.own 0)) 2 :=
  opensFit_of_B _ _ _ _ _ (by rw [hfr, hJ]; exact opensFitB_KR)

-- Negative tests at the key file's place: each has one argument of `opensFitB_KR` changed.
#guard !opensFitB false piKRFull.nums.stages (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds [22]
  [.own 1] 3
#guard !opensFitB false piKRFull.nums.stages (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds [21]
  [.own 1] 2
#guard !opensFitB false piKRFull.nums.stages (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds [22]
  [.own 0] 2
#guard !opensFitB true piKRFull.nums.stages (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds [22]
  [.own 1] 2
-- At a place whose first fold sends its own table the test can be true: the fresh table's tree is
-- listed with the source that the rounds declare, the first after those sent before the test.
#guard opensFitB true ToyTrees.p.nums.stages (proximityTestKind guardedProximityTestParts ToyTrees.p : Block T12 Unit).rounds
  [5, 4, 4] [.own 0, .own 1, .own 2] 2

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.opensFit_of_B
#print axioms ProofFile.Honest.K12.opensFit_toy
#print axioms ProofFile.Honest.K12.opensFit_came
#print axioms ProofFile.Honest.K12.opensFitB_KR
#print axioms ProofFile.Honest.K12.opensFit_KR
#print axioms ProofFile.Honest.K12.depthOf
#print axioms ProofFile.Honest.K12.srcOfB
#print axioms ProofFile.Honest.K12.opensFitB
