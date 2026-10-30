-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestAtKeyRangesShape.lean: the public tests of the door and of the
first stage, and the test's function on shapes, evaluated at one place of a proximity test: the
ranges' test of the key file at the full size (`piKRFull`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), at a written shape in front of it (`shKRFull`). One
definition, a closed term, and five closed facts, each by an evaluation in Lean's kernel. Nothing is
general: every statement is at closed terms: that place, that shape, or that shape changed in one
thing.

Terms, as in the heads of TestAtKeyRanges.lean and TestSwitchPub.lean (this folder). The ranges'
test is the proximity test on the group of the lookups' own message, in the key file's first chain
(Johnson/Desc/Key/Ranges.lean). A place, or plan, is a `P12` (Johnson/Desc/K12/Frame.lean: the
numbers of the place of a test). The parts of a test are the front, the batching, in each stage but
the last the fold, the switch and the batching after it, and the base case; the stages are
`p.nums.stages`. The door is the word of Johnson/Desc/K12/Honest/Shape/TestDoor.lean for the front,
the batching, the frame's question after it and the first fold; the frame is the test's own (`proximityTestKind`,
Frame.lean), not the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean). `doorB`
(TestDoor.lean) is what the door asks of the shape, as one Bool. `firstB` (TestSwitchPub.lean) is
the conjunction of `doorB`, of `switchPubB` (what is public at the first switch) and of two tests on
the declared rounds of the batching and of the first fold. The core's shape is a `CoreSh`
(Johnson/Desc/Ground/Shape/Core.lean): a statement (`StSh`: codes, oracle messages, groups), a book
of trees (`BookSh`: trees, and the place of each message in them) and a count of roots, with every
field element left out. A shape in front of a test is a `TestSh`
(Johnson/Desc/K12/Honest/Shape/Test.lean), here `frontSh c g mask` (TestAtKeyRanges.lean). "The
place's own letters" are the other arguments of `doorB` and `firstB`, each as a function of the
place. "In front of" the test means before it, "behind" the test after it; "premises" are
hypotheses.

  `door_KR`, `first_KR`: `doorB` and `firstB` with the place's own letters (`doorOf`, `firstOf`,
    Johnson/Desc/K12/Honest/Shape/TestAtKeyRanges.lean) are true at that shape, the group 0 and the
    mask's message 2. In Lean: `doorOf piKRFull (frontSh shKRFull 0 (some 2)) = true`, and the same
    with `firstOf`
  `core_KR`: `testCore` (Johnson/Desc/K12/Honest/Shape/TestCore.lean) returns a shape at `piKRFull`,
    `shKRFull`, 0 and `some 2`. Of that shape, the one behind the test, the statement has: nine
    messages; four groups, each begun and without an open row, with code, mask code and members
    `(12, 11, [1])`, `(13, 12, [3])`, `(14, 13, [5])` and `(15, 14, [7])`; five trees; five roots.
    By reading, the four pairs of codes are `piKRFull.idx`: the stages' codes
  `first_KR_no`: controls: `firstOf` is false at the group 1; with no mask named; with one open row
    less; with one root more. In Lean: four equations with `false`, each at `first_KR`'s arguments
    changed in one thing: 1 for 0 (the shape has one group, number 0); `none` for `some 2`; the
    first element dropped from the group's `kinds`; `roots := 3` for 2
  `codes_KR`: the codes of `shKRFull` are the key file's table of codes (`codesKeyFull`,
    Johnson/Desc/K12/Law/PlacesKeyFull.lean). In Lean: `shKRFull.st.codes = codesKeyFull`
  `shKRFull`: a definition: the core's shape in front of the ranges' test, as a closed term: three
    messages (the index masks'; the lookups' own message, the one member of group 0; the first
    fold's mask, which rides in that message's tree), one group with 980 open rows, all of the kind
    "plain", two trees, two roots. In Lean, of the third message: tree 1 has `parts := [1, 2]`, and
    the place of message 2 is `(1, 1)`

By what. The five theorems are closed by `decide +kernel`; no lemma is called. The kernel evaluates
`doorOf`, `firstOf` and `frontSh` (TestAtKeyRanges.lean) and `testCore` (TestCore.lean) at the
closed terms `piKRFull`, `codesKeyFull` and `shKRFull`.

Limits.
- The shape was copied by a program from the printed output of Lean's evaluator: a run on shapes of
  the fifteen guards before the ranges' test, from the first chain's first shape at the sizes of a
  key that the library states in Lean [the printed output is not in this library; its sha256 is
  5510b39f568ceebfbe47499c0f9457bbfa80adefc4ab59ab492b52d48f8bc25f; it leaves the 980 kinds out,
  which were evaluated separately]. A guard is what a verifier's step asks of the structure, as
  against its tests on values (Core.lean). The number fifteen is stated in no Lean text here.
- That run rests on stand-ins: its one-time parameters were put together by hand, and the groups
  that are told at two sendings were guessed.
- No theorem here says that a run of the description comes to a structure of this shape.
- What the three messages are called (the index masks'; the lookups' own; the first fold's mask) is
  a word of these comments: the term has numbers and flags only.
- All limits of PlaceKeyRangesFull.lean hold here too. Among them: the numbers of the closed place
  were copied by a program from another printed output, and by that file's head three numbers rest
  on printed output only (`first`, `free`, `start`). `doorB` compares `p.nums.free` with the shape's
  `roots` (`frontOwesB`, TestDoor.lean): here both sides rest on printed output.
- All limits of TestAtKeyRanges.lean hold here too. Among them: `doorOf` and `firstOf` take the
  declared rounds from `cutBOf`, `cutFOf` and `cutSOf`, which no lemma ties to the frame's cut.
- The other premises of the first stage's law (the first mark; that the rows taken in are plain; the
  named test on the open rows; the view's form; the reading's accept) are not here. In Lean: the law
  is `first_of_B` (TestSwitchPub.lean), these are its hypotheses ht, hp, hv, fB, fF, hfit, hans and
  hread, and it is not called here. No structure (`T12`, Johnson/Desc/K12/Join.lean) of this shape
  is written here.
- `core_KR` has numbers of the returned shape, not the shape: nothing on the messages but their
  number, on the groups' field `kept`, on the trees but their number, on the places or on the codes.
  By the head of TestCore.lean, `testCore` asks fewer guards than the test's sub-protocol: that it
  returns says nothing on whether the sub-protocol accepts.
- `door_KR`, `core_KR` and `codes_KR` have no negative test here. `first_KR_no` does not say which
  clause of `firstB` is false at each of its four arguments.
- "Public" is a word of these comments, for the plan, the codes, the declared rounds and the shape.
  No statement in Lean here says that any of them is public.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Member (piKRFull codesKeyFull)

/-- The core's shape in front of the key file's ranges' test, at the full size. By position, in the
fields' own order (Johnson/Desc/Ground/Shape/Core.lean): the statement's shape (the codes: base,
mask, each as log-length, message length, tail; the messages: shape [code, main rows, main degree,
mask rows, mask code, answers], sampled, number of sample rows, pad, groups, ledger [next, left,
rows, log of the rows, closed], spent; the groups: code, mask code, members, kept, the open rows'
kinds, begun); the book's shape (the trees: shape [two log-lengths, main symbols, mask symbols],
number, source, parts, opened at one list only, lists; the places); the roots. The inner structures
`Code`, `OracleShape`, `Ledger` and `TreeShape` are in OnBytes/Iop/Ground.lean; 4294967295 is `noId`
there: no code. The term was copied by a program from printed output: see the head's limits. -/
def shKRFull : CoreSh :=
  ⟨⟨⟨#[⟨24, 4194304, 97⟩, ⟨21, 131072, 52⟩, ⟨17, 8192, 52⟩, ⟨13, 512, 52⟩, ⟨14, 512, 49⟩, ⟨22,
  262144, 98⟩, ⟨18, 16384, 49⟩, ⟨14, 1024, 49⟩, ⟨15, 1024, 39⟩, ⟨15, 2048, 49⟩, ⟨13, 256, 41⟩, ⟨15,
  256, 29⟩, ⟨22, 262144, 49⟩, ⟨19, 16384, 39⟩, ⟨17, 2048, 33⟩, ⟨20, 2048, 25⟩], #[⟨13, 64, 146⟩,
  ⟨12, 256, 52⟩, ⟨14, 1024, 49⟩, ⟨14, 128, 49⟩, ⟨13, 64, 49⟩, ⟨15, 512, 39⟩, ⟨13, 256, 49⟩, ⟨15,
  128, 49⟩, ⟨14, 64, 49⟩, ⟨13, 64, 41⟩, ⟨15, 256, 29⟩, ⟨16, 4096, 49⟩, ⟨17, 2048, 39⟩, ⟨17, 1024,
  33⟩, ⟨20, 4096, 25⟩]⟩, [⟨⟨4294967295, 0, 1, 1, 6, 1⟩, true, 1, [(.mask, 255)], [], some ⟨48, 207,
  1, 0, false⟩, false⟩, ⟨⟨12, 2, 1, 9, 11, 1⟩, true, 1, [(.mask, 65528)], [0], some ⟨62017, 1978, 9,
  4, false⟩, false⟩, ⟨⟨4294967295, 0, 1, 16, 11, 0⟩, false, 0, [], [], none, false⟩], [⟨12, 11, [1],
  [false], List.replicate 980 .plain, false⟩]⟩, ⟨[⟨⟨13, 13, #[0], #[3]⟩, 0, .own 0, [0], false, 0⟩,
  ⟨⟨22, 16, #[2, 0], #[27, 48]⟩, 1, .own 1, [1, 2], true, 0⟩], [(0, 0), (1, 0), (1, 1)]⟩, 2⟩

theorem codes_KR : shKRFull.st.codes = codesKeyFull := by decide +kernel

/-- **The door's Bool is true**: `doorOf` at `piKRFull` and at `frontSh shKRFull 0 (some 2)`. -/
theorem door_KR : doorOf piKRFull (frontSh shKRFull 0 (some 2)) = true := by decide +kernel

/-- **All that is public in front of the first stage, as one Bool, is true**: `firstOf` at the same
arguments. The other hypotheses of `first_of_B` (Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean)
are not shown here. -/
theorem first_KR : firstOf piKRFull (frontSh shKRFull 0 (some 2)) = true := by decide +kernel

/-- What the test's function on shapes, `testCore`, returns there, in numbers: the number of
messages; of each group the code, the mask code, the members, whether its test has begun and the
number of open rows; the number of trees; the count of roots. Compared by `==`. The rest of the
returned shape is not in the statement. That `testCore` returns does not say that the test's
sub-protocol accepts. -/
theorem core_KR : ((testCore piKRFull shKRFull 0 (some 2)).map (fun c =>
      (c.st.oracles.length, c.st.groups.map (fun G => (G.code, G.maskCode, G.members, G.inRun,
        G.kinds.length)), c.book.trees.length, c.roots)) ==
    some (9, [(12, 11, [1], true, 0), (13, 12, [3], true, 0), (14, 13, [5], true, 0),
      (15, 14, [7], true, 0)], 5, 5)) = true := by decide +kernel

/-- Controls: `firstOf` is false at the group 1; with no mask named; with one open row less; with
one root more. The statement does not say which clause of `firstB` is false at each. -/
theorem first_KR_no :
    firstOf piKRFull (frontSh shKRFull 1 (some 2)) = false ∧
    firstOf piKRFull (frontSh shKRFull 0 none) = false ∧
    firstOf piKRFull (frontSh { shKRFull with st := { shKRFull.st with
      groups := shKRFull.st.groups.map fun G => { G with kinds := G.kinds.drop 1 } } } 0
        (some 2)) = false ∧
    firstOf piKRFull (frontSh { shKRFull with roots := 3 } 0 (some 2)) = false := by
  decide +kernel

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.codes_KR
#print axioms ProofFile.Honest.Sh.door_KR
#print axioms ProofFile.Honest.Sh.first_KR
#print axioms ProofFile.Honest.Sh.core_KR
#print axioms ProofFile.Honest.Sh.first_KR_no
#print axioms ProofFile.Honest.Sh.shKRFull
