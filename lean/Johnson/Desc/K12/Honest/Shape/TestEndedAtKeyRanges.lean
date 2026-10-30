-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestEndedAtKeyRanges.lean: at the ranges' test of the key file at the
full size (`piKRFull`, Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), "the test has run to its end"
is met on the shape: the computable test `endedB` (Johnson/Desc/ProofFile/Honest/K12/Ended.lean) is
true at the written shape in front of that test (`shKRFull`, a closed term,
Johnson/Desc/K12/Honest/Shape/TestAtKeyRangesShape.lean). So, where the test's block
(`proximityTestKind guardedProximityTestParts piKRFull`, Johnson/Desc/K12/Frame.lean and JoinGuarded.lean) accepts at a structure of
that shape, `testEnded` (Johnson/Desc/Key/Ranges.lean) is true of the structure that the block
returns. `leaveRanges` (Johnson/Desc/Key/Chain1.lean), the function by which the key file's first
chain writes the test's result back into its state, returns where `testEnded` is true and refuses
otherwise. One definition, five closed facts, and two theorems that are general in the structure,
the rounds and the columns.

Terms. The ranges' test is the proximity test on the group of the lookups' own message, in the key
file's first chain (Ranges.lean); `piKRFull` is its place, or plan (`P12`, Frame.lean). The
structure inside a proximity test is `T12` (Johnson/Desc/K12/Join.lean). A thin shape is `ThinSh`
(Johnson/Desc/K12/Honest/Shape/TestCore.lean), with four fields: `core`, the shape of statement,
book and count of roots (`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean); `g`, the number of the
group under test; `pass`, a reduced form of what passes from a part of the test to the next; `mask`,
in the words of `T12`: the number of the message that holds the present stage's mask, if it has
come. `thinSh t` is the thin shape of t, and `testThin` is the test as a function on thin shapes
(both in TestCore.lean). `endedThin` (Ended.lean) is `testEnded` on a thin shape. `endedB p a` says
that `testThin p a` returns and that `endedThin` is true of what it returns. "In front of" the test
means before it, "behind" the test after it.

  `ended_KR`: `endedB piKRFull frontKR = true`
  `ended_at_KR`, `leaves_at_KR`: at every structure t₀ of the thin shape `frontKR`, at all rounds
    rs and columns gs: where the block's decision returns t', `testEnded t' = true`; and
    `leaveRanges s t'` returns at every state s of the first chain (`FirstState`,
    Johnson/Desc/Key/Link.lean)
  `frontKR`: a definition: the thin shape in front: the written core, the group 0, nothing passed,
    the mask 2. In Lean: `⟨shKRFull, 0, .nothing, some 2⟩`
  `ended_KR_front`, `ended_KR_unspent`, `ended_KR_open`, `ended_KR_pass`: negative tests, each by
    the kernel: in front of the test `endedThin` is false, for three causes at once (the group has
    not begun; it holds open rows; the first fold's mask is neither sampled nor spent); at the
    shape behind the test, turned in one thing, it is false: the first fold's mask not spent (a
    message neither sampled nor spent); an open row in the last group; something still passed on.
    The three causes are by reading of `shKRFull`: the statement of `ended_KR_front` has only
    `false`. The other three statements end in `some false`: they also say that `testThin` returns
    at `frontKR`

By what. `ended_KR` and the four negative tests are closed by `decide +kernel`. `ended_at_KR` is
`ended_of_accept`, and `leaves_at_KR` is `leaves_ranges` (both in Ended.lean), at `piKRFull` and at
`ended_KR` rewritten by the hypothesis on the shape. The two hypotheses of these lemmas on the
plan, `piKRFull.early = true` and `piKRFull.answers = 1`, are closed by `rfl`.

Hypotheses. Of `ended_at_KR` and `leaves_at_KR`: hs: the thin shape of t₀ is `frontKR`; h: the
decision of the block at t₀, rs and gs returns t'.

Limits.
- All limits of TestAtKeyRangesShape.lean hold here too: the shape `shKRFull` rests only on printed
  output, of a run on shapes that rests on stand-ins; no theorem says that a run of the description
  comes to a structure of this shape.
- That the block accepts is a hypothesis.
- No t₀, rs and gs that meet the two hypotheses together are shown here: neither at this place nor
  at a small made-up plan.
- The negative tests change the shape behind the test in their own statements: they show that three
  of the four clauses of `endedThin` can fail there (never changed: "the group's number is below
  the number of groups"; nor, of the third clause, the half "has begun"), not that a run comes to
  such a shape.
- "Nothing is left untested" (`ChainEnd.NothingLeft`) fails behind this same test
  (Johnson/Desc/K12/Honest/Shape/TestLeftAtKeyRanges.lean): the index masks' message is sampled and
  names no group. `testEnded` asks of a message that it is sampled or spent as a mask, and so does
  not mind. `ChainEnd.NothingLeft` is defined in Johnson/Desc/ChainEndLaw.lean.
  TestLeftAtKeyRanges.lean is not in this library.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRangesShape
import Johnson.Desc.ProofFile.Honest.K12.Ended

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh
open H2K.Member (piKRFull)
open ProofFile.Honest.K12 (endedThin endedB ended_of_accept leaves_ranges)

/-- The thin shape in front of the ranges' test: the fields are `core := shKRFull`, `g := 0`,
`pass := .nothing`, `mask := some 2`. -/
def frontKR : ThinSh := ⟨shKRFull, 0, .nothing, some 2⟩

/-- **The test on the shape in front is true**: `testThin piKRFull frontKR` returns, and `endedThin`
is true of what it returns. -/
theorem ended_KR : endedB piKRFull frontKR = true := by decide +kernel

/-! Negative tests -/

/-- In front of the test `endedThin` is false. -/
theorem ended_KR_front : endedThin frontKR = false := by decide +kernel

/-- Behind the test, the first fold's mask not spent: a message neither sampled nor spent. In Lean:
`endedThin` is false of what `testThin` returns at `frontKR`, with the field `spent` of message 2
set to `false`. -/
theorem ended_KR_unspent : ((testThin piKRFull frontKR).map fun a =>
    endedThin { a with core := { a.core with st := { a.core.st with
      oracles := modAt a.core.st.oracles 2 fun o => { o with spent := false } } } }) =
    some false := by decide +kernel

/-- Behind the test, an open row in the last group. In Lean: `endedThin` is false of what `testThin`
returns at `frontKR`, with the field `kinds` of group 3 set to `[.plain]`. That there are four
groups behind the test is `core_KR` (TestAtKeyRangesShape.lean). -/
theorem ended_KR_open : ((testThin piKRFull frontKR).map fun a =>
    endedThin { a with core := { a.core with st := { a.core.st with
      groups := modAt a.core.st.groups 3 fun G => { G with kinds := [.plain] } } } }) =
    some false := by decide +kernel

/-- Behind the test, something still passed on. In Lean: `endedThin` is false of what `testThin`
returns at `frontKR`, with the field `pass` set to `.switched`. -/
theorem ended_KR_pass : ((testThin piKRFull frontKR).map fun a =>
    endedThin { a with pass := .switched }) = some false := by decide +kernel

/-- **At every structure of that thin shape: an accept gives "the test has run to its end"**:
`testEnded` is true of the structure t' that the block returns. -/
theorem ended_at_KR (t₀ t' : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hs : thinSh t₀ = frontKR)
    (h : (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).decide t₀ rs gs = .ok t') :
    testEnded t' = true :=
  ended_of_accept piKRFull rfl rfl t₀ t' rs gs h (hs ▸ ended_KR)

/-- So `leaveRanges` returns at t', at every state s of the key file's first chain. -/
theorem leaves_at_KR (t₀ t' : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hs : thinSh t₀ = frontKR)
    (h : (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).decide t₀ rs gs = .ok t') (s : FirstState) :
    ∃ s', leaveRanges s t' = .ok s' :=
  leaves_ranges piKRFull rfl rfl t₀ t' rs gs h (hs ▸ ended_KR) s

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.ended_KR
#print axioms ProofFile.Honest.Sh.ended_KR_front
#print axioms ProofFile.Honest.Sh.ended_KR_unspent
#print axioms ProofFile.Honest.Sh.ended_KR_open
#print axioms ProofFile.Honest.Sh.ended_KR_pass
#print axioms ProofFile.Honest.Sh.ended_at_KR
#print axioms ProofFile.Honest.Sh.leaves_at_KR
#print axioms ProofFile.Honest.Sh.frontKR
