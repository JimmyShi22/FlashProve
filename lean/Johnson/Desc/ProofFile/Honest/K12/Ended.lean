-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Ended.lean: where the decision of a proximity test's block
accepts, that the test has run to its end (`testEnded`, Johnson/Desc/Key/Ranges.lean) follows from a
computable test, `endedB`, on the plan and on the shape of the state before the test. The block is
`proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/Frame.lean, JoinGuarded.lean): the proximity test as a sub-protocol
(`Block`, Johnson/Desc/Block.lean) on a state of type `T12` (Johnson/Desc/K12/Join.lean). The plan p
(`P12`, Johnson/Desc/K12/Frame.lean) has the numbers of the test's place. The two main theorems hold
at every plan with `p.early = true` and `p.answers = 1`, and at all states, rounds and columns. Two
computable definitions and three theorems, with their proofs.

What for. In a key file's first chain (`firstChain`, Johnson/Desc/Key/Chain1.lean) the test on the
ranges (the proximity test on the group of the lookups' own message) is wrapped by `rangesTest`
(Ranges.lean) with `leaveRanges` (Chain1.lean). `leaveRanges` is handed the chain's state and the
test's state after the test, and it returns only where `testEnded` is true of the latter. The clause
`accepts` of `K12At` (SaysYesK12.lean in this folder) has two halves: the block's decision returns
some t'; and `leave st t'` returns. Where `leave` is `leaveRanges`, `leaves_ranges` gives the second
half from the first half, the two hypotheses on the plan and `endedB`.

How. `testEnded t` reads of the state t: `t.pass` (what is passed from one part of the test to the
next); `t.g` (the number of the group under test); the number of groups; of each group from number
`t.g` on, `inRun` and whether it has an open row; of each oracle message, `sampled` and
`spentAsMask`. All of these are in the thin shape `thinSh t` (`ThinSh`,
Johnson/Desc/K12/Honest/Shape/TestCore.lean). Its fields are `core` (`CoreSh`,
Johnson/Desc/Ground/Shape/Core.lean: the statement, the book of trees and the count of roots with
every field element left out), `g`, `pass` (`ThinPass`: what `thinPass` keeps of `t.pass`) and
`mask`. Under the two hypotheses on the plan, where the block accepts at t₀ and returns t', the thin
shape after the test is computed from the plan and the thin shape before it:
`testThin p (thinSh t₀) = some (thinSh t')` (`k12_thin`, TestCore.lean).

  `ended_of_accept`: the masks come early · one answer · the block's decision accepts at t₀ and
    returns t' · `endedB` at t₀'s thin shape ⟹ `testEnded t' = true`
  `leaves_ranges`: under the same four hypotheses, at every state s of the chain (`FirstState`,
    Johnson/Desc/Key/Link.lean), `leaveRanges s t'` returns
  `testEnded_thin`: `testEnded t = endedThin (thinSh t)`, at every t
  `endedThin`: a definition: the four clauses of `testEnded`, read off a thin shape
  `endedB`: a definition: the test on the thin shape before the proximity test: `testThin p a`
    returns a thin shape, and `endedThin` is true of it; false where `testThin p a` is `none`

By what. `ended_of_accept` rewrites `endedB` by `k12_thin` (TestCore.lean) and then uses
`testEnded_thin`. `testEnded_thin` unfolds `thinPass` (TestCore.lean) and the readers `stSh`,
`grpSh` and `orcSh` (Core.lean). `leaves_ranges` unfolds `leaveRanges` and uses `ended_of_accept`.

Hypotheses of `ended_of_accept` and `leaves_ranges`. `he`: `p.early = true` (in the list: the masks
come early). `ha`: `p.answers = 1` (in the list: one answer). `h`: the block's `decide` at t₀, at
the rounds `rs` and the groups of columns `gs`, returns `.ok t'`. `hB`:
`endedB p (thinSh t₀) = true`.

Limits. `endedB` is a hypothesis: it is shown of no shape here (at one written shape: `ended_KR`,
Johnson/Desc/K12/Honest/Shape/TestEndedAtKeyRanges.lean, with that file's limits). It reads no
value. By type that is so of field elements only: a number in a shape can be made of a value (the
limits of Core.lean). `leaves_ranges` says that `leaveRanges` returns, and nothing of what it
returns. Nothing is stated at `K12At` here: its `leave` is a free parameter. The block is taken at
the type `Block T12 Unit`; `firstChain` has it at `Block T12 Claim`, and no statement here carries
the decision from one type to the other. Nothing on whether the block accepts. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh
open ProofFile.Honest.Sh (ThinSh ThinPass thinSh thinPass testThin k12_thin)

/-- The four clauses of `testEnded` (Johnson/Desc/Key/Ranges.lean), read off a thin shape. -/
def endedThin (a : ThinSh) : Bool :=
  (match a.pass with
    | .nothing => true
    | _ => false) &&
  decide (a.g < a.core.st.groups.length) &&
  ((a.core.st.groups.drop a.g).all fun G => G.inRun && G.kinds.isEmpty) &&
  a.core.st.oracles.all fun o => o.sampled || o.spent

theorem testEnded_thin (t : T12) : testEnded t = endedThin (thinSh t) := by
  have e1 : (match t.pass with
      | .nothing => true
      | _ => false) = (match thinPass t.pass with
      | .nothing => true
      | _ => false) := by cases t.pass <;> rfl
  have e2 : (stSh t.st).groups.length = t.st.groups.size := by simp [stSh]
  have e3 : ((stSh t.st).groups.drop t.g).all (fun G => G.inRun && G.kinds.isEmpty) =
      (t.st.groups.toList.drop t.g).all fun G => G.inRun && G.rows.isEmpty := by
    show ((t.st.groups.toList.map grpSh).drop t.g).all _ = _
    rw [← List.map_drop, List.all_map]
    refine congrArg (fun f => (t.st.groups.toList.drop t.g).all f) ?_
    funext G
    simp [grpSh]
  have e4 : (stSh t.st).oracles.all (fun o => o.sampled || o.spent) =
      t.st.oracles.all fun o => o.sampled || o.spentAsMask := by
    show (t.st.oracles.toList.map orcSh).all _ = _
    rw [List.all_map, ← Array.all_toList]
    rfl
  unfold testEnded endedThin
  show _ = ((match thinPass t.pass with
      | .nothing => true
      | _ => false) && decide (t.g < (stSh t.st).groups.length) &&
    ((stSh t.st).groups.drop t.g).all (fun G => G.inRun && G.kinds.isEmpty) &&
    (stSh t.st).oracles.all fun o => o.sampled || o.spent)
  rw [← e1, e2, e3, e4]
  rfl

/-- The test on the thin shape before the proximity test: `testThin p a` returns a thin shape, and
`endedThin` is true of it. It is false where `testThin p a` is `none`. -/
def endedB (p : P12) (a : ThinSh) : Bool := (testThin p a).any endedThin

/-- **Where the block accepts and `endedB` is true of the thin shape before the test, the test has
run to its end.** Hypotheses and limits: at the top of this file. -/
theorem ended_of_accept (p : P12) (he : p.early = true) (ha : p.answers = 1) (t₀ t' : T12)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t₀ rs gs = .ok t')
    (hB : endedB p (thinSh t₀) = true) : testEnded t' = true := by
  unfold endedB at hB
  rw [k12_thin p he ha t₀ t' rs gs h] at hB
  rw [testEnded_thin]
  exact hB

/-- **Under the same hypotheses `leaveRanges` returns at the state after the test.** Nothing is said
of what it returns. -/
theorem leaves_ranges (p : P12) (he : p.early = true) (ha : p.answers = 1) (t₀ t' : T12)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t₀ rs gs = .ok t')
    (hB : endedB p (thinSh t₀) = true) (s : FirstState) : ∃ s', leaveRanges s t' = .ok s' := by
  unfold leaveRanges
  rw [if_pos (ended_of_accept p he ha t₀ t' rs gs h hB)]
  exact ⟨_, rfl⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.testEnded_thin
#print axioms ProofFile.Honest.K12.ended_of_accept
#print axioms ProofFile.Honest.K12.leaves_ranges
#print axioms ProofFile.Honest.K12.endedThin
#print axioms ProofFile.Honest.K12.endedB
