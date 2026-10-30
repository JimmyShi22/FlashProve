--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesSeat.lean: THE SEAT OF THE PROXIMITY TEST ON THE RANGES, IN THE KEY FILE's FIRST CHAIN:
WHAT IT ASKS AROUND THE TEST, CLAUSE BY CLAUSE, AND THAT THESE CLAUSES WITH THE TEST's OWN
ACCEPTANCE GIVE THE SUB-PROTOCOL's. The sub-protocol "rng" is the proximity test's own sub-protocol
with a step in front (the test's state is made of the chain's; nine tests are asked) and a step
behind (the test's state is written back; four tests are asked). These two steps have no part of a
prover. Statements and proofs, by unfolding. Steps of the verifier's: NOTHING IS SHOWN OF ANY
PROVER: no completeness, nothing on what a view shows.

The library's laws on this seat say what an acceptance GIVES (Johnson/RunOne/Law/RngAsked.lean,
RngAtKeyD.lean). Here the other direction.

What is shown.
  `Enters one s`: the three clauses of the step in front on the chain's state: no count of rows is
    owed; all lookups are laid; the ranges' group is there, its test has not begun, and it holds as
    many open rows as the lookups have laid. **`enterRanges_passes`**: under them that step returns
    the state's statement, book and roots, the group's number, and the number of the first fold's
    mask.
  `rangesState s`: the test's state that is made of them.
  `Asked p t G L a`: the six further clauses, to the letter of the library's `asksOnRecord`, with
    the group, its layout and the first stage that they read. **`asksOnRecord_passes`**.
  `testEnded_of`: the four clauses of the step behind, from their parts. **`leaveRanges_passes`**:
    under the library's `testEnded` that step returns the chain's state with the test's statement,
    book and roots, and no count of rows owed.
  **`ranges_passes`**: THE WHOLE: `Enters`, `Asked`, the proximity test's own sub-protocol's
    acceptance at `rangesState s`, and `testEnded` of the state that it leaves: the sub-protocol
    "rng" accepts, and the state behind is written out.

Limits.
- `Asked` restates the library's six tests; none of them is derived here from simpler book-keeping.
  Two read public values and the carried codes alone (the mask's number is named; the codes are the
  place's); four read the group's rows' forms, its layout, and the book's trees' numbers.
- The proximity test's own acceptance is a premise: it has parts of a prover.
- That a run's states meet the premises is not shown. Of `Asked` none is typed.


-/
import E2E.KeyListed
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block need)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (FirstState Claim RangesLaid enterRanges leaveRanges rangesTest
  rangesParams rangesRecord asksOnRecord enterAndAsk testEnded layoutIsStage behindBatching
  lookupsOf)

/-- **The three clauses of the step in front on the chain's state.** -/
structure Enters (one : OneTime) (s : FirstState) : Prop where
  waits : s.noneWaits = true
  laid : s.base.keys.length = (lookupsOf one).length
  group : ∃ G : OnBytes.Group, s.d.st.groups[s.grp]? = some G ∧ G.inRun = false ∧
    G.rows.size = s.base.rows.flatten.length

/-- **Under them the step in front returns.** -/
theorem enterRanges_passes (one : OneTime) (s : FirstState) (h : Enters one s) :
    enterRanges one s = .ok ⟨s.d, s.grp, s.rider⟩ := by
  obtain ⟨G, hG, h1, h2⟩ := h.group
  have a2 : (s.base.keys.length == (lookupsOf one).length) = true := beq_iff_eq.2 h.laid
  have a3 : ((s.d.st.groups[s.grp]?).any fun G =>
      !G.inRun && G.rows.size == s.base.rows.flatten.length) = true := by
    rw [hG]
    show (!G.inRun && G.rows.size == s.base.rows.flatten.length) = true
    rw [h1, beq_iff_eq.2 h2]
    rfl
  unfold enterRanges
  simp only [h.waits, a2, a3, need, bind, Except.bind, pure, Except.pure, if_true]

/-- The test's state that is made of the chain's. -/
def rangesState (s : FirstState) : T12 :=
  { st := s.d.st, book := s.d.book, roots := s.d.roots, g := s.grp, pass := .nothing
    mask := s.rider }

/-- **The six further clauses**, with the group, its layout and the first stage that they read. -/
structure Asked (p : P12) (t : T12) (G : OnBytes.Group) (L : GroupLayout) (a : Fmt.M1.Stage) :
    Prop where
  group : t.st.groups[t.g]? = some G
  layout : t.st.layout t.g = some L
  stage : ∃ l, p.nums.stages = a :: l
  mask : t.mask.isSome = true
  codes : H2K.Pub.pubOk p t.st.codes = true
  rows : Means.combineAt (begun t.st t.g G) t.g ⟨L, runRows t.st G⟩ = true
  four : layoutIsStage a L = true
  opened : H2K.First.gpOk p (behindBatching t G L) = true
  labels : H2K.First.labelsOk p (behindBatching t G L) = true

/-- **Under them the asking returns.** -/
theorem asksOnRecord_passes {p : P12} {t : T12} {G : OnBytes.Group} {L : GroupLayout}
    {a : Fmt.M1.Stage} (h : Asked p t G L a) : asksOnRecord p t = .ok () := by
  obtain ⟨l, hl⟩ := h.stage
  unfold asksOnRecord
  rw [h.group, h.layout, hl]
  simp only [h.mask, h.codes, h.rows, h.four, h.opened, h.labels, need, bind, Except.bind,
    if_true]

/-- The four clauses of the step behind, from their parts. -/
theorem testEnded_of (t : T12) (h1 : t.pass = .nothing) (h2 : t.g < t.st.groups.size)
    (h3 : ∀ G ∈ t.st.groups.toList.drop t.g, G.inRun = true ∧ G.rows.isEmpty = true)
    (h4 : ∀ o ∈ t.st.oracles, o.sampled = true ∨ o.spentAsMask = true) : testEnded t = true := by
  have a3 : ((t.st.groups.toList.drop t.g).all fun G => G.inRun && G.rows.isEmpty) = true :=
    List.all_eq_true.2 fun G hG => by rw [(h3 G hG).1, (h3 G hG).2]; rfl
  have a4 : (t.st.oracles.all fun o => o.sampled || o.spentAsMask) = true :=
    Array.all_eq_true_iff_forall_mem.2 fun o ho => Bool.or_eq_true_iff.2 (h4 o ho)
  unfold testEnded
  rw [h1, decide_eq_true h2, a3, a4]
  rfl

/-- **Under the library's test the step behind returns.** -/
theorem leaveRanges_passes (s : FirstState) (t : T12) (h : testEnded t = true) :
    leaveRanges s t =
      .ok { s with d := { s.d with st := t.st, book := t.book, roots := t.roots }, owed := none }
    := by
  unfold leaveRanges
  rw [if_pos h]

/-- **THE WHOLE: the sub-protocol "rng" accepts, and the state behind is written out.** -/
theorem ranges_passes (one : OneTime) (N : H2U.PlaceNums) (s : FirstState) (G : OnBytes.Group)
    (L : GroupLayout) (a : Fmt.M1.Stage) (tE : T12) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hE : Enters one s)
    (hA : Asked (rangesParams N) (rangesState s) G L a)
    (hK : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Claim).decide (rangesState s) rs gs = .ok tE)
    (hL : testEnded tE = true) :
    (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs =
      .ok { s with d := { s.d with st := tE.st, book := tE.book, roots := tE.roots }
                   owed := none } := by
  show (enterAndAsk (enterRanges one) (rangesParams N) s).bind (fun t =>
    ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Claim).decide t rs gs).bind (leaveRanges s)) = _
  have e : enterAndAsk (enterRanges one) (rangesParams N) s = .ok (rangesState s) := by
    unfold enterAndAsk rangesRecord
    rw [enterRanges_passes one s hE]
    show (asksOnRecord (rangesParams N) (rangesState s)).map (fun _ => rangesState s) = _
    rw [asksOnRecord_passes hA]
    rfl
  rw [e]
  show ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Claim).decide (rangesState s) rs gs).bind
    (leaveRanges s) = _
  rw [hK]
  exact leaveRanges_passes s tE hL

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.enterRanges_passes
#print axioms AtPublicFiles.AtFiles.asksOnRecord_passes
#print axioms AtPublicFiles.AtFiles.testEnded_of
#print axioms AtPublicFiles.AtFiles.leaveRanges_passes
#print axioms AtPublicFiles.AtFiles.ranges_passes
