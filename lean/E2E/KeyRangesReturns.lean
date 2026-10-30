--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesReturns.lean: THE PROXIMITY TEST ON THE RANGES, IN THE KEY FILE's FIRST CHAIN: "THE
GUARD RETURNS, THE STEP's OWN TESTS PASS, THE NAMED TESTS ON VALUES PASS: THEN THE SUB-PROTOCOL's
DECISION RETURNS" (`ReturnsV`, E2E/KeyShapeFirstReturns.lean), at the sub-protocol "rng" as the
chain's blocksInOrder list has it (`rngEntry`, Johnson/Desc/K12/Law/SitsKeyChains.lean), at the first
chain's own guard on the shape and a named test on values that is written here. Steps of the
verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `enters_of_B`   the guard's first test (`entersB`, E2E/KeyShapeFirstBack.lean) gives, at a
      state's shape, the three clauses that the seat asks of the chain's state (`Enters`,
      E2E/KeyRangesSeat.lean).
  `gRng`   the guard: written in E2E/KeyShapeFirstBack.lean: `entersB`; `guardK12`
      (Johnson/Desc/K12/Honest/Shape/TestSeatAsks.lean) at the shape's core, group and mask; the
      first mark and the codes' message lengths; the test on the core's shape.
  `vRng`   the named test on values, at the test's structure as the seat makes it: the front's
      named test on the open rows (`claimsB`); no row of the statement has a written-out factor
      (`stPlainB`); `valsK12` (Johnson/Desc/K12/Honest/Shape/TestValsB.lean).
  ★★ `returns_rng`   `ReturnsV` at the two.

WHAT `vRng` IS, SAID PLAINLY. `valsK12` RUNS THE TEST's OWN PARTS TO MAKE THE CLAIM; its only test
is the base case's own decision; under the guard and the step's own tests it is equivalent to the
sub-protocol's yes. `claimsB` is a test on the open rows' coefficients. `stPlainB` reads no field
element: it stands here because the shape does not hold it.

By what. Calls: `seat_returns`, `runRows_plain`; `enterRanges_passes`, `leaveRanges_passes`
(E2E/KeyRangesSeat.lean); `alike_k12` (SitsKeyChains.lean). Three steps of the proof have their
like, by name, in the library's Johnson/RunOne/Law/RngOver.lean, at `rangesTest`: `rounds_over`,
`decide_over`, `form_over`.

Limits. All limits of TestSeatAsks.lean stand: one tree at the first stage; the mask has come; no
written-out factor. That the guard returns at any shape, and that `vRng` passes at any run, is
shown nowhere here. Of the guard's tests `guardK12` is evaluated, and true, at the closed place of
the full size, which is `rangesParams nKRFull` (`params_KR`,
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean), and the written shape: `guard_KR`
(Johnson/Desc/K12/Honest/Shape/TestSeatAsksAtKeyRanges.lean). Nothing on completeness, on soundness
or on what a view shows.


-/
import E2E.KeyShapeFirstReturns
import E2E.KeyRangesSeat
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks
import Johnson.Desc.K12.Law.SitsKeyChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block roundsFit noDigest OpenedColumn)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges rangesTest rangesParams
  rangesRecord asksOnRecord enterAndAsk testEnded lookupsOf)
open AtPublicFiles.KeyShape (Pub1)
open ProofFile.Honest.Sh (guardK12 seat_returns valsK12 claimsB runRows_plain)

variable (Q : Pub1) (cs : Codes)

/-- What the guard's first test gives at a state's shape. -/
theorem enters_of_B {s : FirstState} (h : entersB Q (sh₁B Q cs s) = true) : Enters Q.one s := by
  unfold entersB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' : (keysSlots s.base.keys).length = (lookupsOf Q.one).length := eq_of_beq h2
  have h3' : has (stSh s.d.st).groups[s.grp]? (fun G =>
      !G.inRun && G.kinds.length == (s.base.rows.map (·.length)).sum) = true := h3
  rw [grp_get] at h3'
  refine ⟨h1, ?_, ?_⟩
  · unfold keysSlots at h2'
    rwa [List.length_map] at h2'
  · cases hG : s.d.st.groups[s.grp]? with
    | none =>
      rw [hG] at h3'
      cases h3'
    | some G =>
      rw [hG] at h3'
      simp only [has, Option.map_some, Option.getD_some, Bool.and_eq_true, Bool.not_eq_true',
        beq_iff_eq] at h3'
      refine ⟨G, rfl, h3'.1, ?_⟩
      have k : (G.rows.toList.map (·.kind)).length = (s.base.rows.map (·.length)).sum := h3'.2
      rw [List.length_map, Array.length_toList] at k
      rw [k, List.length_flatten]

/-- **The named test on values.** -/
def vRng (N : H2U.PlaceNums) : Val FirstState := fun s rs gs =>
  claimsB (rangesState s) && stPlainB s.d.st &&
    valsK12 (rangesParams N) (rangesState s) rs gs

/-- ★★ **THE GUARD RETURNS, THE STEP's OWN TESTS PASS, THE NAMED TEST ON VALUES PASSES: THEN "rng"
RETURNS.** -/
theorem returns_rng (N : H2U.PlaceNums) (ft : Nat) :
    ReturnsV ft (sh₁B Q cs) (H2K.JointK.rngEntry Q.one N) (gRng Q N, vRng N) := by
  intro s rs cols t hg hF hv
  obtain ⟨er, ed, -⟩ := H2K.JointK.alike_k12 Claim Unit guardedProximityTestParts (rangesParams N)
  have hg' : gRng Q N (sh₁B Q cs s) = .ok t := hg
  unfold gRng at hg'
  split at hg'
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    split at hg'
    · rename_i hm2
      rw [Bool.and_eq_true] at hm2
      have hT : stTidyB s.d.st = true := hm2.1
      have hv' : (claimsB (rangesState s) && stPlainB s.d.st &&
          valsK12 (rangesParams N) (rangesState s) (rs.map noDigest)
            ((H2K.JointK.rngEntry Q.one N).shown ft rs cols)) = true := hv
      simp only [Bool.and_eq_true] at hv'
      obtain ⟨⟨v1, v2⟩, v4⟩ := hv'
      have eR : (H2K.JointK.rngEntry Q.one N).rounds =
          (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).rounds := er
      have eS : (H2K.JointK.rngEntry Q.one N).shown ft rs cols =
          (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).shown ft rs cols := by
        unfold Block.shown Block.want
        rw [eR]
      have hF' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).Fits ft rs cols := by
        unfold Block.Fits Block.want at hF ⊢
        rw [eR] at hF
        exact hF
      rw [eS] at v4 ⊢
      obtain ⟨ha, t', hd, he⟩ := seat_returns (p := rangesParams N) (t := rangesState s) rfl hm.2
        hT (fun G hG => runRows_plain v2 hG) v1 ft rs cols hF' v4
      refine ⟨{ s with d := { s.d with st := t'.st, book := t'.book, roots := t'.roots }
                       owed := none }, ?_⟩
      show (enterAndAsk (enterRanges Q.one) (rangesParams N) s).bind (fun t =>
        ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Claim).decide t (rs.map noDigest) _).bind
          (leaveRanges s)) = _
      have e : enterAndAsk (enterRanges Q.one) (rangesParams N) s = .ok (rangesState s) := by
        unfold enterAndAsk rangesRecord
        rw [enterRanges_passes Q.one s (enters_of_B Q cs hm.1)]
        show (asksOnRecord (rangesParams N) (rangesState s)).map (fun _ => rangesState s) = _
        rw [ha]
        rfl
      rw [e, ed]
      show ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (rangesState s) _ _).bind
        (leaveRanges s) = _
      rw [hd]
      exact leaveRanges_passes s t' he
    · cases hg'
  · cases hg'

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.enters_of_B
#print axioms AtPublicFiles.AtFiles.returns_rng
