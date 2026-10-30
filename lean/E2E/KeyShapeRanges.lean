--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeRanges.lean: THE RANGES' PROXIMITY TEST, THE KEY FILE's FIRST CHAIN's SUB-PROTOCOL
"rng", ON SHAPES: ONE DIRECTION: (B1) of Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's cut.
Where the sub-protocol accepts, the test on the core's shape (`testCore`,
Johnson/Desc/K12/Honest/Shape/TestCore.lean) returns the core's shape behind; of the chain's other
named values one turns: no count of rows waits any more. Statements and proofs. A step of the
verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `k12_any`: the test's decision is the same function at every type of claims: the library's
    `alike_k12`.
  `ranges_inv`: the seated test's accept, read back: the test accepts at the state that is made of
    the chain's (`rangesState`, E2E/KeyRangesSeat.lean), and the chain's state behind is written
    out.
  **`ranges_core`**: (B1) on the core's shape, at a place whose masks are sent ahead and whose
    samples have one answer.
  `ranges_tidy`, `ranges_codes`: the mark on the statement is kept (the library's `k12_tidy`); so
    are the codes (`k12_grows`).
  `ranges_place`: the two conditions on the place are parts of the sub-protocol's own test on public
    values.

Limits.
- (B2) IS NOT HERE: `testCore` asks fewer guards than the test; the nine clauses that the seat asks
  in front (E2E/KeyRangesSeat.lean: `Enters`, `Asked`) and "the test has run to its end" are not
  written on the shape here.
- The laws are stated at the chain's state and the core's shape: the whole chain's shape is another
  file's.


-/
import E2E.KeyRangesSeat
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.K12.Law.GrowsTest
import Johnson.Desc.K12.Coin.TidyThrough
import Johnson.Desc.K12.Law.SitsKeyChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest.Sh (testCore k12_core_sh)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges rangesTest rangesParams
  rangesRecord asksOnRecord enterAndAsk testEnded)

/-- The test's decision is the same function at every type of claims. -/
theorem k12_any {Cl : Type} (p : P12) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Cl).decide = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide :=
  (H2K.JointK.alike_k12 Cl Unit guardedProximityTestParts p).2.1

/-- The seated test's accept, read back. -/
theorem ranges_inv {Cl : Type} (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl).decide s rs gs =
      .ok s') :
    ∃ tE : T12, (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (rangesState s) rs gs =
        .ok tE ∧
      s' = { s with d := { s.d with st := tE.st, book := tE.book, roots := tE.roots }
                    owed := none } := by
  have h' : (enterAndAsk (enterRanges one) (rangesParams N) s).bind (fun t =>
      ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl).decide t rs gs).bind (leaveRanges s)) =
      .ok s' := h
  cases he : enterAndAsk (enterRanges one) (rangesParams N) s with
  | error e =>
    rw [he] at h'
    cases h'
  | ok t =>
    rw [he] at h'
    have ht : t = rangesState s := by
      unfold enterAndAsk rangesRecord at he
      cases hl : enterRanges one s with
      | error e =>
        rw [hl] at he
        cases he
      | ok l =>
        rw [hl] at he
        have hl' : l = ⟨s.d, s.grp, s.rider⟩ := by
          unfold enterRanges at hl
          obtain ⟨_, _, hl⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hl
          obtain ⟨_, _, hl⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hl
          obtain ⟨_, _, hl⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hl
          exact (Except.ok.inj hl).symm
        subst hl'
        have he' : (asksOnRecord (rangesParams N) (rangesState s)).map
            (fun _ => rangesState s) = .ok t := he
        cases ha : asksOnRecord (rangesParams N) (rangesState s) with
        | error e =>
          rw [ha] at he'
          cases he'
        | ok u =>
          rw [ha] at he'
          exact (Except.ok.inj he').symm
    subst ht
    have h'' : ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (rangesState s) rs
        gs).bind (leaveRanges s) = .ok s' := by
      rw [← k12_any (Cl := Cl)]
      exact h'
    cases hk : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (rangesState s) rs gs with
    | error e =>
      rw [hk] at h''
      cases h''
    | ok tE =>
      rw [hk] at h''
      refine ⟨tE, rfl, ?_⟩
      have h3 : leaveRanges s tE = .ok s' := h''
      unfold leaveRanges at h3
      split at h3
      · exact (Except.ok.inj h3).symm
      · cases h3

/-- **(B1) on the core's shape.** -/
theorem ranges_core {Cl : Type} (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl).decide s rs gs =
      .ok s') (he : (rangesParams N).early = true) (ha : (rangesParams N).answers = 1) :
    testCore (rangesParams N) (coreSh ⟨s.d.st, s.d.book, s.d.roots⟩) s.grp s.rider =
        some (coreSh ⟨s'.d.st, s'.d.book, s'.d.roots⟩) ∧
      ∃ d, s' = { s with d := d, owed := none } := by
  obtain ⟨tE, hk, rfl⟩ := ranges_inv one N s s' rs gs h
  have c : testCore (rangesParams N) (coreSh ⟨s.d.st, s.d.book, s.d.roots⟩) s.grp s.rider =
      some (coreSh ⟨tE.st, tE.book, tE.roots⟩) :=
    k12_core_sh (rangesParams N) he ha (rangesState s) tE rs gs hk
  exact ⟨c, { s.d with st := tE.st, book := tE.book, roots := tE.roots }, rfl⟩

/-- The mark on the statement is kept. -/
theorem ranges_tidy {Cl : Type} (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl).decide s rs gs =
      .ok s') (hl : s.d.st.codes.lengthsOk = true) (hT : stTidyB s.d.st = true) :
    stTidyB s'.d.st = true := by
  obtain ⟨tE, hk, rfl⟩ := ranges_inv one N s s' rs gs h
  exact tidy_mark (VerifiableInference.Desc.K12.Coin.k12_tidy _ _ tE rs gs hk hl (tidy_of hT))

/-- So are the codes. -/
theorem ranges_codes {Cl : Type} (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl).decide s rs gs =
      .ok s') : s'.d.st.codes = s.d.st.codes := by
  obtain ⟨tE, hk, rfl⟩ := ranges_inv one N s s' rs gs h
  exact (H2K.Out.k12_grows _ _ tE rs gs hk).1

/-- The two conditions on the place are parts of the sub-protocol's own test on public values. -/
theorem ranges_place {Cl : Type} (one : OneTime) (N : H2U.PlaceNums)
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Cl).planOk = true) :
    (rangesParams N).early = true ∧ (rangesParams N).answers = 1 := by
  have h' : ((Block.inside (enterAndAsk (enterRanges one) (rangesParams N))
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl) leaveRanges).planOk &&
      VerifiableInference.Desc.Key.asksOnPlan (rangesParams N)) = true := h
  rw [Bool.and_eq_true] at h'
  have h2 := h'.2
  unfold VerifiableInference.Desc.Key.asksOnPlan at h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1.1.1, h2.1.1.2⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.k12_any
#print axioms AtPublicFiles.AtFiles.ranges_inv
#print axioms AtPublicFiles.AtFiles.ranges_core
#print axioms AtPublicFiles.AtFiles.ranges_tidy
#print axioms AtPublicFiles.AtFiles.ranges_codes
#print axioms AtPublicFiles.AtFiles.ranges_place
