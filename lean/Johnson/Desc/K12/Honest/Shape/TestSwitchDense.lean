-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestSwitchDense.lean: the "dense" twin of `first_stage_of_shape`
(TestSwitch.lean in this folder).

What it is. The old statements take as a hypothesis that every row taken in is a `PlainRow`. The
twins take `DenseRow` in its place. `PlainRow` (OnBytes/Slice/BlkPlain.lean) says that no tensor of
a row has a written-out variable. `DenseRow` (OnBytes/Slice/BlkProxDense.lean) allows such variables
where every tensor is in order and its slice lies inside its vector; it follows from `PlainRow`
(`denseRow_of_plain`). The rows meant are those that the proximity test takes in at the group under
test (`runRows`, OnBytes/Slice/BlkBegin.lean). Apart from that and from the twins' names, each
statement is the old one, letter for letter.

Why. The only place where the old chain spends its hypothesis is the field `dense` of the library's
`TestFront`, which `testFront_of` fills from `PlainRow` by `denseRow_of_plain`. So the weaker
hypothesis is enough. That a row taken in at the first chain's proximity test has written-out
variables is read off the description's text; no theorem in these files says so.

Main names. `first_stage_of_shape_dense`.

By what. Each proof is the old proof with the twins' names in it.

Limits.
- These statements stand over Johnson/Prover/Link/FormFirst.lean, whose structure
  `TestFront` has the field `dense`. With a field `plain`, `testFront_of_dense`
   (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
  rest, could not be proved.
- They do not reach the first chain's proximity test yet. The library proves the new hypothesis
  there, of the verifier's state (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean).
  These files do not show that the other hypotheses hold there: the other fields of `ShapeAsksD`
  (Johnson/Desc/ProofFile/Honest/K12/PlanBDense.lean), `planB`, and the hypotheses on the prover's
  data.
- `ShapeAsksD` is made from the old `ShapeAsks` (`shapeAsksD_of`), and so from the old mark
  `stPlainB`; and from `FrontAsksD`, the hypotheses on the front with the same new field, by
  `shapeAsksD_of_front` (ShapeAllDense.lean) and `shapeAsksD_of_two`, `shapeAsksD_of_form`,
  `shapeAsksD_of_draws` (ShapeOfTwoDense.lean); `FrontAsksD` is made by `frontAsksD_of_five`
  (FrontAtShapeDense.lean). These files lie in Johnson/Desc/ProofFile/Honest/K12/. Without a twin:
  `sorts_of_coreB` (SortsMember.lean) and `frontAsks_of_shape` (OneToAll.lean, not in the library
  yet).
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Only the case in which the fresh table has come earlier is served, as in the old statements.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.K12.Honest.Shape.TestSwitch
import Johnson.Desc.K12.Honest.Shape.TestDoorDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.Sh
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.JointK (foldedFit_pure)
open ProofFile.Honest.K12 (TestFrontOwn foldTOwn enteredT withOwn ownBook foldFrontOwn_first
  front_entered)
open ProofFile.Honest.K12 (foldCutOwn foldCutOwn_of door_yes_own)

/-- The twin of `first_stage_of_shape` (TestSwitch.lean), with `DenseRow` in the place of
`PlainRow`. -/
theorem first_stage_of_shape_dense {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i : ℕ × ℕ}
    {n : IoppStage} {id : ℕ} {cutB cutF : List Fmt.DeclaredRound} {last : Bool}
    {dS dC : Fmt.DeclaredRound} (h : doorB p cur nxt cutB i (n.code, n.maskCode) (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r)
    (hv : claimsB t = true)
    (Pl : SwitchPub p t.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC)
    (hB : batCut cutB = true) (hF : foldCut cur.k cutF = true) (rsB rsF : List Fmt.RoundView)
    (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row →
      ReadsAny p cur last n dS dC
      (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) id (rsF.map noDigest))
      (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
        (rsF.map noDigest))
      (batT t G row).st.groups.size rC gs bk) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest)) ∧
      SwitchDone p 0 cur nxt last n dS dC
        (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest))
        (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
          (rsF.map noDigest))
        (batT t G row).st.groups.size rS rC a gs bk := by
  have h' := h
  unfold doorB at h'
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of_dense h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  have Fo := frontOwes_of h3 hv H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H cutB B hB rsB fB
  obtain ⟨rE, rR, hrs, hR⟩ := rounds_split (length_of_foldCut hF) fF
  have hrd := hread G row H.group hr
  refine ⟨G, row, H.group, hr, front5_yes B.pass H.group Fo, hb, group_batT H row,
    fold5_yes (foldFront_first H _ row hr) hF rsF fF, ?_⟩
  rw [hrs] at hrd ⊢
  exact first_switch_came H (VerifiableInference.Desc.K12.Seat.front_in_step Fo.front) hr Pl rE rR
    hR rS rC hfit a hans gs bk hrd

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.first_stage_of_shape_dense
