-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean: the "dense" twins of `testFront_of`,
`door_of_shape` (TestDoor.lean in this folder).

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

Main names. `testFront_of_dense`, `testFront_of_plain'`, `door_of_shape_dense`.

By what. Each proof is the old proof with the twins' names in it. One line differs beyond that: the
hypothesis fills the field `dense` as it stands. `testFront_of_plain'` is new: the twin at
`denseRow_of_plain`.

Limits.
- These statements rest on this: in Johnson/Prover/Link/FormFirst.lean the structure
  `TestFront` has the field `dense`. With a field `plain` in its place,
  `testFront_of_dense` (Johnson/Desc/K12/Honest/Shape/TestDoorDense.lean), on which all the twins
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
import Johnson.Desc.K12.Honest.Shape.TestDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.Sh
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Ground (Clauses on has)
open H2K.First (Seat1 seatOf entered opensOf gpOf gpL gpAll gpOk labelsL labelsOk memL apartB oM oZ
  codeB keyAt logAt widthAt numAt)
open Johnson.Prover.Link (TestFront BatOwes FrontOwes batT layoutOf_own)
open ProofFile.Honest.K12 (TestFrontOwn)

/-- The twin of `testFront_of` (TestDoor.lean): the library's `TestFront` from the tests on the
shape, from the first mark and from `DenseRow` of every row taken in. The last hypothesis is the
field `dense` of `TestFront` as it stands. -/
theorem testFront_of_dense {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat} {id : Nat}
    (h : commonB p cur nxt (testSh t).core t.g i n = true) (hm : t.mask = some id)
    (hc : cameB cur (testSh t).core t.g i id = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r) :
    ∃ G, TestFront p cur nxt t G i n id := by
  obtain ⟨G, C⟩ := common_of h
  unfold cameB at hc
  have e : (testSh t).core.st = stSh t.st := rfl
  rw [e, grp_get, orc_get, C.group] at hc
  cases ho : t.st.oracles[id]? with
  | none =>
    rw [ho] at hc
    cases hc
  | some o =>
    rw [ho] at hc
    simp only [has, Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hc
    have b7' : id ∉ G.members := by
      intro hmem
      have : G.members.toList.contains id = true := by
        rw [Array.contains_toList]
        exact Array.contains_iff_mem.2 hmem
      rw [show (grpSh G).members = G.members.toList from rfl, this] at b7
      cases b7
    exact ⟨G, C.group, (tidy_of ht).inOrder,
      hp G C.group, C.idx0, C.idx1,
      C.code, C.maskCode, C.base, C.maskC, C.base1, C.mask1, C.layK, C.layH, C.main, C.noKept, hm,
      ⟨o, ho, b1, b2, b3, b4, b5, b6, b7'⟩, C.stage, C.stage1, C.vars⟩

/-- The old statement of `testFront_of` (TestDoor.lean), letter for letter, drawn from the twin. -/
theorem testFront_of_plain' {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat}
    {id : Nat}
    (h : commonB p cur nxt (testSh t).core t.g i n = true) (hm : t.mask = some id)
    (hc : cameB cur (testSh t).core t.g i id = true)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r) :
    ∃ G, TestFront p cur nxt t G i n id :=
  testFront_of_dense h hm hc ht fun G hG r hr => denseRow_of_plain (hp G hG r hr)

open Johnson.Prover.Link (batCut foldCut foldT bat5_yes front5_yes group_batT fold5_yes
  foldFront_first drawnOf)

open ProofFile.Honest.K12 (foldCutOwn foldTOwn door_yes_own)

/-- The twin of `door_of_shape` (TestDoor.lean), with `DenseRow` in the place of `PlainRow`. -/
theorem door_of_shape_dense {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i n : Nat × Nat}
    {id : Nat}
    {cutB cutF : List Fmt.DeclaredRound} (h : doorB p cur nxt cutB i n (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r)
    (hv : claimsB t = true) (hB : batCut cutB = true) (hF : foldCut cur.k cutF = true)
    (rsB rsF : List Fmt.RoundView) (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n id
          (rsF.map noDigest)) := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFront_of_dense h1 hm h4' ht hp
  have B := batOwes_of h2 H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H cutB B hB rsB fB
  exact ⟨G, row, H.group, hr, front5_yes B.pass H.group (frontOwes_of h3 hv H.group), hb,
    group_batT H row, fold5_yes (foldFront_first H _ row hr) hF rsF fF⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.testFront_of_dense
#print axioms ProofFile.Honest.Sh.testFront_of_plain'
#print axioms ProofFile.Honest.Sh.door_of_shape_dense
