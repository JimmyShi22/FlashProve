-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/WholeShapeDense.lean: the "dense" twin of `test_accepts_shape`
(WholeShape.lean in this folder).

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

Main names. `test_accepts_shape_dense`.

By what. Each proof is the old proof with the twins' names in it.

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
import Johnson.Desc.ProofFile.Honest.K12.WholeShape
import Johnson.Desc.K12.Honest.Shape.FirstTermDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open ProofFile.Honest.Sh (first_of_shape_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape first_of_shape_own SwitchPub claimsB testSh)
variable {W X : Type}

/-- The twin of `test_accepts_shape` (WholeShape.lean), with `DenseRow` in the place of `PlainRow`.
-/
theorem test_accepts_shape_dense (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ))) (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = some id) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.recB w fr (D 0))
      (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next l o t P col
            (Johnson.Prover.Link.rowOf t) D)
          (sNext (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D)
          (sCol (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base J.p j cur (l.map (·.1))).decide t
        ((lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).rs.map noDigest)
        (lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).gs = .ok t' ∧ Post t')
    (hI : ClaimTrue (sgOf next)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D) →
      Inv rest 1 next ((J.laid.drop 1).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
        (aCol rest.isEmpty next
          (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧ Post t' := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨d1, d2, d3, ⟨row, L, hp⟩, Y⟩ := first_of_shape_dense J.p
    (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp
    c i n id dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
  rw [← eR] at d2 d3 hp Y
  exact accepts_of_first J w fr C D a next rest ds os hst hrd hor Dp c _ n dS dC d1 d2 d3 Y Pl.early
    Pl.one Pl.stageN Pl.fits A nB oB row L hp R (V row L hp) Inv Post hstep hbase hI

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.test_accepts_shape_dense
