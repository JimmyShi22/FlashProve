-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/BodyInvFirstDense.lean: the "dense" twin of `bodyInv_behind_first`
(BodyInvFirst.lean in this folder).

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

Main names. `bodyInv_behind_first_dense`.

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
import Johnson.Desc.ProofFile.Honest.K12.BodyInvFirst
import Johnson.Desc.K12.Honest.Shape.FirstTermDense
import Johnson.Desc.K12.Honest.Shape.SwitchInShapeDense
import Johnson.Desc.ProofFile.Honest.K12.WholeShapeDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open ProofFile.Honest.Sh (switchIn_shape_dense first_of_shape_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape switchIn_shape SwitchPub claimsB testSh)
variable {W X : Type}

/-- The twin of `bodyInv_behind_first` (BodyInvFirst.lean), with `DenseRow` in the place of
`PlainRow`. -/
theorem bodyInv_behind_first_dense (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ)))
    (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = some id) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, DenseRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty
      ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1
      (J.recB w fr (D 0)) (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Sp : FirstSwitchPlan J.p (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll J.p rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    Wanted J w fr C D a next rest Dp c := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨-, -, -, -, Y⟩ := first_of_shape_dense J.p (coinsOf J.p.nums.stages C.hide C.rest)
    rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl
    hv Pl hB hF fB (by rw [← eR]; exact A)
  obtain ⟨rows, In, hst1⟩ := switchIn_shape_dense J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a
    next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
    (noDigest ⟨[.answer (ofE (aAns J.p 0 a next 1 D (t1At J.p
      (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1
      (J.first w fr C) D)))], D (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩) rfl
  rw [← eR] at Y In hst1
  have hI := bodyInv_first_all J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
    (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D n _
    rows Y Sp In hPlan hFit
  obtain ⟨_, -, hG⟩ := test_accepts_shape_dense J w fr C D a next rest ds os hst hrd hor Dp c i n id
      dS dC
    h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (fun rest' j cur l o t P col =>
      BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D rest' j cur l o t P col ∧
        Wanted J w fr C D a next rest Dp c)
    (fun _ => Wanted J w fr C D a next rest Dp c)
    (fun next' rest' j cur l o t P col x =>
      ⟨(hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P col
          x.1).1,
        (hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P col
          x.1).2, x.2⟩)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t P col x.1
      exact ⟨t', e, x.2⟩)
    (fun hc => ⟨hI hc, hI hc⟩)
  exact hG

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bodyInv_behind_first_dense
