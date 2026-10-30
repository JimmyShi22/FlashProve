-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/EndOkOwn.lean: for a proximity test whose first fold sends its
own fresh table: from the four sorts of hypotheses (on the plan, on shapes, on forms, on data) to
"the last claim is true" at the place itself. One structure; two theorems.

What it is. BodyInvFirstOwn.lean in this folder ends in the library's invariant of the later stages
at the renumbered place `renumP p` (Renumber.lean). RenumberEnd.lean has the bridge back: from that
invariant at `renumP p` to `EndOkT p` (Johnson/Desc/ProofFile/Honest/K12/Sim/TreesLaw.lean), the
premise of the law `core_own_trees` there. Between the two stand the fellows of `wanted_of_plan`
(Sim/PlanLaw.lean) and of `behind_of_plan_trees` (Sim/TreesPlan.lean). The second is stated here
already across the bridge.

Main names.
  `ShapeAsksO`: `ShapeAsks` (PlanB.lean in the folder above) with one field turned: `came` (a
  message is named as the mask on entry) gives way to `noMask` (none is). The eight other fields are
  the same to the sign. A twin of nine fields for one field's
  sake: `came` and `noMask` bar each other, so `ShapeAsks` cannot serve; a later turn of `ShapeAsks`
  wants the same turn here.
  `wanted_of_plan_own`: `WantedOwn` (BodyInvFirstOwn.lean) from the test `planOB` (PlanOwn.lean),
  `ShapeAsksO`, `FormAsks` and `DataAsks`, where the place's flag `ownMask` is true.
  `endOk_of_plan_own`: from the same hypotheses, `EndOkT J.p …` at the letters of
  `behind_of_plan_trees`.

By what. The proofs are those of `wanted_of_plan` and `behind_of_plan_trees`, with
`bodyInv_behind_first_own`, `switchPlan_renum`, and `planFrom_of_ok` at `renumP J.p`; then
`endOk_of_behind_renum`. What is shown of `EndOkT` is its second disjunct.

Over what it stands. Through BodyInvFirstOwn.lean: the library's structures in their later form,
with the clause `dense`: see Johnson/Desc/K12/Honest/Shape/SwitchInShapeOwn.lean, "Over what it
stands".

Limits.
- `endOk_of_plan_own` is a bridge, no top: it speaks of the last claim alone. It is no sentence at a
  member. The renumbered place stands in one public hypothesis (the clause "planFromOk at the
  renumbered place" of `planOB`) and not in the conclusion. `wanted_of_plan_own` is a helper: its
  conclusion speaks of the renumbered place, a term of comparison. At `renumP p` the first fold's
  own mask tree is left out of the lists. So nothing that is drawn there may be quoted of stage 0,
  of all the test's trees, or of any count or budget over them. No file's plan that we know of has
  these numbers.
- Conditionals; no member is shown. `planOB` says yes at three written places (PlanOwn.lean, by an
  evaluation in Lean's kernel). These files do not show that `ShapeAsksO`, `FormAsks` and `DataAsks`
  can be met together.
- `stPlainB` is asked (the field `plainRows`), as in `ShapeAsks`. There is no "dense" twin.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.BodyInvFirstOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.PlanOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.RenumberEnd
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlanLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB)

variable {W X : Type}

section Asks
variable (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)

/-- The hypotheses on the state on entry, on the state after the batching and on the state after the
first fold, where the first fold sends its own fresh table: `ShapeAsks` (PlanB.lean) with `came`
turned to `noMask`. The state on entry is the job's, not shown to be the verifier's. -/
structure ShapeAsksO (K : Codes) (Dp : Plain) : Prop where
  codes : (J.rec₀ w fr).st.codes = K
  door : Sh.doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
    (lettersOf J.p (stA J.p) (stN J.p)).i
    ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
    (testSh (J.rec₀ w fr)) = true
  noMask : (J.rec₀ w fr).mask = none
  tidy : stTidyB (J.rec₀ w fr).st = true
  plainRows : stPlainB (J.rec₀ w fr).st = true
  claims : claimsB (J.rec₀ w fr) = true
  plain : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
    gpOf J.p (J.recB w fr (D 0)) (stA J.p) L = some Dp ∧ ok (gpL J.p (stA J.p) row Dp) = true ∧
      L.k = (sgOf (stA J.p)).h + (sgOf (stA J.p)).g ∧ L.h = (sgOf (stA J.p)).h ∧
      2 ^ L.logEll = (stA J.p).C.l ∧ 2 ^ L.logEllZk = (stA J.p).Z.l
  codes₁ : (tFold J w fr C D).st.codes = K
  pub : ∀ rows gp, (tFold J w fr C D).pass = .single rows gp →
    readPubB (coreSh ⟨(tFold J w fr C D).st, (tFold J w fr C D).book, (tFold J w fr C D).roots⟩)
      (singleSh rows) (stA J.p).C.a = true ∧
    OldOk (sgOf (stA J.p)) (sgOf (stN J.p)) (tFold J w fr C D).st.codes rows
      (lettersOf J.p (stA J.p) (stN J.p)).n.code (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode

end Asks

/-- `WantedOwn` from the four sorts of hypotheses and `ho` (the place's flag), at every family c of
the switches' random values. A helper: it concludes at the renumbered place. -/
theorem wanted_of_plan_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (ho : J.p.nums.ownMask = true) (hP : planOB J.p K Dp.ts.length = true)
    (S : ShapeAsksO J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R) (c : ℕ → GE) :
    ∃ a next nx' rest', J.p.nums.stages = a :: next :: nx' :: rest' ∧
      WantedOwn J w fr { C with rest := c } D a next (nx' :: rest') Dp cc := by
  unfold planOB planOL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    have hR : J.p.nums.stages.drop 2 = nx' :: rest' := by
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19,
      p20, p21, p22⟩ := hP
    obtain ⟨ds, hrd⟩ := Option.isSome_iff_exists.1 p1
    obtain ⟨os, hor⟩ := Option.isSome_iff_exists.1 p2
    have hm := S.noMask
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9, s10⟩ := S
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := F
    obtain ⟨d1, d2, d3, d4⟩ := Dt
    simp only [tFold, hA, hN, hR] at s2 s7 s9 s10 f2 f3 f4 f5 f6 f7 d1 d2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    have A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) (nx' :: rest') a next 1
        (J.recB w fr (D 0)) (J.first w fr C) D Dp cc
        ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
        (lettersOf J.p a next).dS (lettersOf J.p a next).dC :=
      ⟨fun row L h => ⟨(s7 row L h).1, (s7 row L h).2.1⟩, p6, p7, d1.width, f5, two_of_length _ p8,
        f2, f3, fun rows gp h => (s10 rows gp h).1, p9, p10, p11, p12⟩
    have V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
        RestAsks J w fr C D a next (nx' :: rest') Dp cc R row L
          ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          (lettersOf J.p a next).n := fun row L h =>
      ⟨p15, sized_of p16, d1, d2, d3, f6, fitAll_of _ _ p17, (s7 row L h).2.2.1,
        (s7 row L h).2.2.2.1, (s7 row L h).2.2.2.2.1, (s7 row L h).2.2.2.2.2,
        by rw [front_getD]; exact d4 row L h, p18,
        by
          show ((t1At J.p _ 0 a (laidS J.p) 1 _ _ D).st.codes.mask.getD _ default).ell = a.Z.l
          rw [s9]
          exact p19,
        fun rows gp h' => (s10 rows gp h').2, f7⟩
    have s9' : (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes = K :=
      (congrArg (fun x => (aRec1 J.p 0 a (laidS J.p) (J.recB w fr (D 0)) x).st.codes)
        (fold_rest J.p.nums.stages C.hide c C.rest a 1 (J.first w fr C) _ D)).trans s9
    refine ⟨a, next, nx', rest', hst, ?_⟩
    refine bodyInv_behind_first_own J w fr { C with rest := c } D a next (nx' :: rest') ds os hst ho
      hrd hor Dp cc (lettersOf J.p a next).i (lettersOf J.p a next).n (lettersOf J.p a next).dS
      (lettersOf J.p a next).dC s2 hm s4 (fun G hG => runRows_plain s5 hG) s6 Pl p4 p5 f1
      (termAsks_rest A c) p13 p14 R (fun row L h => restAsks_rest (V row L h) c) ?_ ⟨?_, p22⟩ f4
    · show SwitchPlan (renumP J.p) (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1
        (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next _
      rw [s9']
      exact switchPlan_renum (switchPlan_of_B p20)
    · show PlanFrom (renumP J.p) (nx' :: rest') (0 + 1) next ((laidS J.p).drop (a.k + 3))
        (t1At J.p (coinsOf J.p.nums.stages C.hide c) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
          (J.first w fr C) D).st.codes
      rw [s9']
      exact planFrom_of_ok (renumP J.p) _ _ _ _ _ p21
  · simp at hP

/-- **The last claim is true, at the place itself, from the four sorts of hypotheses** and `ho` (the
place's flag), at the job's own trees, at every family of the switches' random values. A bridge, no
top. -/
theorem endOk_of_plan_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows)
    (ho : J.p.nums.ownMask = true) (hP : planOB J.p K Dp.ts.length = true)
    (S : ShapeAsksO J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp cc R)
    (a next nx' : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: nx' :: rest') (c : ℕ → GE) :
    EndOkT J.p a next (nx' :: rest') (laidS J.p) (J.recB w fr (D 0)) (J.first w fr C) C.hide
      (J.trees₀ w fr C.mem (J.first w fr C)) D c := by
  have hf : FitAll next (nx' :: rest') := by
    have h := hP
    unfold planOB planOL at h
    split at h
    · rename_i a₁ n₁ x₁ r₁ hst₁
      have e := hst₁.symm.trans hst
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p17, -, -, -, -, -⟩ := h
      exact fitAll_of _ _ p17
    · simp at h
  obtain ⟨a', n', x', r', hst', hW⟩ := wanted_of_plan_own J w fr C D K Dp cc R ho hP S F Dt c
  rw [hst] at hst'
  injection hst' with e1 e2
  injection e2 with e2 e3
  injection e3 with e3 e4
  subst e1 e2 e3 e4
  refine endOk_of_behind_renum J.p a next (nx' :: rest') _ _ _ _ _ D hf c ?_
  unfold WantedOwn at hW
  unfold BehindFirstT
  rw [← hst, Dt.trees]
  exact hW

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.ShapeAsksO
#print axioms ProofFile.Honest.K12.Own.wanted_of_plan_own
#print axioms ProofFile.Honest.K12.Own.endOk_of_plan_own
