-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/BodyInvFirstOwn.lean: the library's invariant of the later
stages, behind the first switch of a proximity test whose first fold sends its own fresh table: at
the renumbered place. One definition; four theorems.

What it is. `bodyInv_behind_first` (BodyInvFirst.lean in the folder above) proves `BodyInv` over
`PlanAll` behind the first stage where the fresh table has come earlier. Where the first fold sends
its own table that invariant, by its text, cannot be had at the place p itself: `PlanFrom` asks
`ownMask = false`, and the later trees' numbers are one higher than its clauses say. `renumP p`
(Renumber.lean in this folder) has the numbers at which these clauses fit from the first switch on.
Here the library's law `bodyInv_first_all` (Johnson/Prover/Link/BodyBehindAll.lean) is called at
`renumP p`, from the first stage as it is played at p.

Main names.
  `WantedOwn`: the statement: `Wanted` (BodyInvFirst.lean) with the place of `BodyInv` and of
  `PlanAll` turned to `renumP J.p`. The rounds, the states and the prover's rows are those at `J.p`.
  `bodyInv_behind_first_own`: `WantedOwn` under the hypotheses of `test_accepts_shape_own`
  (WholeShape.lean in the folder above) and four more: `ho` (the place's flag `ownMask` is true),
  `Sp` and `hPlan` (on the plan at `renumP J.p`), `hFit` (what is sampled from the second stage on
  fits the declared rounds: `FitFrom`).
  `sT3_renum`, `lastOut_renum`, `stageYes_back`: three more of Renumber.lean's kind: what a later
  stage's text reads of the place is the same at both. The first two are called by no proof here:
  Lean sees through both.

By what. `first_of_shape_own` with `firstYes_renum`; `switchIn_shape_own`
(Johnson/Desc/K12/Honest/Shape/SwitchInShapeOwn.lean) at q := `renumP J.p`; `bodyInv_first_all`,
`hstep_at`, `hbase_at` at `renumP J.p`; `base_renum`. That the claim behind the first stage is true
comes out of `test_accepts_shape_own`, which is general in its invariant, as in
`bodyInv_behind_first`.

Over what it stands. The structures in the statements of the three library laws that are called
(`SwitchIn` among them) are read in their later form, with the clause `dense`: see
SwitchInShapeOwn.lean, "Over what it stands".

Limits.
- `bodyInv_behind_first_own` is a helper: its conclusion speaks of the renumbered place, a term of
  comparison. At `renumP p` the first fold's own mask tree is left out of the lists. So nothing that
  is drawn here may be quoted of stage 0, of all the test's trees, or of any count or budget over
  them. No file's plan that we know of has these numbers.
- A conditional; no member is shown. That the two hypotheses on the plan hold at `renumP` of a
  written place is PlanOwn.lean's matter (in this folder). These files do not show that `V`
  (`RestAsks`) and `A` (`TermAsks`) can be met where the first fold sends its own table.
- Every row taken in is asked to be a `PlainRow`. There is no "dense" twin.
- The state on entry is the job's own `rec₀`. It is not shown to be the verifier's.
- Nothing here is a statement on completeness, on soundness or on what a proof hides.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.Renumber
import Johnson.Desc.ProofFile.Honest.K12.WholeAll
import Johnson.Desc.K12.Honest.Shape.SwitchInShapeOwn
import Johnson.Prover.Link.BodyBehindAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape_own switchIn_shape_own SwitchPub claimsB testSh)

variable {W X : Type}

/-! ## 1 What a later stage's text reads of the place -/

theorem sT3_renum (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    sT3 (renumP p) K last j cur next l o t P col row D =
      sT3 p K last j cur next l o t P col row D := rfl

theorem lastOut_renum (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn) :
    lastOut (renumP p) j cur o t P col row D = lastOut p j cur o t P col row D := rfl

/-- What a later stage delivers at the renumbered place it delivers at p. -/
theorem stageYes_back (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (D : ℕ → Fmt.Drawn) (Y : StageYes (renumP p) K rest j cur next l o t P col D) :
    StageYes p K rest j cur next l o t P col D :=
  ⟨Y.fold, Y.switch, Y.behind, Y.came, Y.nF, Y.oF, Y.nS, Y.oS⟩

/-! ## 2 Behind the first stage -/

/-- The statement of `bodyInv_behind_first_own`: `BodyInv` over `PlanAll`, both at the renumbered
place, before the second stage; at the values of `Wanted` (BodyInvFirst.lean), which are at
`J.p`. -/
def WantedOwn (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dp : Plain) (c : ℕ → ℕ → List UInt64) :
    Prop :=
  BodyInv (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll (renumP J.p)) D rest (0 + 1)
    next
    ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
    (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
    (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
    (aCol rest.isEmpty next
      (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))

/-- **`BodyInv` at the renumbered place holds after the first stage of a test whose first fold sends
its own fresh table**, at the values of `WantedOwn`, under the hypotheses of
`test_accepts_shape_own` (WholeShape.lean), `ho`, `Sp` and `hPlan` on the plan at the renumbered
place, and `hFit` on what is sampled from the second stage on. None of them is proved here. -/
theorem bodyInv_behind_first_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ)))
    (hst : J.p.nums.stages = a :: next :: rest) (ho : J.p.nums.ownMask = true)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = none) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, PlainRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty
      ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCutOwn a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1
      (J.recB w fr (D 0)) (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Sp : FirstSwitchPlan (renumP J.p) (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS
      J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll (renumP J.p) rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    WantedOwn J w fr C D a next rest Dp c := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨-, -, -, -, Y⟩ := first_of_shape_own J.p (coinsOf J.p.nums.stages C.hide C.rest)
    rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n dS dC h hm htidy hpl
    hv Pl hB hF fB (by rw [← eR]; exact A)
  obtain ⟨rows, In⟩ := switchIn_shape_own J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a
    next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
    (noDigest ⟨[.answer (ofE (aAns J.p 0 a next 1 D (t1At J.p
      (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1
      (J.first w fr C) D)))], D (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩) rfl (renumP J.p) rfl
  rw [← eR] at Y In
  have hI := bodyInv_first_all (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
    (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D n _
    rows (firstYes_renum _ _ _ _ _ _ _ _ _ _ _ _ Y) Sp In hPlan hFit
  -- `test_accepts_shape_own` is general in its invariant: `WantedOwn` goes in as a second clause
  obtain ⟨_, -, hG⟩ := test_accepts_shape_own J w fr C D a next rest ds os hst hrd hor Dp c i n dS
    dC h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (fun rest' j cur l o t P col =>
      BodyInv (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll (renumP J.p)) D rest' j
          cur l o t P col ∧
        WantedOwn J w fr C D a next rest Dp c)
    (fun _ => WantedOwn J w fr C D a next rest Dp c)
    (fun next' rest' j cur l o t P col x =>
      ⟨stageYes_back _ _ _ _ _ _ _ _ _ _ _ _
          (hstep_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P
            col x.1).1,
        (hstep_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P
          col x.1).2, x.2⟩)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at (renumP J.p) (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t
        P col x.1
      rw [base_renum J.p j cur _ ho a next rest hst] at e
      exact ⟨t', e, x.2⟩)
    (fun hc => ⟨hI hc, hI hc⟩)
  exact hG

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.sT3_renum
#print axioms ProofFile.Honest.K12.Own.lastOut_renum
#print axioms ProofFile.Honest.K12.Own.stageYes_back
#print axioms ProofFile.Honest.K12.Own.WantedOwn
#print axioms ProofFile.Honest.K12.Own.bodyInv_behind_first_own
