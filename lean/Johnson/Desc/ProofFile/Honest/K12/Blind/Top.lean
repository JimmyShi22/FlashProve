-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/Top.lean: a conditional on five equations (`Steps`): that
each of the five parts of the description which the prover's text of a proximity test runs
(`guardedProximityTestParts`'s front, batching, fold, switch, and the batching behind the switch:
Johnson/Desc/K12/JoinGuarded.lean), at two records that agree but for targets (`Agree`, Wipe.lean), at
one list of rounds and one list of groups of columns, refuses with one word, or returns twice and
the two records agree but for targets. The five are proved in four files of this folder (Front.lean;
Bat.lean, the two batchings; Fold.lean; Switch.lean); All.lean lays them in and states what follows
without the premise.

Under these five: the test's text is one at two states on entry that agree but for targets
(`testAll_agree`); and the two parts of the prover's side are one, moves and all, at two jobs whose
states on entry agree so at every input and front (`testHalf_agree`).

  `Steps`        the five equations, each in the form of `fold_agree`
  `keep_agree`   the text keeps the state before where a part refuses: that keeps `Agree`
  `aFold_agree`, `aRec1_agree`, `aAns_agree`, `aRec3_agree`   one stage, piece by piece
  `stagesAll_agree`   all that is shown in the stages
  `recB_agree`, `testAll_agree`, `testAll_agree₂`, `msgAt_agree`   the test's text: at one input and
                 front, where the two states on entry agree
  `moveAt_agree`, `movesFrom_agree`, `firstPart_agree`, `restPart_agree`, `testHalf_agree`   the
                 parts: these ask the agreement at every input and front, since a move makes its own
                 front of what it is handed

What reads the state on entry. `TestJob.recB` alone, and `testAll` through it: the proof of
`testAll_agree` lays `testAll`'s own body open with `recB` alone turned. By the texts: a part's
stops are constant, its shares are constants, each move hands on what it was handed.

Over what it stands. Files of the kind K10's authors that are not in the library yet
(Johnson/Desc/ProofFile/Honest/K10/: StAtZero, WipeFold, BatWipe, WipeS, Wipe/).

Limits. AT ONE LIST OF GROUPS: THIS IS NO LAW ON A FOLD AT MADE-UP COLUMNS THROUGH THE TEST'S BLOCK:
the columns are the same words on both sides. That `Steps` holds is not said here: it is `theSteps`
(All.lean). The description's sixth part, the base case, is not treated: by reading it tests a
target's value; the verifier runs it, the prover's text of the test never does. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.Fold
import Johnson.Desc.ProofFile.Honest.K12.Blind.Readers
import Johnson.Desc.ProofFile.Honest.K12.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc.K12 (T12 Passing P12 guardedProximityTestParts)
open VerifiableInference.Desc.K12 (Laid)
open Johnson.Prover.Link (PS BCoins BOut rowOf lastOut)
open ProofFile.Honest.K10 (AlikeE)

/-! ## 1 The five steps, by name -/

/-- **The five equations.** -/
structure Steps : Prop where
  front : ∀ (p : P12)
    {t t' : T12}, Agree t t' → ∀ (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    AlikeE wipeT ((guardedProximityTestParts.front p).decide t rs gs)
      ((guardedProximityTestParts.front p).decide t' rs gs)
  bat : ∀ (p : P12) (cut : List Fmt.DeclaredRound)
    {t t' : T12}, Agree t t' → ∀ (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    AlikeE wipeT ((guardedProximityTestParts.bat p cut).decide t rs gs)
      ((guardedProximityTestParts.bat p cut).decide t' rs gs)
  fold : ∀ (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    {t t' : T12}, Agree t t' → ∀ (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    AlikeE wipeT ((guardedProximityTestParts.fold p j cur cut).decide t rs gs)
      ((guardedProximityTestParts.fold p j cur cut).decide t' rs gs)
  switch : ∀ (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound)
    {t t' : T12}, Agree t t' → ∀ (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    AlikeE wipeT ((guardedProximityTestParts.switch p j cur next last cut).decide t rs gs)
      ((guardedProximityTestParts.switch p j cur next last cut).decide t' rs gs)
  batBehind : ∀ (p : P12) (j : ℕ) (next : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    {t t' : T12}, Agree t t' → ∀ (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    AlikeE wipeT ((guardedProximityTestParts.batBehind p j next cut).decide t rs gs)
      ((guardedProximityTestParts.batBehind p j next cut).decide t' rs gs)

/-- Where a part refuses the text keeps the state before. -/
theorem keep_agree {A A' : Except String T12} {t t' : T12} (hA : AlikeE wipeT A A')
    (ht : Agree t t') : Agree (A.toOption.getD t) (A'.toOption.getD t') := by
  rcases hA.split with ⟨e, a, b⟩ | ⟨x, x', a, b, c⟩
  · rw [a, b]
    exact ht
  · rw [a, b]
    exact c

/-! ## 2 The stages -/

theorem aFold_agree (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (P : PS) {t t' : T12}
    (h : Agree t t') (D : ℕ → Fmt.Drawn) :
    aFold K j cur o P (rowOf t) D = aFold K j cur o P (rowOf t') D := by
  unfold aFold
  rw [vecG_wipe _ _ _ (rowOf_agree h)]

theorem aRec1_agree (s5 : Steps) (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) {t t' : T12}
    (h : Agree t t') (rf : List Fmt.RoundView) :
    Agree (aRec1 p j cur l t rf) (aRec1 p j cur l t' rf) :=
  keep_agree (s5.fold _ _ _ _ h _ _) h

theorem aAns_agree (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (D : ℕ → Fmt.Drawn)
    {t t' : T12} (h : Agree t t') (Q : PS) :
    aAns p j cur next o D t Q = aAns p j cur next o D t' Q := by
  unfold aAns
  rw [codes_agree h]

theorem aRec3_agree (s5 : Steps) (p : P12) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (trees : List Tree) (D : ℕ → Fmt.Drawn) {t t' : T12} (h : Agree t t')
    (rs : List Fmt.RoundView) :
    Agree (aRec3 p last j cur next l o trees D t rs)
      (aRec3 p last j cur next l o trees D t' rs) :=
  have h2 := keep_agree (s5.switch p j cur next last _ h _ _) h
  keep_agree (s5.batBehind _ _ _ _ h2 _ _) h2

/-- **All that is shown in the stages is one at two records that agree but for targets.** -/
theorem stagesAll_agree (s5 : Steps) (p : P12) (K : BCoins) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t t' : T12)
      (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn), Agree t t' →
      stagesAll p K rest j cur l o t P trees D = stagesAll p K rest j cur l o t' P trees D
  | [], j, cur, l, o, t, t', P, trees, D, h => by
    simp only [stagesAll, lastAll, lastOut_agree p j cur o h]
  | next :: rest, j, cur, l, o, t, t', P, trees, D, h => by
    have e1 := aFold_agree K j cur o P h D
    have h1 := aRec1_agree s5 p j cur l h (aFold K j cur o P (rowOf t') D)
    have e2 := aAns_agree p j cur next o D h1 (aNext K rest.isEmpty j cur next o P D)
    have h3 := aRec3_agree s5 p rest.isEmpty j cur next l o trees D h1
      (aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t' (aFold K j cur o P (rowOf t') D))
        (aNext K rest.isEmpty j cur next o P D)))
    have ih := stagesAll_agree s5 p K rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((H2K.Pub.sgOf cur).h + (H2K.Pub.sgOf cur).g) + 3) _ _
      (aNext K rest.isEmpty j cur next o P D)
      [((H2K.Pub.sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D))] D
      h3
    simp only [stagesAll, e1, e2, ih]

/-! ## 3 The test's text -/

variable {V W X C : Type}

theorem recB_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12) (w : W)
    (fr : Front X) (h : Agree (J.rec₀ w fr) (r' w fr)) (d : Fmt.Drawn) :
    Agree (J.recB w fr d) (({ J with rec₀ := r' } : TestJob W X).recB w fr d) :=
  have h1 := keep_agree (s5.front J.p h [] []) h
  keep_agree (s5.bat _ _ h1 _ _) h1

/-- **The test's text is one at two states on entry that agree but for targets.** -/
theorem testAll_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12) (w : W)
    (fr : Front X) (h : Agree (J.rec₀ w fr) (r' w fr)) (K : TestCoins) (D : ℕ → Fmt.Drawn) :
    testAll { J with rec₀ := r' } w fr K D = testAll J w fr K D := by
  have hB := recB_agree s5 J r' w fr h (D 0)
  unfold testAll
  show (match J.p.nums.stages with
    | [] => (⟨[], [], []⟩ : BOut)
    | s :: rest =>
      let P := J.first w fr K
      let B := stagesAll J.p (coinsOf J.p.nums.stages K.hide K.rest) rest 0 s (J.laid.drop 1) 1
        (({ J with rec₀ := r' } : TestJob W X).recB w fr (D 0)) P (J.trees₀ w fr K.mem P) D
      ⟨⟨[], D 0⟩ :: B.rs,
        (fun _ => []) ::
          (if J.fresh.isNone then B.tr.set 0 (freshCol (H2K.Pub.sgOf s) P) else B.tr),
        B.gs⟩) = _
  cases J.p.nums.stages with
  | nil => rfl
  | cons s rest =>
    simp only [stagesAll_agree s5 J.p _ rest 0 s (J.laid.drop 1) 1 _ _ (J.first w fr K)
      (J.trees₀ w fr K.mem (J.first w fr K)) D hB]

/-- The same at two jobs. -/
theorem testAll_agree₂ (s5 : Steps) (J J' : TestJob W X) (hp : J.p = J'.p)
    (hm : J.members = J'.members) (hf : J.fresh = J'.fresh) (hr : J.rows₀ = J'.rows₀)
    (ht : J.trees₀ = J'.trees₀) (w : W) (fr : Front X) (h : Agree (J.rec₀ w fr) (J'.rec₀ w fr))
    (K : TestCoins) (D : ℕ → Fmt.Drawn) : testAll J w fr K D = testAll J' w fr K D := by
  obtain ⟨p, members, fresh, rec₀, rows₀, trees₀⟩ := J
  obtain ⟨p', members', fresh', rec₀', rows₀', trees₀'⟩ := J'
  obtain rfl : p = p' := hp
  obtain rfl : members = members' := hm
  obtain rfl : fresh = fresh' := hf
  obtain rfl : rows₀ = rows₀' := hr
  obtain rfl : trees₀ = trees₀' := ht
  exact (testAll_agree s5 ⟨p, members, fresh, rec₀, rows₀, trees₀⟩ rec₀' w fr h K D).symm

theorem msgAt_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12) (w : W)
    (fr : Front X) (h : Agree (J.rec₀ w fr) (r' w fr)) (K : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) : msgAt { J with rec₀ := r' } w fr K D i = msgAt J w fr K D i := by
  unfold msgAt
  rw [testAll_agree s5 J r' w fr h K D]
  rfl

/-! ## 4 The parts -/

theorem moveAt_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) (rd : C → TestCoins) (i : ℕ) :
    moveAt { J with rec₀ := r' } rd i = moveAt J rd i := by
  unfold moveAt
  simp only [msgAt_agree s5 J r' _ _ (h _ _)]

theorem movesFrom_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) (rd : C → TestCoins) (a n : ℕ) :
    movesFrom { J with rec₀ := r' } rd a n = movesFrom J rd a n := by
  unfold movesFrom
  simp only [moveAt_agree s5 J r' h]

/-- **The first part is one**: counts, names, stops, shares and moves. -/
theorem firstPart_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) :
    (firstPart { J with rec₀ := r' } : Part V W X) = firstPart J := by
  obtain ⟨p, members, fresh, rec₀, rows₀, trees₀⟩ := J
  cases fresh with
  | none =>
    unfold firstPart
    exact congrArg _ (movesFrom_agree s5 ⟨p, members, none, rec₀, rows₀, trees₀⟩ r' h _ 0 _)
  | some x =>
    unfold firstPart
    exact congrArg _ (movesFrom_agree s5 ⟨p, members, some x, rec₀, rows₀, trees₀⟩ r' h _ 0 _)

/-- **The second part is one.** -/
theorem restPart_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) :
    (restPart { J with rec₀ := r' } : Part V W X) = restPart J := by
  unfold restPart foldMoves switchMoves baseMoves
  simp only [movesFrom_agree s5 J r' h]
  rfl

/-- **The pair is one.** -/
theorem testHalf_agree (s5 : Steps) (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Agree (J.rec₀ w fr) (r' w fr)) :
    (proverSideOfProximityTest { J with rec₀ := r' } : Placed V W X) = proverSideOfProximityTest J := by
  unfold proverSideOfProximityTest
  rw [firstPart_agree s5 J r' h, restPart_agree s5 J r' h]

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.Steps
#print axioms ProofFile.Honest.K12.Blind.keep_agree
#print axioms ProofFile.Honest.K12.Blind.aFold_agree
#print axioms ProofFile.Honest.K12.Blind.aRec1_agree
#print axioms ProofFile.Honest.K12.Blind.aAns_agree
#print axioms ProofFile.Honest.K12.Blind.aRec3_agree
#print axioms ProofFile.Honest.K12.Blind.stagesAll_agree
#print axioms ProofFile.Honest.K12.Blind.recB_agree
#print axioms ProofFile.Honest.K12.Blind.testAll_agree
#print axioms ProofFile.Honest.K12.Blind.testAll_agree₂
#print axioms ProofFile.Honest.K12.Blind.msgAt_agree
#print axioms ProofFile.Honest.K12.Blind.moveAt_agree
#print axioms ProofFile.Honest.K12.Blind.movesFrom_agree
#print axioms ProofFile.Honest.K12.Blind.firstPart_agree
#print axioms ProofFile.Honest.K12.Blind.restPart_agree
#print axioms ProofFile.Honest.K12.Blind.testHalf_agree
