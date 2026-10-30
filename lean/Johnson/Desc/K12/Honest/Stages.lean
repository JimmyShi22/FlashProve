-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Stages.lean: ALL THAT A PROVER SHOWS IN THE STAGES OF A PROXIMITY TEST (the
kind K12: Johnson/Desc/K12/Frame.lean), AS ONE TERM, at a whole family of sampled challenges: the
rounds of the view, each round's tree, the groups of opened columns. General in the place's numbers
(`P12`), in the verifier's state in front, in the first stage's rows and in the trees that hold
them. Definitions with code, and theorems that tie the term to Johnson/Prover/Link/BodyAll.lean. It
hangs on no frame for an honest side.

Why not `bodyAll` itself. (1) It calls `foldQ`, evaluations of which have broken off, and `ansAt`,
for which Lean compiles no code (Johnson/Desc/K12/Honest/Fold.lean has both, and what is known of
the cause), so a part made of it cannot be played in a test. (2) It deals every switch ONE group of
columns, from one tree. Where a group's oracle messages were sent apart, the first switch opens
several trees. From the second stage on the two texts are one: `stages_eq`.

The term is made of that folder's own pieces wherever they run: the state by index and its step
(`PS`, `nextPS`), the packing (`packedN`), the written columns (`stageColW`, `lastCol`), the last
stage (`lastOut`), a group of columns (`groupAt`). As there, it carries the verifier's state, made
by running the description's own parts (`guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) on the rounds and
groups made so far; where a part rejects, the state in hand is kept.

  `Tree`, `groupsAt`   a tree's depth and written column; the groups that an opening of several
                 trees is dealt, tree by tree
  `aFold` ... `aRec3`   one stage that is not the last, piece by piece: the fold's rounds · the
                 sampled point · the prover's state behind · the new tree's column · the verifier's
                 state behind the fold · the answer · the switch's two rounds · the groups · the
                 verifier's state behind the switch and the batching behind it
  `lastAll`, `stagesAll`   the last stage; THE TERM: the stages from a stage on

What is shown.
  `drawn_showRV`, **`point_eq`**: the sampled point, read off the sampled challenges, is `sGam`.
  **`fold_eq`**, **`next_eq`**, **`col_eq`**, **`rec1_eq`**: the fold's rounds, the prover's state
    behind, the new tree's column and the verifier's state behind the fold are `sRF`, `sNext`,
    `sCol`, `sT1`.
  **`ans_eq`**, **`switch_eq`**, **`rec3_eq`**: where the two stages fit: the answer and the
    switch's rounds are `sAns`, `sRS`; and, where one tree of the stage's depth holds the rows, the
    verifier's state behind the switch is `sT3`.
  `FitAll`, **`stages_eq`**: where each stage fits the next and one tree of the stage's depth holds
    the rows, `stagesAll` is `bodyAll`.

Limits.
- The equations hold at all letters, also at coins, rows and states that no run reaches; they say
  that two texts are one, nothing on a decision. At stages that do not fit, the last four say
  nothing. `FitAll` at a list of one stage is `True`: there `stages_eq` is about the last stage
  alone.
- Where a part of the description rejects, the term goes on with the state in hand: what it shows
  behind that point is of no use, and nothing here says when that happens.
- The sampled challenges are counted by the library's h + (k - h), the frame's cut by k: one number
  where h ≤ k, which the test's own test on the plan asks.
- One answer and one pad at each switch: a place whose switches count more answers is not served.
- No honest prover is defined. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## 1 Trees and groups -/

/-- A tree: its depth, and its written column at a position. -/
abbrev Tree : Type := ℕ × (ℕ → List UInt64)

/-- The groups that an opening of these trees is dealt: tree by tree, the columns at the list of the
sampled positions, in the tree's own range. -/
def groupsAt (trees : List Tree) (poss : List ℕ) : List (List (ℕ × List UInt64)) :=
  trees.map fun x => groupAt x.1 poss x.2

/-! ## 2 One stage that is not the last -/

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (trees : List Tree) (row : GroupRow) (D : ℕ → Fmt.Drawn)

/-- The fold's rounds. -/
def aFold : List Fmt.RoundView :=
  foldShown (sgOf cur) (vecG (sgOf cur) row) (μOf (sgOf cur) P) (K.W (sgOf cur) j) fun n =>
    D (o + n)

/-- The sampled point, read off the sampled challenges. -/
def aPoint : Fin ((sgOf cur).h + (sgOf cur).g) → GE :=
  readP ((sgOf cur).h + (sgOf cur).g)
    ((List.range ((sgOf cur).h + (sgOf cur).g)).map fun n =>
      E.ofTriple ((D (o + (n + 1))).elems.headD (0, 0, 0)))

/-- The prover's state behind the switch. -/
def aNext : PS :=
  nextPS (sgOf cur) (aPoint cur o D) (K.fr j)
    (if last then K.new j else { K.new j with fM := packedN (sgOf next) (K.W (sgOf next) (j + 1)) })
    P

/-- The written column of the tree that the switch sends. Q: the state behind the switch. -/
def aCol (Q : PS) : ℕ → List UInt64 :=
  if last then lastCol (sgOf next) Q
  else stageColW (sgOf next) Q.tabM Q.tabZ Q.tM Q.tZ Q.fM Q.fT

/-- The verifier's state behind the fold. rf: the fold's rounds. -/
def aRec1 (rf : List Fmt.RoundView) : T12 :=
  ((guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t (rf.map noDigest)
    []).toOption.getD t

/-- The answer that "CS" shows. t₁: the verifier's state behind the fold. Q: the prover's state
behind the switch. -/
def aAns (t₁ : T12) (Q : PS) : GE :=
  let els := (D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems.map E.ofTriple
  let bits := (Send.cube t₁.st.codes
    (switchTargetStage ((stageAt p (j + 1) next).getD default).code
      ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1).shape).bits
  sampleAt (sgOf next) (readP _ (els.take bits)) (orOne (readE (els.getD bits zeroE)))
    (μOf (sgOf next) Q)

/-- The switch's two rounds. a: the answer. -/
def aSwitch (a : GE) : List Fmt.RoundView :=
  [⟨[], D (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩,
    ⟨[.answer (ofE a)], D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩]

/-- The groups that the switch's opening is dealt. -/
def aGroups : List (List (ℕ × List UInt64)) :=
  groupsAt trees (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss

/-- The verifier's state behind the switch and the batching behind it. t₁: the verifier's state
behind the fold. rs: the switch's rounds. -/
def aRec3 (t₁ : T12) (rs : List Fmt.RoundView) : T12 :=
  let cutS := ((l.drop (1 + cur.k)).take 2).map (·.1)
  let t₂ := ((guardedProximityTestParts.switch p j cur next last cutS).decide t₁ (rs.map noDigest)
    (aGroups cur o trees D)).toOption.getD t₁
  ((guardedProximityTestParts.batBehind p (j + 1) next cutS).decide t₂ [] []).toOption.getD t₂

end Stage

/-! ## 3 All stages -/

/-- The last stage: the rounds of `lastOut`; the groups from these trees. -/
def lastAll (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) : BOut :=
  let L := lastOut p j cur o t P (fun _ => []) (rowOf t) D
  ⟨L.rs, L.tr, groupsAt trees (D (o + 1)).poss⟩

/-- **The rounds, the trees and the groups of the stages from a stage on.** trees: the trees that
hold P's rows. o: the number of the stage's first round. -/
def stagesAll (p : P12) (K : BCoins) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS →
    List Tree → (ℕ → Fmt.Drawn) → BOut
  | [], j, cur, _, o, t, P, trees, D => lastAll p j cur o t P trees D
  | next :: rest, j, cur, l, o, t, P, trees, D =>
    let rf := aFold K j cur o P (rowOf t) D
    let Q := aNext K rest.isEmpty j cur next o P D
    let col := aCol rest.isEmpty next Q
    let t₁ := aRec1 p j cur l t rf
    let rs := aSwitch cur o D (aAns p j cur next o D t₁ Q)
    let R := stagesAll p K rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3) (aRec3 p rest.isEmpty j cur next l o trees D t₁ rs) Q
      [((sgOf next).C.a, col)] D
    ⟨rf ++ rs ++ R.rs, rf.map (fun _ _ => []) ++ [col, fun _ => []] ++ R.tr,
      aGroups cur o trees D ++ R.gs⟩

/-! ## 4 The ties to Johnson/Prover/Link/BodyAll.lean -/

/-- What the rounds of `showRV` sampled first, in order. -/
theorem drawn_showRV : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).map drawnOf =
      (List.range k).map fun n => E.ofTriple ((D n).elems.headD (0, 0, 0))
  | 0, _, _ => rfl
  | k + 1, q, D => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show drawnOf ⟨_, D 0⟩ :: (showRV k _ fun n => D (n + 1)).map drawnOf = _
    rw [drawn_showRV k _ fun n => D (n + 1)]
    rfl

section Ties
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn)

/-- The fold's rounds are `sRF`. -/
theorem fold_eq : sRF K j cur o P row D = aFold K j cur o P row D := rfl

/-- The sampled point is `sGam`. -/
theorem point_eq : sGam K j cur o P row D = aPoint cur o D := by
  unfold sGam aPoint
  congr 1
  show (showRV _ _ fun n => D (o + (n + 1))).map drawnOf = _
  exact drawn_showRV _ _ _

/-- The state behind the switch is `sNext`. -/
theorem next_eq : sNext K last j cur next o P row D = aNext K last j cur next o P D := by
  unfold sNext aNext
  rw [point_eq]

/-- The new tree's column is `sCol`. -/
theorem col_eq :
    sCol K last j cur next o P row D = aCol last next (aNext K last j cur next o P D) := by
  unfold sCol aCol
  rw [next_eq]

/-- The verifier's state behind the fold is `sT1`. -/
theorem rec1_eq : sT1 p K j cur l o t P row D = aRec1 p j cur l t (aFold K j cur o P row D) := rfl

/-- Where the two stages fit, the answer is `sAns`. -/
theorem ans_eq (hf : CsFit (sgOf cur) (sgOf next)) :
    sAns p K j cur next l o t P row D =
      aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P row D))
        (aNext K last j cur next o P D) := by
  unfold sAns aAns
  rw [sampleAt_eq _ _ hf, point_eq, rec1_eq]
  unfold aNext
  rw [muOf_next hf]

/-- Where the two stages fit, the switch's two rounds are `sRS`. -/
theorem switch_eq (hf : CsFit (sgOf cur) (sgOf next)) :
    sRS p K j cur next l o t P row D =
      aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P row D))
        (aNext K last j cur next o P D)) := by
  unfold sRS aSwitch
  rw [ans_eq p K last j cur next l o t P row D hf]

/-- Where the two stages fit and one tree of the stage's depth holds the rows, the verifier's state
behind the switch and the batching behind it is `sT3`. -/
theorem rec3_eq (hf : CsFit (sgOf cur) (sgOf next)) :
    sT3 p K last j cur next l o t P col row D =
      aRec3 p last j cur next l o [((sgOf cur).C.a, col)] D
        (aRec1 p j cur l t (aFold K j cur o P row D))
        (aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P row D))
          (aNext K last j cur next o P D))) := by
  unfold sT3 aRec3
  rw [switch_eq p K last j cur next l o t P row D hf, rec1_eq]
  rfl

end Ties

/-- Each stage fits the next, along a list of stages. -/
def FitAll : Fmt.M1.Stage → List Fmt.M1.Stage → Prop
  | _, [] => True
  | cur, next :: rest => CsFit (sgOf cur) (sgOf next) ∧ FitAll next rest

/-- **Where each stage fits the next and one tree of the stage's depth holds the rows, the term of
this file is `bodyAll`.** -/
theorem stages_eq (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn),
    FitAll cur rest →
    stagesAll p K rest j cur l o t P [((sgOf cur).C.a, col)] D =
      bodyAll p K rest j cur l o t P col D
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, col, D, hf => by
    unfold stagesAll bodyAll
    simp only
    rw [stages_eq p K rest (j + 1) next _ _ _ _ _ D hf.2,
      ← rec3_eq p K rest.isEmpty j cur next l o t P col (rowOf t) D hf.1,
      ← switch_eq p K rest.isEmpty j cur next l o t P (rowOf t) D hf.1,
      ← col_eq K rest.isEmpty j cur next o P (rowOf t) D,
      ← next_eq K rest.isEmpty j cur next o P (rowOf t) D, ← fold_eq]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.drawn_showRV
#print axioms ProofFile.Honest.K12.fold_eq
#print axioms ProofFile.Honest.K12.point_eq
#print axioms ProofFile.Honest.K12.next_eq
#print axioms ProofFile.Honest.K12.col_eq
#print axioms ProofFile.Honest.K12.rec1_eq
#print axioms ProofFile.Honest.K12.ans_eq
#print axioms ProofFile.Honest.K12.switch_eq
#print axioms ProofFile.Honest.K12.rec3_eq
#print axioms ProofFile.Honest.K12.stages_eq
