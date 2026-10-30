-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByAll.lean: `stagesBy_of`: the six statements
`Spec.dense_reads`, `Spec.fold_eq`, `Spec.next_tab`, `Spec.col_eq`, `Spec.ans_eq` and `Spec.last_eq`
(RunBySpec.lean) imply `Spec.stagesBy_eq`: `stagesBy` (RunBy.lean) gives the rounds, trees and
opened columns of `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean). By induction on the list of
later stages. The six are hypotheses here; RunByEq.lean supplies their proofs.

  `okFrom_le`, `okFrom_room`, `okFrom_last`, `pow2B_of_fit`, `switchFitB_pows`   what `okFrom` and
                 `switchFitB` (RunBy.lean) give
  `bPt`, `bFold`, `bBits`, `bAns`   the sub-terms of one stage of `stagesBy`, as definitions
  `stagesBy_cons`   `stagesBy` at a stage that is not the last, written with them (by unfolding)
  `lib_tree`     the field `tree` of `Seams.lib` (Run.lean), unfolded
  `stagesBy_of`   the implication

Limits. At `Seams.lib` alone. The warnings (`RunOut.no`) are left out. The trees of the stage at
which `Spec.stagesBy_eq` starts are one variable on both sides, and `groupOf` is `groupAt` by
unfolding (`groupOf_eq`, RunBySpec.lean): so that stage's opened columns are the same term on both
sides. The later stages' trees are computed in two ways (`Spec.col_eq`). Two definitions give the
same words; nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE vecIn vecG)
open Johnson.Prover.Link (PS BCoins BOut μOf coefU groupAt rowOf)
open Fmt.M1 (Stage GRow)
open Fmt.M1.Own (PSt tabOf colOf lhs)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.K12 (P12 T12 Laid guardedProximityTestParts stageAt)
open H2K.Pub (sgOf)

/-! ## 1 What `okFrom` gives -/

theorem okFrom_le {s : Stage} {rest : List Stage} (h : okFrom s rest = true) : s.h ≤ s.k := by
  cases rest with
  | nil =>
    simp only [okFrom, Bool.and_eq_true, beq_iff_eq] at h
    omega
  | cons n rest =>
    simp only [okFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1

theorem okFrom_room {s : Stage} {rest : List Stage} (h : okFrom s rest = true)
    (hr : rest.isEmpty = false) : 2 * s.k + 1 ≤ s.h + s.Z.l := by
  cases rest with
  | nil => exact absurd hr (by simp)
  | cons n rest =>
    simp only [okFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2

theorem okFrom_last {s : Stage} {rest : List Stage} (h : okFrom s rest = true)
    (hr : rest.isEmpty = true) : s.k = 0 := by
  cases rest with
  | nil =>
    simp only [okFrom, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  | cons n rest => exact absurd hr (by simp)

/-- If `switchFitB s n` holds, s's main message length is a power of two. -/
theorem pow2B_of_fit {s n : Stage} (h : switchFitB s n = true) : pow2B s.C.l = true := by
  simp only [switchFitB, pow2B, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨h1, -⟩, h3⟩, -⟩, -⟩ := h
  have e : s.C.l = 2 ^ (n.k + Fmt.M1.lg n.C.l) := by rw [← h1, Nat.pow_add, ← h3]
  have l2 : Fmt.M1.lg s.C.l = n.k + Fmt.M1.lg n.C.l := by
    rw [e]
    exact Nat.log2_two_pow
  rw [l2]
  exact e

theorem switchFitB_pows {s n : Stage} (h : switchFitB s n = true) :
    pow2B n.C.l = true ∧ pow2B n.Z.l = true := by
  simp only [switchFitB, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

/-! ## 2 The sub-terms of one stage of `stagesBy` -/

/-- The elements that the fold's rounds sampled. -/
def bPt (cur : Stage) (o : ℕ) (D : ℕ → Fmt.Drawn) : List Fmt.M1.E :=
  (List.range cur.k).map fun n => headE (D (o + 1 + n))

/-- The fold's rounds, as `stagesBy` computes them. -/
def bFold (S : Seams) (K : Sorted) (j : ℕ) (cur : Stage) (o : ℕ) (t : T12) (P : PSt)
    (D : ℕ → Fmt.Drawn) : List Fmt.RoundView :=
  ⟨[.e (Fmt.M1.FoldOwn.Trial.sigma .two
      { k := cur.k, h := cur.h, G := S.dense (rowAt t) cur, m := S.tab P.M cur.C.l
        mu := S.tab P.W cur.Z.l, U := hideBy K (j + 1), eps := headE (D o), g := bPt cur o D
        lzk := cur.Z.l })], D o⟩ ::
    ((S.rounds .two
      { k := cur.k, h := cur.h, G := S.dense (rowAt t) cur, m := S.tab P.M cur.C.l
        mu := S.tab P.W cur.Z.l, U := hideBy K (j + 1), eps := headE (D o), g := bPt cur o D
        lzk := cur.Z.l } (bPt cur o D)).map (·.1)).zipIdx.map
      fun q => ⟨[.e q.1.1, .e q.1.2], D (o + 1 + q.2)⟩

/-- How many coordinates the point of the switch's sample has. -/
def bBits (p : P12) (j : ℕ) (next : Stage) (t₁ : T12) : ℕ :=
  (OnBytes.Send.cube t₁.st.codes
    (OnBytes.switchTargetStage ((stageAt p (j + 1) next).getD default).code
      ((stageAt p (j + 1) next).getD default).maskCode next.k next.h 1).shape).bits

/-- The answer sent in the round "CS", as `stagesBy` computes it. -/
def bAns (S : Seams) (p : P12) (j : ℕ) (cur next : Stage) (o : ℕ) (D : ℕ → Fmt.Drawn) (t₁ : T12)
    (Q : PSt) : Fmt.M1.E :=
  lhs .two
    (Fmt.M1.sampleRow .two next.Am next.Az
      ((List.range next.na).map fun i =>
        ((D (o + 1 + cur.k)).elems.take (bBits p j next t₁)).getD i Fmt.Fld.zeroE)
      (orOneW ((D (o + 1 + cur.k)).elems.getD (bBits p j next t₁) Fmt.Fld.zeroE)) Fmt.Fld.zeroE)
    (S.tab Q.M next.C.l) (S.tab Q.W next.Z.l)

/-- `stagesBy` at a stage that is not the last, without the warnings. -/
theorem stagesBy_cons (S : Seams) (p : P12) (K : Sorted) (next : Stage) (rest : List Stage) (j : ℕ)
    (cur : Stage) (l : Laid) (o : ℕ) (t : T12) (P : PSt) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) :
    (stagesBy S p K (next :: rest) j cur l o t P trees D).toB =
      let rf := bFold S K j cur o t P D
      let Q := nextBy S .two K (j + 2) cur next rest.isEmpty (bPt cur o D) P
      let tree := S.tree next rest.isEmpty Q
      let col := tree.2
      let t₁ := (keep t ((guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
        (rf.map noDigest) [])).1
      let rs : List Fmt.RoundView :=
        [⟨[], D (o + 1 + cur.k)⟩, ⟨[.answer (bAns S p j cur next o D t₁ Q)], D (o + 2 + cur.k)⟩]
      let gs := trees.map fun x => groupOf x (D (o + 2 + cur.k)).poss
      let cutS := ((l.drop (1 + cur.k)).take 2).map (·.1)
      let t₂ := (keep t₁ ((guardedProximityTestParts.switch p j cur next rest.isEmpty cutS).decide t₁
        (rs.map noDigest) gs)).1
      let t₃ := (keep t₂ ((guardedProximityTestParts.batBehind p (j + 1) next cutS).decide t₂ [] [])).1
      let R := (stagesBy S p K rest (j + 1) next (l.drop (cur.k + 3)) (o + cur.k + 3) t₃ Q
        [tree] D).toB
      ⟨rf ++ rs ++ R.rs, rf.map (fun _ _ => []) ++ [col, fun _ => []] ++ R.tr, gs ++ R.gs⟩ := rfl

/-- The tree that a switch sends, at `Seams.lib`. -/
theorem lib_tree (next : Stage) (last : Bool) (Q : PSt) :
    Seams.lib.tree next last Q = (next.C.a, colOf next false last Q) := rfl

/-! ## 3 The fold's rounds and the answer -/

theorem bFold_eq (hD : Spec.dense_reads) (hF : Spec.fold_eq) (K : Sorted) (B : BCoins) (j : ℕ)
    (s : Stage) (last : Bool) (o : ℕ) (t : T12) (P : PS) (q : PSt) (D : ℕ → Fmt.Drawn)
    (hh : s.h ≤ s.k) (hp : pow2B s.C.l = true) (hH : HideTie K B j s) (T : Tab s last P q) :
    bFold Seams.lib K j s o t q D = aFold B j s o P (rowOf t) D := by
  obtain ⟨d1, d2, d3⟩ := hD (rowAt t) s hh hp
  have e := hF s (denseAt (rowAt t) s) last P q (hideBy K (j + 1)) (fun n => D (o + n)) hh d2 d3 T
  rw [d1, hH.1, rowAt_eq] at e
  simp only [← Nat.add_assoc, Nat.add_zero] at e
  exact e

theorem bAns_eq (hA : Spec.ans_eq) (p : P12) (j : ℕ) (cur next : Stage) (last : Bool) (o : ℕ)
    (D : ℕ → Fmt.Drawn) (t₁ : T12) (Q : PS) (q : PSt) (h1 : cur.h ≤ cur.k) (h2 : next.h ≤ next.k)
    (h3 : pow2B next.C.l = true) (h4 : pow2B next.Z.l = true) (T : Tab next last Q q) :
    bAns Seams.lib p j cur next o D t₁ q = ofE (aAns p j cur next o D t₁ Q) :=
  hA p j cur next last o D t₁ Q q h1 h2 h3 h4 T

/-! ## 4 All stages -/

theorem stagesBy_of (hD : Spec.dense_reads) (hF : Spec.fold_eq) (hN : Spec.next_tab)
    (hC : Spec.col_eq) (hA : Spec.ans_eq) (hL : Spec.last_eq) : Spec.stagesBy_eq := by
  intro p K B rest
  induction rest with
  | nil =>
    intro j s l o t P q trees D ok _ _ T
    simp only [okFrom, Bool.and_eq_true, beq_iff_eq] at ok
    exact hL Seams.lib p K j s l o t P q trees D ok.1 ok.2 T
  | cons next rest ih =>
    intro j s l o t P q trees D ok ties hide T
    have hh : s.h ≤ s.k := okFrom_le ok
    simp only [okFrom, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨-, hfit⟩, ok'⟩ := ok
    have hh' : next.h ≤ next.k := okFrom_le ok'
    have hk := sg_k hh
    have T0 : Tab s false P q := T
    have e1 : bFold Seams.lib K j s o t q D = aFold B j s o P (rowOf t) D :=
      bFold_eq hD hF K B j s false o t P q D hh (pow2B_of_fit hfit) (hide (by simp)) T0
    have TQ : Tab next rest.isEmpty (aNext B rest.isEmpty j s next o P D)
        (nextBy Seams.lib .two K (j + 2) s next rest.isEmpty (bPt s o D) q) :=
      hN K B j s next rest.isEmpty o P q D hh hh' hfit (okFrom_room ok') T0 ties.1
    have e3 := hC next rest.isEmpty _ _ hh' (okFrom_last ok') TQ
    have e5 := fun t₁ => bAns_eq hA p j s next rest.isEmpty o D t₁ _ _ hh hh'
      (switchFitB_pows hfit).1 (switchFitB_pows hfit).2 TQ
    have i1 : o + 1 + ((sgOf s).h + (sgOf s).g) = o + 1 + s.k := by rw [hk]
    have i2 : o + 2 + ((sgOf s).h + (sgOf s).g) = o + 2 + s.k := by rw [hk]
    have i3 : o + ((sgOf s).h + (sgOf s).g) + 3 = o + s.k + 3 := by rw [hk]
    have hide' : rest ≠ [] → HideTie K B (j + 1) next := fun hr =>
      ties.1.hide (by cases rest with
        | nil => exact absurd rfl hr
        | cons _ _ => rfl)
    rw [stagesBy_cons]
    unfold stagesAll
    simp only [lib_tree, e1, e3, e5, keep_fst]
    rw [ih (j + 1) next _ _ _ _ _ _ D ok' ties.2 hide' TQ]
    simp only [aRec1, aRec3, aSwitch, aGroups, groupsAt, i1, i2, i3, groupOf_eq]
    rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.okFrom_le
#print axioms ProofFile.Honest.K12.Light.okFrom_room
#print axioms ProofFile.Honest.K12.Light.okFrom_last
#print axioms ProofFile.Honest.K12.Light.pow2B_of_fit
#print axioms ProofFile.Honest.K12.Light.switchFitB_pows
#print axioms ProofFile.Honest.K12.Light.stagesBy_cons
#print axioms ProofFile.Honest.K12.Light.lib_tree
#print axioms ProofFile.Honest.K12.Light.bFold_eq
#print axioms ProofFile.Honest.K12.Light.bAns_eq
#print axioms ProofFile.Honest.K12.Light.stagesBy_of
#print axioms ProofFile.Honest.K12.Light.bPt
#print axioms ProofFile.Honest.K12.Light.bFold
#print axioms ProofFile.Honest.K12.Light.bBits
#print axioms ProofFile.Honest.K12.Light.bAns
