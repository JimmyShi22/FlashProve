-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunJobLaw.lean: proof of `runJob_eq`. For every `RunJob` R
(RunJob.lean), prover's input, random values and sampled challenges, if the stages pass `StagesOk`
(RunBy.lean), then `runBy` at `RunIn.ofRun R` gives the rounds, trees and opened columns of
`testAll` at `R.toTest`. There is no hypothesis on the rows or on the trees given.

  `red_eq`, `fitL_range`, `normList_eq`, `normRows_eq`, `split_idx`   helpers on lists brought to a
                 length
  `first_read`   decoding any lists (`readPS`) and tabulating the result (`firstOf`) gives
                 `normFirst` of these lists. No hypothesis
  `symBy_eq`, `treeBy_eq`   where h ≤ k and `Tab` (RunBySpec.lean) holds, a chosen row's symbol and
                 a tree are the same words whether computed on words or over the field, at all
                 positions
  `runJob_in`    where the stages pass `StagesOk`, `runBy` at `RunIn.ofRun R` equals `runBy` at
                 `RunIn.ofTest R.toTest`, warnings included, for every `Seams`
  `runJob_eq`, `runJob_halving_eq`   the statement, at `Seams.lib` and at `Seams.halving`

By what. `runJob_in` reduces the statement to `runBy_eq` (RunByEq.lean). `first_tab` gives `Tab` at
the first stage, and `col_symE_wr` (RunByCols.lean) the symbols. `RunIn.ofRun` builds its trees by
`treeW` (ColW.lean) at every `Seams`. So all statements of this file on `RunIn.ofRun`, those at
`Seams.lib` too, speak of `treeW`; the proof of `runJob_in` turns it into `treeBy` by the theorem
`treeW_eq` (ColWLaw.lean), not by unfolding.

Limits.
- The right side's job is built from the left side's data. So on the first stage's rows the equation
  says only that decoding and encoding again brings them to their sizes, not that they are the right
  rows; and it says nothing on a `TestJob` written in another form.
- No hypothesis on the rows is needed because both sides pad short lists with 0, tails too (see
  RunRows.lean's limits). `RunJob.rowsFit` is false in that case.
- Nothing on whether the trees given are those that the senders sent.
- Two definitions give the same words. Nothing follows on what a verifier decides. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunJob
import Johnson.Desc.ProofFile.Honest.K12.RunByEq
import Johnson.Desc.ProofFile.Honest.K12.ColWLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE lst toE_addE toE_zeroE okE_addE length_fitL getD_fitL)
open Johnson.Prover.Link (PS wr mainSym maskSym freshSym)
open Fmt.M1 (Stage fitL)
open Fmt.M1.Own (PSt)
open H2K.Pub (sgOf)

variable {W X : Type}

/-! ## 1 The rows -/

theorem red_eq (x : Fmt.M1.E) : red x = ofE (toE x) :=
  eq_ofE (okE_addE _ _) (by
    show toE (Fmt.Fld.two.addE x Fmt.Fld.zeroE) = toE x
    rw [toE_addE, toE_zeroE, add_zero])

/-- `fitL d n l` has entry j of l at j, and d beyond l's end. -/
theorem fitL_range {α : Type} (d : α) (n : ℕ) (l : List α) :
    fitL d n l = (List.range n).map fun j => l.getD j d := by
  refine List.ext_getElem (by rw [length_fitL, List.length_map, List.length_range]) fun i h₁ _ => ?_
  have hi : i < n := by rw [length_fitL] at h₁; exact h₁
  rw [List.getElem_map, List.getElem_range, ← getD_fitL d n l i hi, List.getD_eq_getElem _ _ h₁]

theorem normList_eq (n : ℕ) (l : List Fmt.M1.E) : normList n l = wr n (lst l) := by
  unfold normList wr
  rw [fitL_range, List.map_map]
  exact List.map_congr_left fun j _ => red_eq _

theorem normRows_eq (nr n : ℕ) (rows : List (List Fmt.M1.E)) :
    normRows nr n rows = (List.range nr).map fun b => wr n (lst (rows.getD b [])) := by
  unfold normRows
  rw [fitL_range, List.map_map]
  exact List.map_congr_left fun b _ => normList_eq n _

/-- Index b + 2 ^ n * c splits into row b and place c. -/
theorem split_idx (n b c : ℕ) (hb : b < 2 ^ n) :
    (b + 2 ^ n * c) % 2 ^ n = b ∧ (b + 2 ^ n * c) / 2 ^ n = c := by
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hb, Nat.zero_add]

/-- Decoding any lists and tabulating the result gives these lists brought to the stage's sizes. -/
theorem first_read (s : Stage) (p : PSt) : firstOf s (readPS s p) = normFirst s p := by
  unfold firstOf normFirst
  rw [normRows_eq, normRows_eq, normRows_eq, normRows_eq]
  have e1 : ((List.range (2 ^ s.k)).map fun b =>
      (List.range s.C.l).map fun c => ofE ((readPS s p).tabM (b + 2 ^ s.k * c))) =
      (List.range (2 ^ s.k)).map fun b => wr s.C.l (lst (p.M.getD b [])) :=
    List.map_congr_left fun b hb => List.map_congr_left fun c _ => by
      show ofE (lst (p.M.getD ((b + 2 ^ s.k * c) % 2 ^ s.k) []) ((b + 2 ^ s.k * c) / 2 ^ s.k)) = _
      rw [(split_idx s.k b c (List.mem_range.1 hb)).1, (split_idx s.k b c (List.mem_range.1 hb)).2]
  have e2 : ((List.range (2 ^ s.h)).map fun b =>
      (List.range s.Z.l).map fun c => ofE ((readPS s p).tabZ (b + 2 ^ s.h * c))) =
      (List.range (2 ^ s.h)).map fun b => wr s.Z.l (lst (p.W.getD b [])) :=
    List.map_congr_left fun b hb => List.map_congr_left fun c _ => by
      show ofE (lst (p.W.getD ((b + 2 ^ s.h * c) % 2 ^ s.h) []) ((b + 2 ^ s.h * c) / 2 ^ s.h)) = _
      rw [(split_idx s.h b c (List.mem_range.1 hb)).1, (split_idx s.h b c (List.mem_range.1 hb)).2]
  rw [e1, e2]
  rfl

/-! ## 2 The trees -/

/-- Where h ≤ k and `Tab` holds, a chosen row's symbol computed on words is the one computed over
the field, encoded. -/
theorem symBy_eq (s : Stage) (P : PS) (p : PSt) (h : s.h ≤ s.k) (T : Tab s false P p) (x : ℕ)
    (r : Sel) : symBy s p x r = symOf s P x r := by
  have hP : p.P = (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b) := T.ride
  have hPi : p.Pi = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b) := T.rideT
  rcases r with ⟨kind, b, base⟩
  cases kind
  · show (if b < 2 ^ s.k then _ else _) = if b < 2 ^ s.k then _ else _
    by_cases hb : b < 2 ^ s.k
    · rw [if_pos hb, if_pos hb, T.main, T.mainT, getD_range _ _ _ b hb, getD_range _ _ _ b hb,
        col_symE_wr]
      show _ = ofE (Johnson.Prover.Link.symG s.C x
        (fun j => P.tabM (b + 2 ^ ((sgOf s).h + (sgOf s).g) * j)) (P.tM b))
      rw [sg_k h]
    · rw [if_neg hb, if_neg hb]
  · show (if b < 2 ^ s.h then _ else _) = if b < 2 ^ s.h then _ else _
    by_cases hb : b < 2 ^ s.h
    · rw [if_pos hb, if_pos hb, T.mask, T.maskT, getD_range _ _ _ b hb, getD_range _ _ _ b hb,
        col_symE_wr]
      rfl
    · rw [if_neg hb, if_neg hb]
  · show (if b < 2 ^ s.h then _ else _) = if b < 2 ^ s.h then _ else _
    by_cases hb : b < 2 ^ s.h
    · rw [if_pos hb, if_pos hb, hP, hPi, getD_range _ _ _ b hb, getD_range _ _ _ b hb,
        col_symE_wr]
      rfl
    · rw [if_neg hb, if_neg hb]

/-- Under the same hypotheses the two trees are equal, at all positions. -/
theorem treeBy_eq (s : Stage) (P : PS) (p : PSt) (h : s.h ≤ s.k) (T : Tab s false P p)
    (t : ℕ × List Sel) : treeBy s t p = treeOf s t P := by
  unfold treeBy treeOf
  have e : (fun x => symBy s p x) = fun x => symOf s P x :=
    funext fun x => funext fun r => symBy_eq s P p h T x r
  exact congrArg (fun f : ℕ → Sel → Fmt.M1.E => (t.1, fun x => wordsAt (f x) t.2)) e

/-! ## 3 The run -/

/-- Where the stages pass `StagesOk`, `runBy` gives the same result, warnings included, at
`RunIn.ofRun R` and at `RunIn.ofTest R.toTest`. -/
theorem runJob_in (S : Seams) (R : RunJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (ok : StagesOk R.p.nums.stages = true) :
    runBy S (RunIn.ofRun R w fr C) D = runBy S (RunIn.ofTest R.toTest w fr C) D := by
  rcases h : R.p.nums.stages with _ | ⟨s, _ | ⟨n, rest⟩⟩
  · rw [h] at ok
    exact absurd ok (by simp [StagesOk])
  · rw [h] at ok
    exact absurd ok (by simp [StagesOk])
  · rw [h] at ok
    have ok' : okFrom s (n :: rest) = true := ok
    have hs : R.s₀ = s := by
      unfold RunJob.s₀
      rw [h]
      rfl
    have T := first_tab W X R.toTest w fr C s (n :: rest) h (by simp) ok'
    have eF : firstOf s (R.toTest.rows₀ w fr C.mem) = normFirst s (R.rows w fr C.mem) := by
      show firstOf s (readPS R.s₀ (R.rows w fr C.mem)) = _
      rw [hs, first_read]
    rw [eF] at T
    have eT : (R.trees.map fun t => treeBy s t
        { normFirst s (R.rows w fr C.mem) with
          P := (ridersBy .two (sortedOf (s :: n :: rest) C) 1 s false).1
          Pi := (ridersBy .two (sortedOf (s :: n :: rest) C) 1 s false).2 }) =
        R.trees.map fun t => treeOf s t (R.toTest.first w fr C) :=
      List.map_congr_left fun t _ => treeBy_eq s _ _ (okFrom_le ok') T t
    have eI : RunIn.ofTest R.toTest w fr C =
        { RunIn.ofRun R w fr C with
          trees := fun _ => R.trees.map fun t => treeOf s t (R.toTest.first w fr C) } := by
      have e0 : R.toTest.s₀ = s := hs
      have eTr : R.toTest.trees₀ w fr C.mem (R.toTest.first w fr C) =
          R.trees.map fun t => treeOf s t (R.toTest.first w fr C) := by
        show (R.trees.map fun t => treeOf R.s₀ t (R.toTest.first w fr C)) = _
        rw [hs]
      unfold RunIn.ofTest RunIn.ofRun
      rw [e0, eF, hs, eTr]
      rfl
    rw [eI]
    unfold runBy
    simp only [RunIn.ofRun, h, hs, treeW_eq]
    rw [show (n :: rest).isEmpty = false from rfl, eT]

/-- Where the stages pass `StagesOk`, `runBy` at `Seams.lib` and `RunIn.ofRun R` gives the rounds,
trees and opened columns of `testAll` at `R.toTest`. The warnings are left out. -/
theorem runJob_eq (R : RunJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (ok : StagesOk R.p.nums.stages = true) :
    (runBy Seams.lib (RunIn.ofRun R w fr C) D).toB = testAll R.toTest w fr C D := by
  rw [runJob_in Seams.lib R w fr C D ok]
  exact runBy_eq W X R.toTest w fr C D ok

/-- The same at `Seams.halving`. -/
theorem runJob_halving_eq (R : RunJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (ok : StagesOk R.p.nums.stages = true) :
    (runBy Seams.halving (RunIn.ofRun R w fr C) D).toB = testAll R.toTest w fr C D := by
  rw [halving_rounds]
  exact runJob_eq R w fr C D ok

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.red_eq
#print axioms ProofFile.Honest.K12.Light.fitL_range
#print axioms ProofFile.Honest.K12.Light.normList_eq
#print axioms ProofFile.Honest.K12.Light.normRows_eq
#print axioms ProofFile.Honest.K12.Light.split_idx
#print axioms ProofFile.Honest.K12.Light.first_read
#print axioms ProofFile.Honest.K12.Light.symBy_eq
#print axioms ProofFile.Honest.K12.Light.treeBy_eq
#print axioms ProofFile.Honest.K12.Light.runJob_in
#print axioms ProofFile.Honest.K12.Light.runJob_eq
#print axioms ProofFile.Honest.K12.Light.runJob_halving_eq
