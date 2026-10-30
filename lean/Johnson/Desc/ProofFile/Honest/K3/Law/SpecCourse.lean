-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecCourse.lean: the honest side of the kind "lookup" (K3). A
course whose summands are the specification's: what each stage's job, variables, true end values and
claimed value are. Theorems. Those of sections 1 and 4 are conditional on the hypotheses
`Numbered R` and `SpecAt R N w` of Honest/K3/Law/SpecLawful.lean, or on one of them, but for five
helpers that bear neither (`dataAt_congr`; `lineV_read`, `levelCall_len`, `fold_add_read`,
`G_beyond`); those of sections 2 and 3 on neither.

Terms. Honest/K3/GLOSSARY.md ("course", "job, summand", "specification", "stage").

What is shown, by the file's sections.
  1. `data_at`, `carried_of`, `carried_tie`, `carried_key`, `carried_tab`, `carried_leaves`,
     `carried_bits`: at each stage the course's three functions are the specification's job at the
     run's data and points, carried.
  2. `size_keyPt`, `size_tabPt`, `size_zeroPt`; `withPoints_tab`, `withPoints_leaves`,
     `withPoints_bits`: sizes of points; the variables at the points.
  3. `key_lt`, `tab_lt`, `mem_key`: which stages stand in the row of a face with one part.
  4. `key_zero`, `key_succ`, `plane_read`, `tab_zero`, `tab_succ`: what the claimed values are: the
     extension of a tree's level at the point in front of it.

Others, in no line above: `dataAt_congr`, `lineV_read`, `levelCall_len`, `len_level`, `mem_tie0`,
`fold_add_read`, `G_beyond`, `mem_leaves`, `mem_bits`.

Hypotheses that remain. `hW`: `Numbered R`; `hS`: `SpecAt R N w`. Besides: `hs`: the stage is one of
the row's; `hp`: one part of keys; `hm`, `hl`, `hj`: a level's, or a plane's, number is in range (in
`G_beyond`: beyond it); `hz`: a point's size; `hc`: the stage's call is the level's; `h1`, `h2`: two
structures of points have one theta and one alpha; `hj`, `hJ`: (in `carried_of`) the specification's
job at the stage is the carried Jf, which yields J at the run's data and points.

Users. This file is imported by Honest/K3/FastLaw/Lift.lean, Honest/K3/Law/SpecNumbered.lean,
Honest/K3/Law/SpecProof.lean, Honest/K3/Law/Thread/DigitsPointsAt.lean and
Honest/K3/Law/Thread/ExchangeKeys.lean.

Limits. One part of keys. Nothing is summed here.
An instance of the two hypotheses: Honest/K3/Law/SpecMember.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecValues
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecLawful
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import OnBytes.Tie.Pv.Lookup.Ends.FoRowH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (orderDefault eqTab)
open OnBytes.Slice (readE readE_add readE_sub readE_mul readE_zero readE_one)
open OnBytes.HonestTrace.Look (Job Data pj ext tieJob keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (layBack levelVars)
open VerifiableInference.Desc.K3 (leafVars bitsCall noVar)

variable {P : Type} {N : KE → TwV.Nums P KE} {w : Hidden} {R : Course Ask}

/-! ## 1 The jobs at the stages -/

/-- The specification's data depend on theta and alpha alone of the points. -/
theorem dataAt_congr (N : KE → TwV.Nums P KE) (w : Hidden) (p q : Pts) (h1 : p.theta = q.theta)
    (h2 : p.alpha = q.alpha) : dataAt N w p = dataAt N w q := by
  unfold dataAt
  rw [h1, h2]

/-- Conditional on `SpecAt R N w`, and on theta and alpha being the run's: the data at a stage's own
points are the run's. -/
theorem data_at (hS : SpecAt R N w) (s : Stage) (hs : s ∈ stages R.f)
    (h1 : (R.ptsAt s).theta = R.pts.theta) (h2 : (R.ptsAt s).alpha = R.pts.alpha) :
    dataAt N (R.t.input (R.ptsAt s).heard) (R.ptsAt s) = dataAt N w R.pts := by
  rw [show R.t.input (R.ptsAt s).heard = w from hS.one s hs]
  exact dataAt_congr N w _ _ h1 h2

/-- Conditional on `SpecAt R N w`: a stage whose entry in the filling is a carried job. -/
theorem carried_of (hS : SpecAt R N w) (s : Stage) (Jf : Hidden → Pts → Job KE)
    (hj : (specJobs N).job s = carry Jf) (J : Job KE)
    (hJ : Jf (R.t.input (R.ptsAt s).heard) (R.ptsAt s) = J) : CarriedAt R s J := by
  subst hJ
  refine ⟨fun rs => ?_, fun rs m => ?_, fun rs => ?_⟩
  · rw [hS.J]
    show ((specJobs N).job s).round (R.t.input (R.ptsAt s).heard) (R.ptsAt s) rs = _
    rw [hj]
    rfl
  · rw [hS.J]
    show ((specJobs N).job s).inY (R.t.input (R.ptsAt s).heard) (R.ptsAt s) rs m = _
    rw [hj]
    rfl
  · rw [hS.J]
    show ((specJobs N).job s).ends (R.t.input (R.ptsAt s).heard) (R.ptsAt s) rs = _
    rw [hj]
    rfl

/-- Conditional on `Numbered R` and `SpecAt R N w`: at a step of the tie the course's three
functions are the specification's job at the run's data, carried. -/
theorem carried_tie (hW : Numbered R) (hS : SpecAt R N w) (j : Nat)
    (hs : Stage.tie j ∈ stages R.f) :
    CarriedAt R (.tie j) (tieJob (dataAt N w R.pts) j) := by
  obtain ⟨h1, h2⟩ : _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => tieJob (dataAt N w p) j) rfl _ ?_
  show tieJob (dataAt N _ _) j = _
  rw [data_at hS _ hs h1 h2]

/-- Conditional on `Numbered R` and `SpecAt R N w`: the like at a level of the key tree, at the
run's point in front of it. -/
theorem carried_key (hW : Numbered R) (hS : SpecAt R N w) (m : Nat)
    (hs : Stage.key 0 m ∈ stages R.f) :
    CarriedAt R (.key 0 m) (keyJob (dataAt N w R.pts) m (byBit (R.pts.keyPt 0 m))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => keyJob (dataAt N w p) m (byBit (p.keyPt 0 m))) rfl _ ?_
  show keyJob (dataAt N _ _) m (byBit ((R.ptsAt (.key 0 m)).keyPt 0 m)) = _
  rw [data_at hS _ hs h1 h2, h3]

/-- Conditional on `Numbered R` and `SpecAt R N w`: the like at a level of the table side. -/
theorem carried_tab (hW : Numbered R) (hS : SpecAt R N w) (l : Nat)
    (hs : Stage.tab l ∈ stages R.f) :
    CarriedAt R (.tab l) (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => tabJob (dataAt N w p) l (byBit (p.tabPt l))) rfl _ ?_
  show tabJob (dataAt N _ _) l (byBit ((R.ptsAt (.tab l)).tabPt l)) = _
  rw [data_at hS _ hs h1 h2, h3]

/-- Conditional on `Numbered R` and `SpecAt R N w`: the like at the leaves. -/
theorem carried_leaves (hW : Numbered R) (hS : SpecAt R N w) (hs : Stage.leaves ∈ stages R.f) :
    CarriedAt R .leaves (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _
    (fun w p => leavesJob (dataAt N w p) (byBit (p.tabPt (N (up p.theta)).d))) rfl _ ?_
  show leavesJob (dataAt N _ _)
    (byBit ((R.ptsAt .leaves).tabPt (N (up (R.ptsAt .leaves).theta)).d)) = _
  rw [data_at hS _ hs h1 h2, h1, hS.nums.d, h3]

/-- Conditional on `Numbered R` and `SpecAt R N w`: the like at the bits. -/
theorem carried_bits (hW : Numbered R) (hS : SpecAt R N w) (hs : Stage.bits ∈ stages R.f) :
    CarriedAt R .bits (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => bitsJob (dataAt N w p) (byBit p.zeroPt)) rfl _ ?_
  show bitsJob (dataAt N _ _) (byBit (R.ptsAt .bits).zeroPt) = _
  rw [data_at hS _ hs h1 h2, h3]

/-! ## 2 Sizes of points; the variables at the points -/

/-- The point in front of a key level has one coordinate for each variable. -/
theorem size_keyPt (f : LFace) (base : Nat) (heard : List Fmt.Drawn) (i m : Nat) :
    ((ptsOf f base heard).keyPt i m).size = m := by
  cases m with
  | zero => rfl
  | succ m =>
    show (behind m _ _ _).size = m + 1
    unfold behind
    rw [Array.size_append, VerifiableInference.Desc.First.ProdV.layBack_size]
    simp
    omega

/-- The like on the table's side. -/
theorem size_tabPt (f : LFace) (base : Nat) (heard : List Fmt.Drawn) (l : Nat) :
    ((ptsOf f base heard).tabPt l).size = f.mu + l := by
  cases l with
  | zero =>
    show ((drawsAt heard _ f.mu).toArray.reverse).size = f.mu + 0
    simp [drawsAt]
  | succ l =>
    show (behind (f.mu + l) _ _ _).size = f.mu + (l + 1)
    unfold behind
    rw [Array.size_append, VerifiableInference.Desc.First.ProdV.layBack_size]
    simp
    omega

/-- The bits' point has mu + d coordinates. -/
theorem size_zeroPt (f : LFace) (base : Nat) (heard : List Fmt.Drawn) :
    (ptsOf f base heard).zeroPt.size = f.mu + f.d := by
  show ((drawsAt heard _ (f.mu + f.d)).toArray.reverse).size = f.mu + f.d
  simp [drawsAt]

/-- At a level of the table side the shape with the points written in is the verifier's own list
of variables. -/
theorem withPoints_tab (f : LFace) (l : Nat) (p : Pts) :
    withPoints (levelCall (f.mu + l)).vs (pointsAt f (.tab l) p) =
      levelVars (f.mu + l) (p.tabPt l) (orderDefault (f.mu + l)) := by
  rw [← blank_levelVars (f.mu + l) (p.tabPt l) (orderDefault (f.mu + l)) (by simp [orderDefault])]
  exact withPoints_blank _

/-- The like at the leaves. -/
theorem withPoints_leaves (f : LFace) (p : Pts) :
    withPoints (leafVars f #[]) (pointsAt f .leaves p) = leafVars f (p.tabPt f.d) := by
  have e : (leafVars f (p.tabPt f.d)).map blank = leafVars f #[] := by
    unfold leafVars
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp [blank]
  rw [← e]
  exact withPoints_blank _

/-- The like at the bits, at a point of mu + d coordinates. -/
theorem withPoints_bits (f : LFace) (p : Pts) (hz : p.zeroPt.size = f.mu + f.d) :
    withPoints (bitsCall (List.replicate (f.mu + f.d) zeroE)).vs (pointsAt f .bits p) =
      (bitsCall p.zeroPt.toList).vs := by
  have e : (bitsCall p.zeroPt.toList).vs.map blank =
      (bitsCall (List.replicate (f.mu + f.d) zeroE)).vs := by
    unfold bitsCall
    simp only [List.map_map, List.map_replicate]
    rw [← hz, ← Array.length_toList, ← List.map_const']
    rfl
  rw [← e]
  exact withPoints_blank _

/-! ## 3 Which stages stand in the row -/

/-- At one part of keys: a level of a key tree that stands in the row is the first
part's, below v. -/
theorem key_lt {f : LFace} {v i m : Nat} (hp : f.parts = [v]) (hs : Stage.key i m ∈ stages f) :
    i = 0 ∧ m < v := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc, hp] at hs <;> exact ⟨hs.2, hs.1⟩

/-- A level of the table side that stands in the row is below d. -/
theorem tab_lt {f : LFace} {l : Nat} (hs : Stage.tab l ∈ stages f) : l < f.d := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

/-- At one part of keys: the first part's levels below v stand in the row. -/
theorem mem_key {f : LFace} {v m : Nat} (hp : f.parts = [v]) (hm : m < v) :
    Stage.key 0 m ∈ stages f :=
  mem_keyOf (f := f) (y := (v, 0)) (by rw [hp]; simp) hm

/-- The leaves stand in the row. -/
theorem mem_leaves (f : LFace) : Stage.leaves ∈ stages f := by
  unfold stages
  simp

/-- The bits stand in the row. -/
theorem mem_bits (f : LFace) : Stage.bits ∈ stages f := by
  unfold stages
  simp

/-! ## 4 What the claimed values are -/

/-- The line between a level's two true end values, read. -/
theorem lineV_read (R : Course Ask) (s : Stage) (xi : E) :
    rd (R.lineV s xi) = (1 - up xi) * rd (R.T s 0) + up xi * rd (R.T s 1) := by
  show readE (addE (mulE (subE oneE xi) (R.T s 0)) (mulE xi (R.T s 1))) = _
  rw [readE_add, readE_mul, readE_mul, readE_sub, readE_one]
  rfl

/-- A level's call has as many variables as the level. -/
theorem levelCall_len (m : Nat) : (levelCall m).vs.length = m := by simp [levelCall, levelVars]

/-- Conditional on `Numbered R`: a level's sumcheck has a challenge for each variable and
one for Y. -/
theorem len_level (hW : Numbered R) (s : Stage) (m : Nat) (hs : s ∈ stages R.f)
    (hc : s.call R.f = some (levelCall m)) : (R.r s).length = m + 1 := by
  rw [hW.len s hs, shapeAt_eq R s _ hc]
  show ((levelCall m).vs ++ [_]).length = m + 1
  rw [List.length_append, levelCall_len]
  rfl

/-- Conditional on `SpecAt R N w`: the tie has a first step. -/
theorem mem_tie0 (hS : SpecAt R N w) : Stage.tie 0 ∈ stages R.f :=
  mem_tie (by rw [hS.nums.planes]; omega)

/-- Conditional on `Numbered R` and `SpecAt R N w`. **In front of the key tree**: the claimed value
is the key side's root. -/
theorem key_zero (hW : Numbered R) (hS : SpecAt R N w) :
    rd (R.claimed (.key 0 0)) =
      ext 0 ((dataAt N w R.pts).kLvl 0) (byBit (R.pts.keyPt 0 0)) := by
  have e : R.claimed (.key 0 0) = R.T (.tie 0) 0 := by
    show R.rootV 0 = _
    unfold Course.rootV
    rw [hS.nums.parts]
    simp
  rw [e, T_read R (.tie 0) (noVar 3 3) _ rfl (carried_tie hW hS 0 (mem_tie0 hS)),
    OnBytes.HonestTrace.Look.tie_ends_zero]
  exact (OnBytes.HonestTrace.Look.kLvl_root (dataAt N w R.pts)).symm

/-- Conditional on `Numbered R` and `SpecAt R N w`. **Behind a key level**: the claimed value is the
extension of the level below at the point behind the level. -/
theorem key_succ (hW : Numbered R) (hS : SpecAt R N w) (m : Nat)
    (hm : m < (dataAt N w R.pts).v) :
    rd (R.claimed (.key 0 (m + 1))) =
      ext (m + 1) ((dataAt N w R.pts).kLvl (m + 1)) (byBit (R.pts.keyPt 0 (m + 1))) := by
  have hs : Stage.key 0 m ∈ stages R.f := mem_key hS.nums.parts hm
  have hp : (R.f.orders 0 m).Perm (List.range m) := by
    rw [← hS.nums.oK m]
    exact hS.nums.permK m hm
  have hl := len_level hW _ m hs rfl
  show rd (R.lineV (.key 0 m) (R.xiK 0 m)) = _
  rw [lineV_read, T_read R _ (levelCall m) _ rfl (carried_key hW hS m hs),
    T_read R _ (levelCall m) _ rfl (carried_key hW hS m hs), levelCall_len,
    hW.key m (by rw [hS.nums.parts]; exact hm),
    byBit_behind m _ _ _ hp (by rw [List.length_take, hl]; omega), ← hS.nums.oK m]
  exact line_key (dataAt N w R.pts) m _ _ _ (hS.nums.permK m hm)

/-- A sum that is folded, read. -/
theorem fold_add_read (g : Nat → E) : ∀ (l : List Nat) (c : E),
    up (l.foldl (fun c j => addE c (g j)) c) = up c + (l.map fun j => up (g j)).sum
  | [], c => by simp
  | j :: l, c => by
    rw [List.foldl_cons, fold_add_read g l, List.map_cons, List.sum_cons,
      show up (addE c (g j)) = up c + up (g j) from readE_add _ _, add_assoc]

/-- Conditional on `Numbered R` and `SpecAt R N w`. **A plane's true root, as the tie's end
values hold it.** -/
theorem plane_read (hW : Numbered R) (hS : SpecAt R N w) (j : Nat) (hj : j < R.f.planes) :
    rd (R.planeV j) = (dataAt N w R.pts).G j := by
  have hpl := hS.nums.planes
  have hn : (dataAt N w R.pts).N.n + 2 = R.f.planes := hpl.symm
  unfold Course.planeV
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, T_read R (.tie 0) (noVar 3 3) _ rfl (carried_tie hW hS 0 (mem_tie0 hS)),
      OnBytes.HonestTrace.Look.tie_ends_zero]
    rfl
  · rw [if_neg h0]
    obtain ⟨s, rfl⟩ : ∃ s, j = s + 1 := ⟨j - 1, by omega⟩
    by_cases h1 : s + 1 + 1 < R.f.planes
    · rw [if_pos h1, T_read R (.tie (s + 1)) (noVar 3 2) _ rfl
        (carried_tie hW hS (s + 1) (mem_tie (by omega))),
        OnBytes.HonestTrace.Look.tie_ends_succ]
      rfl
    · rw [if_neg h1]
      have hs : s = (dataAt N w R.pts).N.n := by omega
      by_cases h2 : R.f.planes = 2
      · rw [if_pos h2, T_read R (.tie 0) (noVar 3 3) _ rfl (carried_tie hW hS 0 (mem_tie0 hS)),
          OnBytes.HonestTrace.Look.tie_ends_zero]
        have hz : (dataAt N w R.pts).N.n = 0 := by omega
        have := Pc_top (dataAt N w R.pts)
        rw [hz] at this
        rw [hs, hz]
        exact this
      · rw [if_neg h2]
        obtain ⟨t, ht⟩ : ∃ t, R.f.planes - 2 = t + 1 := ⟨R.f.planes - 3, by omega⟩
        rw [ht, T_read R (.tie (t + 1)) (noVar 3 2) _ rfl
          (carried_tie hW hS (t + 1) (mem_tie (by omega))),
          OnBytes.HonestTrace.Look.tie_ends_succ]
        have hn' : (dataAt N w R.pts).N.n = t + 1 := by omega
        have := Pc_top (dataAt N w R.pts)
        rw [hn'] at this
        rw [hs, hn']
        exact this

/-- A plane that does not count has the root 1. -/
theorem G_beyond (N : KE → TwV.Nums P KE) (w : Hidden) (p : Pts) (j : Nat)
    (hj : (dataAt N w p).N.n + 2 ≤ j) : (dataAt N w p).G j = 1 :=
  G_one _ j fun u => if_neg (by
    show ¬ j < (N (up p.theta)).n + 2
    exact Nat.not_lt.2 hj)

/-- Conditional on `Numbered R` and `SpecAt R N w`. **In front of the table side's trees**: the
claimed value is the extension of the planes' roots at JOIN's point. -/
theorem tab_zero (hW : Numbered R) (hS : SpecAt R N w) :
    rd (R.tabV 0) = ext ((dataAt N w R.pts).N.w + 0) ((dataAt N w R.pts).tLvl 0)
      (byBit (R.pts.tabPt 0)) := by
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hsz : R.pts.rhoT.size = R.f.mu := size_tabPt R.f R.a.base _ 0
  show up R.joinV = ext (dataAt N w R.pts).N.w _ (byBit R.pts.rhoT)
  unfold Course.joinV
  rw [fold_add_read, show up zeroE = 0 from readE_zero, zero_add, _root_.Fo.lsum, tab_root, hw]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ R.pts.rhoT.size := by rw [hsz]; exact Finset.mem_range.1 hj
  rw [show up (mulE ((eqTab R.pts.rhoT).getD j zeroE)
      (if j < R.f.planes then R.planeV j else oneE)) =
    up ((eqTab R.pts.rhoT).getD j zeroE) * up (if j < R.f.planes then R.planeV j else oneE)
    from readE_mul _ _]
  congr 1
  · refine (_root_.Fo.eqTab_at gl R.pts.rhoT j hj').trans ?_
    congr 1
    simp [_root_.Fo.rdA, byBit, ups]
    exact fun _ _ => rfl
  · by_cases hp : j < R.f.planes
    · rw [if_pos hp]
      exact plane_read hW hS j hp
    · rw [if_neg hp, G_beyond N w R.pts j (by
        show (N (up R.pts.theta)).n + 2 ≤ j
        rw [← hS.nums.planes]
        omega)]
      exact readE_one

/-- Conditional on `Numbered R` and `SpecAt R N w`. **Behind a level of the table side.** -/
theorem tab_succ (hW : Numbered R) (hS : SpecAt R N w) (l : Nat) (hl : l < R.f.d) :
    rd (R.tabV (l + 1)) =
      ext ((dataAt N w R.pts).N.w + l + 1) ((dataAt N w R.pts).tLvl (l + 1))
        (byBit (R.pts.tabPt (l + 1))) := by
  have hs : Stage.tab l ∈ stages R.f := mem_tabOf hl
  have hw : (dataAt N w R.pts).N.w = R.f.mu := hS.nums.w
  have hT : (dataAt N w R.pts).N.oT l = orderDefault (R.f.mu + l) := hS.nums.oT l
  have hlen := len_level hW _ (R.f.mu + l) hs rfl
  show rd (R.lineV (.tab l) (R.xiT l)) = _
  rw [lineV_read, T_read R _ (levelCall (R.f.mu + l)) _ rfl (carried_tab hW hS l hs),
    T_read R _ (levelCall (R.f.mu + l)) _ rfl (carried_tab hW hS l hs), levelCall_len,
    hW.tab l hl, byBit_behind _ _ _ _ (perm_orderDefault _)
      (by rw [List.length_take, hlen]; omega), ← hT]
  exact line_tab (dataAt N w R.pts) l _ _ _ (by rw [hT, hw]; exact perm_orderDefault _)

#print axioms ProofFile.Honest.K3.Law.Spec.lineV_read
#print axioms ProofFile.Honest.K3.Law.Spec.len_level
#print axioms ProofFile.Honest.K3.Law.Spec.key_zero
#print axioms ProofFile.Honest.K3.Law.Spec.key_succ
#print axioms ProofFile.Honest.K3.Law.Spec.fold_add_read
#print axioms ProofFile.Honest.K3.Law.Spec.plane_read
#print axioms ProofFile.Honest.K3.Law.Spec.G_beyond
#print axioms ProofFile.Honest.K3.Law.Spec.tab_zero
#print axioms ProofFile.Honest.K3.Law.Spec.tab_succ
#print axioms ProofFile.Honest.K3.Law.Spec.dataAt_congr
#print axioms ProofFile.Honest.K3.Law.Spec.data_at
#print axioms ProofFile.Honest.K3.Law.Spec.carried_of
#print axioms ProofFile.Honest.K3.Law.Spec.carried_tie
#print axioms ProofFile.Honest.K3.Law.Spec.carried_key
#print axioms ProofFile.Honest.K3.Law.Spec.carried_tab
#print axioms ProofFile.Honest.K3.Law.Spec.carried_leaves
#print axioms ProofFile.Honest.K3.Law.Spec.carried_bits
#print axioms ProofFile.Honest.K3.Law.Spec.size_keyPt
#print axioms ProofFile.Honest.K3.Law.Spec.size_tabPt
#print axioms ProofFile.Honest.K3.Law.Spec.size_zeroPt
#print axioms ProofFile.Honest.K3.Law.Spec.withPoints_tab
#print axioms ProofFile.Honest.K3.Law.Spec.withPoints_leaves
#print axioms ProofFile.Honest.K3.Law.Spec.withPoints_bits
#print axioms ProofFile.Honest.K3.Law.Spec.key_lt
#print axioms ProofFile.Honest.K3.Law.Spec.tab_lt
#print axioms ProofFile.Honest.K3.Law.Spec.mem_key
#print axioms ProofFile.Honest.K3.Law.Spec.mem_leaves
#print axioms ProofFile.Honest.K3.Law.Spec.mem_bits
#print axioms ProofFile.Honest.K3.Law.Spec.levelCall_len
#print axioms ProofFile.Honest.K3.Law.Spec.mem_tie0

end ProofFile.Honest.K3.Law.Spec
