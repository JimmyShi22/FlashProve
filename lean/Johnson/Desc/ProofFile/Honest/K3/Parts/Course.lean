-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Course.lean: the honest side of the kind "lookup" (K3): a
course whose summands are the specification's AT SEVERAL PARTS OF KEYS: what each stage's job,
true end values and claimed value are. Theorems with proofs; no definition. ALL ARE CONDITIONAL on
premises of Honest/K3/Parts/Lawful.lean (`NumberedP R`, `SpecAtP R N w`) and, where orders or sizes
of parts are read, on the verifier's own tests on the face.

  1  `dataP_congr`, `data_at`, `dataP_at`, `carried_of`; `carried_tie0`,
  `carried_tie`, `carried_split`, `carried_key`,
     `carried_tab`, `carried_leaves`, `carried_bits`   at each stage the course's three functions
     are the job at the run's data and points, carried
  2  `getD_of_mem`, `mem_of_lt`, `perm_of_okP`, `facts_of_ok`, `part_v`   the parts' sizes and
     orders, out of the face's tests
  3  `tie0_ends`, `plane_read`, `tab_zero`, `tab_succ`   the table's side: as at one part
  4  `split_same`, `split_T`, `split_claimed`, `root_read`   WHAT THE PARTS' STEPS CLAIM AND LEAVE:
     the product of the roots from a part on; each part's root
  5  `key_zero`, `key_succ`   each part's tree: the extension of a level at the point in front of it

The texts on the table's side follow Honest/K3/Law/SpecCourse.lean line for line; lemmas that read
neither premise are called from there.

Limits. Nothing is summed here. A member of the premises, by evaluation:
Honest/K3/Parts/Member.lean. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Lawful
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (orderDefault eqTab)
open OnBytes.Slice (readE readE_add readE_sub readE_mul readE_zero readE_one)
open OnBytes.HonestTrace.Look (Job Data pj ext tieJob keyJob tabJob leavesJob bitsJob)
open VerifiableInference.Desc.First.ProdV (layBack levelVars)
open VerifiableInference.Desc.K3 (leafVars bitsCall noVar)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (CarriedAt dataAt_congr T_read shapeAt_eq lineV_read levelCall_len
  fold_add_read G_beyond size_tabPt byBit_behind line_key line_tab tab_root Pc_top)

variable {P : Type} {N : KE → TwV.Nums P KE} {w : Hidden} {R : Course Ask}

/-! ## 1 The jobs at the stages -/

/-- The data at parts hang on theta and alpha alone of the points. -/
theorem dataP_congr (N : KE → TwV.Nums P KE) (vs : List Nat) (oK : Nat → Nat → List Nat)
    (w : Hidden)
    (p q : Pts) (h1 : p.theta = q.theta) (h2 : p.alpha = q.alpha) :
    dataP N vs oK w p = dataP N vs oK w q := by
  unfold dataP
  rw [dataAt_congr N w p q h1 h2, h1]

/-- CONDITIONAL ON `SpecAtP R N w`, and on theta and alpha being the run's: the data at a stage's
own points are the run's. -/
theorem data_at (hS : SpecAtP R N w) (s : Stage) (hs : s ∈ stages R.f)
    (h1 : (R.ptsAt s).theta = R.pts.theta) (h2 : (R.ptsAt s).alpha = R.pts.alpha) :
    dataAt N (R.t.input (R.ptsAt s).heard) (R.ptsAt s) = dataAt N w R.pts := by
  rw [show R.t.input (R.ptsAt s).heard = w from hS.one s hs]
  exact dataAt_congr N w _ _ h1 h2

/-- CONDITIONAL ON `SpecAtP R N w`, and on theta and alpha being the run's: the data at parts at a
stage's own points are the run's. -/
theorem dataP_at (hS : SpecAtP R N w) (s : Stage) (hs : s ∈ stages R.f)
    (h1 : (R.ptsAt s).theta = R.pts.theta) (h2 : (R.ptsAt s).alpha = R.pts.alpha) :
    dataP N R.f.parts R.f.orders (R.t.input (R.ptsAt s).heard) (R.ptsAt s) =
      dataP N R.f.parts R.f.orders w R.pts := by
  rw [show R.t.input (R.ptsAt s).heard = w from hS.one s hs]
  exact dataP_congr N _ _ w _ _ h1 h2

/-- CONDITIONAL ON `SpecAtP R N w`: a stage whose entry in the filling is a carried job. -/
theorem carried_of (hS : SpecAtP R N w) (s : Stage) (Jf : Hidden → Pts → Job KE)
    (hj : (specJobsP N R.f.parts R.f.orders).job s = carry Jf) (J : Job KE)
    (hJ : Jf (R.t.input (R.ptsAt s).heard) (R.ptsAt s) = J) : CarriedAt R s J := by
  subst hJ
  refine ⟨fun rs => ?_, fun rs m => ?_, fun rs => ?_⟩
  · rw [hS.J]
    show ((specJobsP N R.f.parts R.f.orders).job s).round (R.t.input (R.ptsAt s).heard)
      (R.ptsAt s) rs = _
    rw [hj]
    rfl
  · rw [hS.J]
    show ((specJobsP N R.f.parts R.f.orders).job s).inY (R.t.input (R.ptsAt s).heard)
      (R.ptsAt s) rs m = _
    rw [hj]
    rfl
  · rw [hS.J]
    show ((specJobsP N R.f.parts R.f.orders).job s).ends (R.t.input (R.ptsAt s).heard)
      (R.ptsAt s) rs = _
    rw [hj]
    rfl

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: at the tie's first step the course's three
functions are `tieTop` at the product of all parts' roots, carried. -/
theorem carried_tie0 (hW : NumberedP R) (hS : SpecAtP R N w) (hs : Stage.tie 0 ∈ stages R.f) :
    CarriedAt R (.tie 0) (tieTop ((dataP N R.f.parts R.f.orders w R.pts).rest 0)
      (dataAt N w R.pts).a
      ((dataAt N w R.pts).Pc 1) ((dataAt N w R.pts).G 0)) := by
  obtain ⟨h1, h2⟩ : _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => tieTop ((dataP N R.f.parts R.f.orders w p).rest 0)
    (dataAt N w p).a ((dataAt N w p).Pc 1) ((dataAt N w p).G 0)) rfl _ ?_
  show tieTop ((dataP N _ _ _ _).rest 0) (dataAt N _ _).a ((dataAt N _ _).Pc 1)
    ((dataAt N _ _).G 0) = _
  rw [data_at hS _ hs h1 h2, dataP_at hS _ hs h1 h2]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the like at a later step of the tie: the
specification's own job at the shared data. -/
theorem carried_tie (hW : NumberedP R) (hS : SpecAtP R N w) (j : Nat)
    (hs : Stage.tie (j + 1) ∈ stages R.f) :
    CarriedAt R (.tie (j + 1)) (tieJob (dataAt N w R.pts) (j + 1)) := by
  obtain ⟨h1, h2⟩ : _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => tieJob (dataAt N w p) (j + 1)) rfl _ ?_
  show tieJob (dataAt N _ _) (j + 1) = _
  rw [data_at hS _ hs h1 h2]

/-- CONDITIONAL ON `SpecAtP R N w`, and on theta and alpha at the step being the run's: the like at
a parts' step. -/
theorem carried_split (hS : SpecAtP R N w) (i : Nat) (hs : Stage.split i ∈ stages R.f)
    (h1 : (R.ptsAt (.split i)).theta = R.pts.theta) (h2 : (R.ptsAt (.split i)).alpha =
      R.pts.alpha) :
    CarriedAt R (.split i) (splitJob (dataP N R.f.parts R.f.orders w R.pts) i) := by
  refine carried_of hS _ (fun w p => splitJob (dataP N R.f.parts R.f.orders w p) i) rfl _ ?_
  show splitJob (dataP N _ _ _ _) i = _
  rw [dataP_at hS _ hs h1 h2]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the like at a level of part i's tree: the
specification's own job AT PART i's DATA, at the run's point in front of the level. -/
theorem carried_key (hW : NumberedP R) (hS : SpecAtP R N w) (i m : Nat)
    (hs : Stage.key i m ∈ stages R.f) :
    CarriedAt R (.key i m)
      (keyJob ((dataP N R.f.parts R.f.orders w R.pts).part i) m (byBit (R.pts.keyPt i m))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p =>
    keyJob ((dataP N R.f.parts R.f.orders w p).part i) m (byBit (p.keyPt i m))) rfl _ ?_
  show keyJob ((dataP N _ _ _ _).part i) m (byBit ((R.ptsAt (.key i m)).keyPt i m)) = _
  rw [dataP_at hS _ hs h1 h2, h3]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the like at a level of the table side. -/
theorem carried_tab (hW : NumberedP R) (hS : SpecAtP R N w) (l : Nat)
    (hs : Stage.tab l ∈ stages R.f) :
    CarriedAt R (.tab l) (tabJob (dataAt N w R.pts) l (byBit (R.pts.tabPt l))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => tabJob (dataAt N w p) l (byBit (p.tabPt l))) rfl _ ?_
  show tabJob (dataAt N _ _) l (byBit ((R.ptsAt (.tab l)).tabPt l)) = _
  rw [data_at hS _ hs h1 h2, h3]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the like at the leaves. -/
theorem carried_leaves (hW : NumberedP R) (hS : SpecAtP R N w) (hs : Stage.leaves ∈ stages R.f) :
    CarriedAt R .leaves (leavesJob (dataAt N w R.pts) (byBit (R.pts.tabPt R.f.d))) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _
    (fun w p => leavesJob (dataAt N w p) (byBit (p.tabPt (N (up p.theta)).d))) rfl _ ?_
  show leavesJob (dataAt N _ _)
    (byBit ((R.ptsAt .leaves).tabPt (N (up (R.ptsAt .leaves).theta)).d)) = _
  rw [data_at hS _ hs h1 h2, h1, hS.nums.d, h3]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the like at the bits. -/
theorem carried_bits (hW : NumberedP R) (hS : SpecAtP R N w) (hs : Stage.bits ∈ stages R.f) :
    CarriedAt R .bits (bitsJob (dataAt N w R.pts) (byBit R.pts.zeroPt)) := by
  obtain ⟨h1, h2, h3⟩ : _ ∧ _ ∧ _ := hW.same _ hs
  refine carried_of hS _ (fun w p => bitsJob (dataAt N w p) (byBit p.zeroPt)) rfl _ ?_
  show bitsJob (dataAt N _ _) (byBit (R.ptsAt .bits).zeroPt) = _
  rw [data_at hS _ hs h1 h2, h3]

/-! ## 2 The parts' sizes and orders -/

/-- A member of the numbered list of parts: the part's size stands at its number. -/
theorem getD_of_mem {l : List Nat} {y : Nat × Nat} (hy : y ∈ l.zipIdx) :
    y.2 < l.length ∧ l.getD y.2 0 = y.1 := by
  obtain ⟨a, i⟩ := y
  have h := List.mem_zipIdx_iff_getElem?.1 hy
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h
  exact ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩

/-- The part with a number below the list's length is a member of the numbered list. -/
theorem mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : (l.getD i 0, i) ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem _ _ hi]
  exact List.getElem?_eq_getElem hi

/-- The verifier's tests on a face give: each level's order of each part's tree lists that
level's variables, each once. -/
theorem perm_of_okP {f : LFace} (hok : f.ok = true) {y : Nat × Nat} (hy : y ∈ f.parts.zipIdx)
    {l : Nat} (hl : l < y.1) : (f.orders y.2 l).Perm (List.range l) := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, List.all_eq_true] at hok
  have h1 := hok.2 y hy
  simp only [VerifiableInference.Desc.First.Prod.runOk, Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 l (List.mem_range.2 hl)
  rw [Nat.zero_add] at h2
  exact perm_of_orderOk (show VerifiableInference.Desc.First.ProdV.orderOk l (f.orders y.2 l) = true
    from h2)

/-- The verifier's tests on a face give: every part has a level; there is a part; the planes that
count lie among the 2 ^ mu. -/
theorem facts_of_ok {f : LFace} (hok : f.ok = true) :
    (∀ v ∈ f.parts, 1 ≤ v) ∧ 0 < f.parts.length ∧ f.planes ≤ 2 ^ f.mu := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  refine ⟨hok.1.1.1.2, ?_, hok.1.1.1.1.1.2⟩
  have := hok.1.1.1.1.2
  cases h : f.parts with
  | nil => simp [h] at this
  | cons a l => simp

/-- Part i's number of levels, as its data have it. -/
theorem part_v (A : DataP P) {y : Nat × Nat} (hy : y ∈ A.vs.zipIdx) (hpos : 1 ≤ y.1) :
    (A.part y.2).v = y.1 := by
  show A.vs.getD y.2 0 - 1 + 1 = y.1
  rw [(getD_of_mem hy).2]
  omega

/-- CONDITIONAL ON `NumberedP R`: a level's sumcheck has a challenge for each variable and
one for Y. -/
theorem len_level (hW : NumberedP R) (s : Stage) (m : Nat) (hs : s ∈ stages R.f)
    (hc : s.call R.f = some (levelCall m)) : (R.r s).length = m + 1 := by
  rw [hW.len s hs, shapeAt_eq R s _ hc]
  show ((levelCall m).vs ++ [_]).length = m + 1
  rw [List.length_append, levelCall_len]
  rfl

/-- CONDITIONAL ON `SpecAtP R N w`: the tie has a first step. -/
theorem mem_tie0 (hS : SpecAtP R N w) : Stage.tie 0 ∈ stages R.f :=
  mem_tie (by rw [hS.nums.planes]; omega)

/-! ## 3 The table's side -/

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the true end values of the tie's first step,
read: the product of all parts' roots; the chain from plane 1 on; plane 0's root. -/
theorem tie0_ends (hW : NumberedP R) (hS : SpecAtP R N w) (j : Nat) :
    rd (R.T (.tie 0) j) = [(dataP N R.f.parts R.f.orders w R.pts).rest 0, (dataAt N w R.pts).Pc 1,
      (dataAt N w R.pts).G 0].getD j 0 :=
  T_read R (.tie 0) (noVar 3 3) _ rfl (carried_tie0 hW hS (mem_tie0 hS)) j

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **A plane's true root, as the tie's end
values hold it.** -/
theorem plane_read (hW : NumberedP R) (hS : SpecAtP R N w) (j : Nat) (hj : j < R.f.planes) :
    rd (R.planeV j) = (dataAt N w R.pts).G j := by
  have hpl := hS.nums.planes
  have hn : (dataAt N w R.pts).N.n + 2 = R.f.planes := hpl.symm
  unfold Course.planeV
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, tie0_ends hW hS 2]
    rfl
  · rw [if_neg h0]
    obtain ⟨s, rfl⟩ : ∃ s, j = s + 1 := ⟨j - 1, by omega⟩
    by_cases h1 : s + 1 + 1 < R.f.planes
    · rw [if_pos h1, T_read R (.tie (s + 1)) (noVar 3 2) _ rfl
        (carried_tie hW hS s (mem_tie (by omega))),
        OnBytes.HonestTrace.Look.tie_ends_succ]
      rfl
    · rw [if_neg h1]
      have hs : s = (dataAt N w R.pts).N.n := by omega
      by_cases h2 : R.f.planes = 2
      · rw [if_pos h2, tie0_ends hW hS 1]
        have hz : (dataAt N w R.pts).N.n = 0 := by omega
        have := Pc_top (dataAt N w R.pts)
        rw [hz] at this
        rw [hs, hz]
        exact this
      · rw [if_neg h2]
        obtain ⟨t, ht⟩ : ∃ t, R.f.planes - 2 = t + 1 := ⟨R.f.planes - 3, by omega⟩
        rw [ht, T_read R (.tie (t + 1)) (noVar 3 2) _ rfl
          (carried_tie hW hS t (mem_tie (by omega))),
          OnBytes.HonestTrace.Look.tie_ends_succ]
        have hn' : (dataAt N w R.pts).N.n = t + 1 := by omega
        have := Pc_top (dataAt N w R.pts)
        rw [hn'] at this
        rw [hs, hn']
        exact this

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **In front of the table side's trees**: the
claimed value is the extension of the planes' roots at JOIN's point. -/
theorem tab_zero (hW : NumberedP R) (hS : SpecAtP R N w) :
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

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **Behind a level of the table side.** -/
theorem tab_succ (hW : NumberedP R) (hS : SpecAtP R N w) (l : Nat) (hl : l < R.f.d) :
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

/-! ## 4 The parts' steps -/

/-- theta and alpha at a parts' step are the run's. -/
theorem split_same (hW : NumberedP R) (i : Nat) (hs : Stage.split i ∈ stages R.f) :
    (R.ptsAt (.split i)).theta = R.pts.theta ∧ (R.ptsAt (.split i)).alpha = R.pts.alpha :=
  hW.same _ hs

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`: the true end values of a parts' step, read:
this part's root; the product of the roots behind it. -/
theorem split_T (hW : NumberedP R) (hS : SpecAtP R N w) (i : Nat) (hs : Stage.split i ∈ stages R.f)
    (j : Nat) :
    rd (R.T (.split i) j) = [(dataP N R.f.parts R.f.orders w R.pts).Zi i,
      (dataP N R.f.parts R.f.orders w R.pts).rest (i + 1)].getD j 0 := by
  obtain ⟨h1, h2⟩ := split_same hW i hs
  rw [T_read R (.split i) (noVar 2 2) _ rfl (carried_split hS i hs h1 h2), split_ends]

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **What a parts' step claims**: the product of
the roots from its part on. -/
theorem split_claimed (hW : NumberedP R) (hS : SpecAtP R N w) (i : Nat)
    (hs : Stage.split i ∈ stages R.f) :
    rd (R.claimed (.split i)) = (dataP N R.f.parts R.f.orders w R.pts).rest i := by
  cases i with
  | zero =>
    show rd (R.T (.tie 0) 0) = _
    rw [tie0_ends hW hS 0]
    rfl
  | succ i =>
    show rd (R.T (.split i) 1) = _
    rw [split_T hW hS i (mem_split (by have := split_lt hs; omega)) 1]
    rfl

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **Each part's root, as the steps' end
values hold it.** -/
theorem root_read (hW : NumberedP R) (hS : SpecAtP R N w) (i : Nat) (hi : i < R.f.parts.length) :
    rd (R.rootV i) = (dataP N R.f.parts R.f.orders w R.pts).Zi i := by
  unfold Course.rootV
  by_cases h1 : i + 1 < R.f.parts.length
  · rw [if_pos h1, split_T hW hS i (mem_split (by omega)) 0]
    rfl
  · rw [if_neg h1]
    have hl : i + 1 = (dataP N R.f.parts R.f.orders w R.pts).vs.length := by
      show i + 1 = R.f.parts.length
      omega
    by_cases h2 : R.f.parts.length ≤ 1
    · have h0 : i = 0 := by omega
      subst h0
      rw [if_pos h2, tie0_ends hW hS 0]
      exact DataP.rest_last _ hl
    · obtain ⟨k, hk⟩ : ∃ k, R.f.parts.length - 2 = k := ⟨_, rfl⟩
      have hik : i = k + 1 := by omega
      rw [if_neg h2, hk, split_T hW hS k (mem_split (by omega)) 1, hik]
      exact DataP.rest_last _ (by rw [← hik]; exact hl)

/-! ## 5 Each part's tree -/

/-- CONDITIONAL ON `NumberedP R` AND `SpecAtP R N w`. **In front of part i's tree**: the claimed
value is that part's root. -/
theorem key_zero (hW : NumberedP R) (hS : SpecAtP R N w) (i : Nat) (hi : i < R.f.parts.length) :
    rd (R.claimed (.key i 0)) =
      ext 0 (((dataP N R.f.parts R.f.orders w R.pts).part i).kLvl 0) (byBit (R.pts.keyPt i 0)) := by
  show rd (R.rootV i) = _
  rw [root_read hW hS i hi]
  exact (OnBytes.HonestTrace.Look.kLvl_root ((dataP N R.f.parts R.f.orders w R.pts).part i)).symm

/-- CONDITIONAL ON `NumberedP R`, `SpecAtP R N w` AND the verifier's tests on the face. **Behind a
level of part i's tree**: the claimed value is the extension of the level below at the point
behind the level. -/
theorem key_succ (hW : NumberedP R) (hS : SpecAtP R N w) (hok : R.f.ok = true) {y : Nat × Nat}
    (hy : y ∈ R.f.parts.zipIdx) (m : Nat) (hm : m < y.1) :
    rd (R.claimed (.key y.2 (m + 1))) =
      ext (m + 1) (((dataP N R.f.parts R.f.orders w R.pts).part y.2).kLvl (m + 1))
        (byBit (R.pts.keyPt y.2 (m + 1))) := by
  have hs : Stage.key y.2 m ∈ stages R.f := mem_keyOf hy hm
  have hp : (R.f.orders y.2 m).Perm (List.range m) := perm_of_okP hok hy hm
  have hl := len_level hW _ m hs rfl
  show rd (R.lineV (.key y.2 m) (R.xiK y.2 m)) = _
  rw [lineV_read, T_read R _ (levelCall m) _ rfl (carried_key hW hS y.2 m hs),
    T_read R _ (levelCall m) _ rfl (carried_key hW hS y.2 m hs), levelCall_len,
    hW.key y hy m hm, byBit_behind m _ _ _ hp (by rw [List.length_take, hl]; omega)]
  exact line_key ((dataP N R.f.parts R.f.orders w R.pts).part y.2) m _ _ _ hp

#print axioms ProofFile.Honest.K3.Parts.dataP_congr
#print axioms ProofFile.Honest.K3.Parts.data_at
#print axioms ProofFile.Honest.K3.Parts.dataP_at
#print axioms ProofFile.Honest.K3.Parts.carried_of
#print axioms ProofFile.Honest.K3.Parts.carried_tie0
#print axioms ProofFile.Honest.K3.Parts.carried_tie
#print axioms ProofFile.Honest.K3.Parts.carried_split
#print axioms ProofFile.Honest.K3.Parts.carried_key
#print axioms ProofFile.Honest.K3.Parts.carried_tab
#print axioms ProofFile.Honest.K3.Parts.carried_leaves
#print axioms ProofFile.Honest.K3.Parts.carried_bits
#print axioms ProofFile.Honest.K3.Parts.getD_of_mem
#print axioms ProofFile.Honest.K3.Parts.mem_of_lt
#print axioms ProofFile.Honest.K3.Parts.perm_of_okP
#print axioms ProofFile.Honest.K3.Parts.facts_of_ok
#print axioms ProofFile.Honest.K3.Parts.part_v
#print axioms ProofFile.Honest.K3.Parts.len_level
#print axioms ProofFile.Honest.K3.Parts.mem_tie0
#print axioms ProofFile.Honest.K3.Parts.tie0_ends
#print axioms ProofFile.Honest.K3.Parts.plane_read
#print axioms ProofFile.Honest.K3.Parts.tab_zero
#print axioms ProofFile.Honest.K3.Parts.tab_succ
#print axioms ProofFile.Honest.K3.Parts.split_same
#print axioms ProofFile.Honest.K3.Parts.split_T
#print axioms ProofFile.Honest.K3.Parts.split_claimed
#print axioms ProofFile.Honest.K3.Parts.root_read
#print axioms ProofFile.Honest.K3.Parts.key_zero
#print axioms ProofFile.Honest.K3.Parts.key_succ

end ProofFile.Honest.K3.Parts
