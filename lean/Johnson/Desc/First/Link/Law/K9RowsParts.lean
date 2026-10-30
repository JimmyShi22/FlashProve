-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9RowsParts.lean: WHERE `Attention.plan` RETURNS A PLAN A0, AND UNDER
TWO PREMISES ON ITS STRUCTURE (it counts its matrices; each shape's rows of symbols are the matrix's
rows over three, rounded up): THE LEFT SIDE OF THE TEST `rowsFitB`
(Johnson/Desc/First/Link/K9RowsAsk.lean: the plan's claims, the indices that the ties take and the
indices that the reads take are together at most the rows of the batching's declared round), WRITTEN
AT A0's OWN NUMBERS (A0.nLin, A0.seam.tl, attPairs A0.S), IS AT MOST THE PLAN's OWN A0.own.rows
(`rows_att`). With it lemmas on the parts of that expression. Statements with their proofs; nothing
is evaluated here.

  `foldl_sum`   a fold that adds is a sum
  `firstB_fold`   GENERAL: `firstB tl` is the first summand of `HTailF2.equationsF`
      (OnBytes/Model/Tail.lean), where the structure counts its matrices and each shape's rows of
      symbols are the matrix's rows over three, rounded up
  `one_hit`, `readsB_le`   GENERAL: `readsB` counts each table at most once
  `sum_repF`, `sum_partsF`, `sum_attEq`, `sum_attF`   the list `attTriples` under any function
  `plane_nKFp`, `scores_nKFp`, `call_nKFp`, `units_count`, `units_eq`   the units for which the
      tables are laid are the planner's own count `(Attention.Counts.of S).nKFp`
  `as_at`, `reads_att`   **where `Attention.plan` returns A0: the reads counted off the plan's
      tables are at most `Attention.tableReads`**: by the make, no numeral
  `rows_join`   GENERAL IN THE SORT: from these and "the plan's rows are its claims and equationsF
      at the planner's reads" (the library's `planG_rows`, `planA_rows`, `planH2_rows`)
  `rows_att`   so at an attention plan: the test's left side is at most the plan's own.rows

THE TWO PREMISES ARE THEOREMS OF THE LIBRARY WHEREVER A PLANNER RETURNS; they are not called here.
The first: `Fo.planG_size`, `Fo.planA_size`, `Fo.planH2_size`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean). The second: `OnBytes.Road.K4.Plan.planG_mS`
(Johnson/Road/K4/Plan/ShapeRowsG.lean), `H2K5.Door.planA_mS`
(Johnson/Desc/First/Att/Door/Law/K5ShpOfPlan.lean), `planH2_mS`
(Johnson/Desc/Kinds/Law/HeadPlanMs.lean). So at an attention plan both follow from the planner's
return.

WHAT IS NOT HERE. No theorem here names `rowsFitB`, `claimsAt`, `pairsAt` or a segment. THE ROOF:
that the declared round's rows (`ProofFile.k9Where`) ARE the plan's rows: so of the test's yes nothing is
shown. THE CARRY: that the test's own arguments at an odd l (the stored plan's claims and tables,
the handed segment's structure) are A0's: the stored plan is not A0: it may differ in the field
plFor of seam.tl (`PlanIs`, Johnson/Desc/First/Att/GuardPublic.lean). The like of `reads_att` at the
layers; at the head the library has `reads_head` (Johnson/Desc/First/Link/Law/K9ReadsHeadPaid.lean).

Related lemmas, all outside this file's imports: `foldl_sum` has the statement of `foldl_add`
(Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean); `firstB_fold` is near `firstB_is` (there) followed
by the first half of `Fo.topOf_eq` (OnBytes/Tie/Pv/Lookup/Ends/FoTopOf.lean), which has the same two
premises.

What is not claimed. That `Attention.plan` returns at any input. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.K9PosAttPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Model
open OnBytes.Road.L5 (fixed plan_mats)

/-! ## 1 Folds as sums -/

theorem foldl_sum {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun n x => n + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_sum f l, List.map_cons, List.sum_cons, Nat.add_assoc]

/-! ## 2 The indices that the ties take -/

/-- **firstB is the first summand of `equationsF`.** -/
theorem firstB_fold (tl : HTailF2) (hN : tl.NM = tl.mats.size)
    (hS : ∀ nu < tl.NM, (tl.shp.getD nu {}).mS = ((tl.mats.getD nu {}).m + 2) / 3) :
    firstB tl = tl.mats.foldl (fun n M => n + tl.stepF * 2 ^ clog2 ((M.m + 2) / 3)) 0 := by
  unfold firstB
  rw [← Array.foldl_toList, foldl_sum (fun nu => tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS),
    foldl_sum (fun M : TMat => tl.stepF * 2 ^ clog2 ((M.m + 2) / 3))]
  congr 1
  congr 1
  refine List.ext_getElem (by simp [hN]) fun i h1 h2 => ?_
  have hi : i < tl.NM := by simpa using h1
  have hi' : i < tl.mats.size := hN ▸ hi
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  rw [hS i hi]
  have e : tl.mats.getD i {} = tl.mats[i] := by simp [Array.getD, hi']
  rw [e]

/-! ## 3 The reads: each table is counted at most once -/

theorem one_hit (f : ℕ → ℕ) (a : ℕ) : ∀ n,
    ((List.range n).map fun mu => if a = mu then f mu else 0).sum ≤ f a
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases h : a = n
    · subst h
      have z : ((List.range a).map fun mu => if a = mu then f mu else 0).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hx
        rw [if_neg (by have := List.mem_range.1 hmu; omega)]
      rw [z]
      simp
    · have ih := one_hit f a n
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_neg h]
      omega

theorem readsB_le (NM : ℕ) (mats : Array TMat) : ∀ ps : List (ℕ × ℕ),
    readsB NM mats ps ≤ (ps.map fun t => (mats.getD t.1 {}).m / t.2).sum := by
  intro ps
  unfold readsB
  rw [foldl_sum (fun mu => ps.foldl
    (fun k t => k + if t.1 = mu then (mats.getD mu {}).m / t.2 else 0) 0), Nat.zero_add]
  have e : ∀ mu, ps.foldl (fun k t => k + if t.1 = mu then (mats.getD mu {}).m / t.2 else 0) 0 =
      (ps.map fun t => if t.1 = mu then (mats.getD mu {}).m / t.2 else 0).sum := by
    intro mu
    rw [foldl_sum (fun t : ℕ × ℕ => if t.1 = mu then (mats.getD mu {}).m / t.2 else 0),
      Nat.zero_add]
  simp only [e]
  clear e
  induction ps with
  | nil => simp
  | cons t ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add]
    exact Nat.add_le_add (one_hit (fun mu => (mats.getD mu {}).m / t.2) t.1 NM) ih

/-! ## 4 The list `attTriples` under any function -/

theorem sum_repF (f : ℕ × ℕ × ℕ → ℕ) (l : List (ℕ × ℕ × ℕ)) : ∀ k,
    ((repB k l).map f).sum = k * (l.map f).sum
  | 0 => by simp [repB]
  | k + 1 => by
    show ((l ++ repB k l).map f).sum = _
    rw [List.map_append, List.sum_append, sum_repF f l k, Nat.succ_mul, Nat.add_comm]

theorem sum_partsF (f : ℕ × ℕ × ℕ → ℕ) (a b c : ℕ) : ∀ n, (∀ q < n, f (q, a, b) ≤ c) →
    (((List.range n).flatMap fun q => [(q, a, b)]).map f).sum ≤ n * c
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append]
    have ih := sum_partsF f a b c n fun q hq => h q (by omega)
    have hn := h n (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.succ_mul]
    omega

/-- The list's sum under f, written out. -/
theorem sum_attEq (f : ℕ × ℕ × ℕ → ℕ) (S : Attention.Shape) (k : ℕ) :
    ((attTriples S k).map f).sum =
      3 * (((List.range S.cf.NAs).flatMap fun q =>
        [(q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs)]).map f).sum +
      (k + 6) * f (S.cf.NAs, S.T, S.fillH) +
      f (S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la) +
      (2 * k + 5) * f (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la) +
      3 * f (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA) := by
  unfold attTriples
  simp only [List.map_append, List.sum_append, sum_repF, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

/-- The list's sum under f, from a bound for each of its five sorts of table. -/
theorem sum_attF (f : ℕ × ℕ × ℕ → ℕ) (S : Attention.Shape) (k : ℕ) {cS cH cO cQ cB : ℕ}
    (hS : ∀ q < S.cf.NAs, f (q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs) ≤ cS)
    (hH : f (S.cf.NAs, S.T, S.fillH) ≤ cH)
    (hO : f (S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la) ≤ cO)
    (hQ : f (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la) ≤ cQ)
    (hB : f (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA) ≤ cB) :
    ((attTriples S k).map f).sum ≤
      3 * (S.cf.NAs * cS) + (k + 6) * cH + cO + (2 * k + 5) * cQ + 3 * cB := by
  rw [sum_attEq]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left 3 (sum_partsF f _ _ cS S.cf.NAs hS)) (Nat.mul_le_mul_left _ hH)) hO)
    (Nat.mul_le_mul_left _ hQ)) (Nat.mul_le_mul_left 3 hB)

/-! ## 5 The units of the scores and the planner's count -/

theorem plane_nKFp (k : Attention.ACall) (x : Attention.Counts) (s : Attention.Seg) :
    (Attention.Counts.plane k x s).nKFp = x.nKFp := by
  unfold Attention.Counts.plane
  split <;> rfl

theorem scores_nKFp (S : Attention.Shape) (k : Attention.ACall) (x : Attention.Counts)
    (s : Attention.Seg) :
    (Attention.Counts.scores S k x s).nKFp = x.nKFp + (if k.holds s then 1 else 0) := by
  unfold Attention.Counts.scores
  split <;> rfl

theorem call_nKFp (S : Attention.Shape) (x : Attention.Counts) (k : Attention.ACall) :
    (Attention.Counts.call S x k).nKFp = x.nKFp + (if k.kind == .kfd then
      ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => k.holds s).length else 0) := by
  have pl : ∀ y, ([Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) y).nKFp =
      y.nKFp := fun y => by
    simp only [List.foldl_cons, List.foldl_nil, plane_nKFp]
  have sc : ∀ y, ([Attention.Seg.fm, Attention.Seg.fd].foldl (Attention.Counts.scores S k) y).nKFp =
      y.nKFp + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => k.holds s).length :=
    fun y => by
      simp only [List.foldl_cons, List.foldl_nil, scores_nKFp]
      by_cases h1 : k.holds Attention.Seg.fm = true <;>
        by_cases h2 : k.holds Attention.Seg.fd = true <;>
        simp [h1, h2]
  unfold Attention.Counts.call
  dsimp only
  by_cases hf : (k.kind == Attention.Table.kfd) = true
  · rw [if_pos hf, if_pos hf, sc]
    by_cases hr : (k.kind == Attention.Table.kr) = true
    · rw [if_pos hr, pl]
    · rw [if_neg hr]
  · rw [if_neg hf, if_neg hf]
    by_cases hr : (k.kind == Attention.Table.kr) = true
    · rw [if_pos hr, pl]
      rfl
    · rw [if_neg hr]
      rfl

theorem units_count (S : Attention.Shape) : ∀ (l : List Attention.ACall) (k : ℕ)
    (x : Attention.Counts),
    ((l.zipIdx k).flatMap fun y =>
      if y.1.kind == Attention.Table.kfd then
        ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => y.1.holds s).map
          fun s => (y.2, y.1, s)
      else []).length + x.nKFp = (l.foldl (Attention.Counts.call S) x).nKFp
  | [], _, x => by simp
  | c :: l, k, x => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.foldl_cons,
      ← units_count S l (k + 1) (Attention.Counts.call S x c), call_nKFp]
    by_cases hk : (c.kind == Attention.Table.kfd) = true
    · simp only [hk, if_true, List.length_map]
      omega
    · simp only [hk, if_false, List.length_nil, Bool.false_eq_true]
      omega

/-- The units that the tables are laid for are the planner's own count. -/
theorem units_eq (S : Attention.Shape) : unitsB S = (Attention.Counts.of S).nKFp := by
  unfold unitsB Attention.unitsOf Attention.Counts.of
  rw [← Array.foldl_toList, ← units_count S S.calls.toList 0 {}]
  rfl

/-! ## 6 The reads at an attention plan -/

theorem as_at (S : Attention.Shape) (i : Attention.In) {q : ℕ} (hq : q < S.cf.NAs) :
    (((Attention.matrices S i).map fixed).getD q {}).m = 2 ^ S.cf.lmS := by
  have e : ((Attention.matrices S i).map fixed).getD q {} =
      fixed (Attention.ownMatrix i ("as" ++ toString q) (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) q
        i.wpS) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    unfold Attention.matrices
    rw [Array.getElem?_append_left (by simpa using hq)]
    simp [hq]
  rw [e, fixed_m]
  rfl

/-- **The reads counted off the plan's tables are at most the planner's reads.** -/
theorem reads_att {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A0 : Attention.Plan} (h0 : Attention.plan settings i cf = .ok A0) :
    readsB A0.seam.tl.NM A0.seam.tl.mats (attPairs A0.S) ≤
      Attention.tableReads A0.S (Attention.Counts.of A0.S) := by
  refine (readsB_le _ _ _).trans ?_
  rw [plan_mats h0]
  unfold attPairs
  rw [List.map_map]
  have t := fun j M hM => (tail_at fixed fixed_m fixed_k A0.S A0.inp j M hM).1
  have one : ∀ x : ℕ, 2 ^ x / 2 ^ x = 1 := fun x => Nat.div_self (Nat.two_pow_pos x)
  have hb := sum_attF
    (fun a => (((Attention.matrices A0.S A0.inp).map fixed).getD a.1 {}).m / a.2.1) A0.S
    (unitsB A0.S) (cS := 1) (cH := A0.S.cf.wcH) (cO := A0.S.cf.wcO * A0.S.T / 2 ^ A0.S.cf.la)
    (cQ := A0.S.cf.wcQ * A0.S.T / 2 ^ A0.S.cf.la) (cB := 1)
    (fun q hq => by
      show (((Attention.matrices A0.S A0.inp).map fixed).getD q {}).m / 2 ^ A0.S.cf.lmS ≤ 1
      rw [as_at A0.S A0.inp hq, one])
    (by
      show (((Attention.matrices A0.S A0.inp).map fixed).getD A0.S.cf.NAs {}).m / A0.S.T ≤ _
      have e := t 0 _ rfl
      rw [Nat.add_zero] at e
      rw [e]
      exact Nat.div_le_of_le_mul (by
        show A0.S.cf.wcH * A0.S.T ≤ A0.S.T * A0.S.cf.wcH
        rw [Nat.mul_comm]))
    (by
      show (((Attention.matrices A0.S A0.inp).map fixed).getD (A0.S.cf.NAs + 1) {}).m /
        2 ^ A0.S.cf.la ≤ _
      rw [t 1 _ rfl]
      exact Nat.le_refl _)
    (by
      show (((Attention.matrices A0.S A0.inp).map fixed).getD (A0.S.cf.NAs + 3) {}).m /
        2 ^ A0.S.cf.la ≤ _
      rw [t 3 _ rfl]
      exact Nat.le_refl _)
    (by
      show (((Attention.matrices A0.S A0.inp).map fixed).getD (A0.S.cf.NAs + 2) {}).m /
        2 ^ A0.S.cf.lmb ≤ 1
      rw [t 2 _ rfl]
      exact (one _).le)
  refine hb.trans ?_
  rw [units_eq]
  unfold Attention.tableReads
  dsimp only
  omega

/-! ## 7 The join, general in the sort -/

/-- **Claims, ties' indices and reads' indices are together at most the plan's rows**: where the
plan's rows are its claims and `equationsF` at the planner's reads. -/
theorem rows_join (tl : HTailF2) (ps : List (ℕ × ℕ)) {n reads rows : ℕ}
    (hN : tl.NM = tl.mats.size)
    (hS : ∀ nu < tl.NM, (tl.shp.getD nu {}).mS = ((tl.mats.getD nu {}).m + 2) / 3)
    (hr : readsB tl.NM tl.mats ps ≤ reads) (hrows : rows = n + tl.equationsF reads) :
    n + (firstB tl + readsB tl.NM tl.mats ps * tl.stepF) ≤ rows := by
  rw [hrows, firstB_fold tl hN hS]
  unfold HTailF2.equationsF
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _) _

/-- At an attention plan. -/
theorem rows_att {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A0 : Attention.Plan} (h0 : Attention.plan settings i cf = .ok A0)
    (hN : A0.seam.tl.NM = A0.seam.tl.mats.size)
    (hS : ∀ nu < A0.seam.tl.NM,
      (A0.seam.tl.shp.getD nu {}).mS = ((A0.seam.tl.mats.getD nu {}).m + 2) / 3) :
    A0.nLin + (firstB A0.seam.tl +
      readsB A0.seam.tl.NM A0.seam.tl.mats (attPairs A0.S) * A0.seam.tl.stepF) ≤ A0.own.rows :=
  rows_join _ _ hN hS (reads_att h0) (Fo.BatRows.planA_rows settings i cf A0 h0)

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.foldl_sum
#print axioms VerifiableInference.Desc.K9Asks.firstB_fold
#print axioms VerifiableInference.Desc.K9Asks.one_hit
#print axioms VerifiableInference.Desc.K9Asks.readsB_le
#print axioms VerifiableInference.Desc.K9Asks.sum_repF
#print axioms VerifiableInference.Desc.K9Asks.sum_partsF
#print axioms VerifiableInference.Desc.K9Asks.sum_attEq
#print axioms VerifiableInference.Desc.K9Asks.sum_attF
#print axioms VerifiableInference.Desc.K9Asks.plane_nKFp
#print axioms VerifiableInference.Desc.K9Asks.scores_nKFp
#print axioms VerifiableInference.Desc.K9Asks.call_nKFp
#print axioms VerifiableInference.Desc.K9Asks.units_count
#print axioms VerifiableInference.Desc.K9Asks.units_eq
#print axioms VerifiableInference.Desc.K9Asks.as_at
#print axioms VerifiableInference.Desc.K9Asks.reads_att
#print axioms VerifiableInference.Desc.K9Asks.rows_join
#print axioms VerifiableInference.Desc.K9Asks.rows_att
