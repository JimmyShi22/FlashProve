-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinRead.lean: two rows of the program's test for a linear claim on a stored table,
over the field.

The test (OnBytes/Iop/Lin.lean) puts rows aside on sent vectors. A vector lies in the main table of
an oracle message in one of two layouts (OnBytes/Iop/Tensor.lean: VectorLay), and the program writes
a row's coefficients on it as structured vectors that are cut at a length and placed on the table.
This file gives two of the rows in closed form, as functions of elements of the field: the row that
evaluates W at the claim's point (linEvalRow; LinF.eval) and the row that ties Omega to the folded
row (linFoldRow; LinF.fold). The coefficient at an index of a table is a function of the number of
the vector's entry that stands there (laid); the weights are those of a vertex of the cube at a
point (eqW, OnBytes/Slice/SimBasic.lean).

The program's entry function does not look at the digits of an index above a structured vector's
variables. So the closed forms hold at every index: they read the index modulo the table's size.

Main definitions: `laid`, `LinF.eval`, `LinF.fold`.
Main theorems: `onTable_vars`, `readE_onTable`, `sum_onTable`, `linEvalRow_inv`, `read_eval`,
`linFoldRow_inv`, `read_fold`.

What is asked: the vectors' index bits fit the tables (kCol, kRow, kLo + kRow at most the tables'
index bits).

Not claimed. Nothing on the rows of the drawn columns or on the row with written-out weights.
Nothing on a run of a block, and nothing on what a row means for sent messages.

-/
import OnBytes.Slice.BlkTensCut
import OnBytes.Slice.BlkLink
import OnBytes.Slice.BlkSendRead
import OnBytes.Iop.Lin

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb
open OnBytes.Params (LinShape)

/-! ## A vector's tensor on a table, at every index -/

/-- A tensor without a written-out factor, placed on a table: it has the table's index bits as its
variables, and no written-out factor. -/
theorem onTable_vars (l : VectorLay) (v : Tensor) (hv : v.denseVars = []) (hb : v.vars ≤ l.bits) :
    (l.onTable v).vars = l.bits ∧ (l.onTable v).denseVars = [] := by
  obtain ⟨_, hd, hp⟩ := onTable_plain_eq l v hv
  refine ⟨?_, hd⟩
  have hw : (v.insertChoice v.vars (l.bits - v.vars) 0).pairs.length = l.bits := by
    have := vars_insertChoice v v.vars (l.bits - v.vars) 0 (Nat.le_refl _)
    unfold Tensor.vars at this hb ⊢
    omega
  show (l.onTable v).pairs.length = l.bits
  rw [hp]
  split
  · rw [List.length_append, List.length_drop, List.length_take, hw]
    omega
  · exact hw

/-- **A vector's tensor, placed on a table, at any index**: the tensor's entry at the number of the
vector's entry that stands at the index modulo the table's size, and 0 where the tensor does not
reach. -/
theorem readE_onTable (l : VectorLay) (v : Tensor) (hv : v.denseVars = []) (hb : v.vars ≤ l.bits)
    (i : ℕ) :
    readE ((l.onTable v).entry i) =
      if l.entryAt (i % 2 ^ l.bits) < 2 ^ v.vars then readE (v.entry (l.entryAt (i % 2 ^ l.bits)))
      else 0 := by
  obtain ⟨h1, h2⟩ := onTable_vars l v hv hb
  have h3 := entry_mod rdE (l.onTable v) h2 i
  rw [h1] at h3
  exact h3.symm.trans (entry_onTable rdE l v hv hb _ (Nat.mod_lt _ (Nat.two_pow_pos _)))

/-- A function of the number of a vector's entry, as a function of the index in the table in which
the vector lies. -/
def laid (lay : VectorLay) (f : ℕ → GE) (i : ℕ) : GE := f (lay.entryAt (i % 2 ^ lay.bits))

/-- **Tensors of n variables on a vector, placed on a table and added up.** -/
theorem sum_onTable (lay : VectorLay) (n : ℕ) (l : List Tensor)
    (hl : ∀ w ∈ l, w.vars = n ∧ w.denseVars = []) (hb : n ≤ lay.bits) (i : ℕ) :
    (l.map fun t => readE ((lay.onTable t).entry i)).sum =
      laid lay (fun e => if e < 2 ^ n then (l.map fun t => readE (t.entry e)).sum else 0) i := by
  have e1 : (l.map fun t => readE ((lay.onTable t).entry i)) =
      l.map fun t => if lay.entryAt (i % 2 ^ lay.bits) < 2 ^ n then
        readE (t.entry (lay.entryAt (i % 2 ^ lay.bits))) else 0 :=
    List.map_congr_left fun t ht => by
      rw [readE_onTable lay t (hl t ht).2 (by rw [(hl t ht).1]; exact hb) i, (hl t ht).1]
  rw [e1]
  unfold laid
  by_cases h : lay.entryAt (i % 2 ^ lay.bits) < 2 ^ n
  · simp only [if_pos h]
  · simp only [if_neg h]
    simp

/-! ## The row that evaluates W -/

namespace LinF

/-- **The row that evaluates W at a point**: on the entries of W, which lies in the main table of
the oracle message w, the weights of the point psi; the coefficients of a form in mask entries; a
target. -/
def eval (lay : VectorLay) (w : ℕ) (psi : List GE) (masks : PscF.MaskForm) (target : GE) :
    RowF where
  coef o part i :=
    (RowF.ofMasks masks target).coef o part i +
      if w == o && Part.main == part then
        laid lay (fun e =>
          if e < 2 ^ psi.length then eqW psi.length (fun t => psi.getD t 0) e else 0) i
      else 0
  target := target

/-- **The row that ties Omega to the folded row.** Omega lies in the main table of the oracle
message omega and has mR entries; on them the row has the weights of the point zeta. The folded row
lies in that of u; on its entry j + 2 ^ kLo y, for y below mR, the row has the negative of the
weight of the point psiLo, zeta. The target is 0. -/
def fold (mR kLo : ℕ) (layO : VectorLay) (omega : ℕ) (layU : VectorLay) (u : ℕ)
    (psiLo zeta : List GE) : RowF where
  coef o part i :=
    (if omega == o && Part.main == part then
        laid layO (fun e => if e < mR then eqW zeta.length (fun t => zeta.getD t 0) e else 0) i
      else 0) +
      if u == o && Part.main == part then
        laid layU (fun e => if e / 2 ^ kLo < mR then
          -eqW (psiLo ++ zeta).length (fun t => (psiLo ++ zeta).getD t 0) e else 0) i
      else 0
  target := 0

end LinF

/-- What the program's row on W is made of. -/
theorem linEvalRow_inv (S : LinShape) (claim : LinClaim) (w : ℕ) (lay : VectorLay) (r : Row)
    (h : linEvalRow S claim w lay = some r) :
    claim.psi.length = S.kCol ∧
      r = addLaid { units := claim.masks, target := claim.target } w lay [Tensor.eq claim.psi] := by
  unfold linEvalRow at h
  by_cases hl : claim.psi.length = S.kCol
  · simp [hl] at h
    exact ⟨hl, h.symm⟩
  · simp [hl] at h

/-- The weights of a point, from the program's tensor. -/
theorem readE_eqList (z : List E) (s : E) (j : ℕ) :
    readE ((Tensor.eq z s).entry j) =
      readE s * eqW (z.map readE).length (fun t => (z.map readE).getD t 0) j := by
  rw [readE_eq, readL_eq_getD, List.length_map]

/-- **The program's row on W, for the claim made of a row on the matrix, read.** -/
theorem read_eval (S : LinShape) (row : TensorRow) (w : ℕ) (lay : VectorLay) (r : Row)
    (hb : S.kCol ≤ lay.bits) (h : linEvalRow S (memberClaim row) w lay = some r) :
    r.kind = .plain ∧
      readRow r = LinF.eval lay w (row.psi.map readE) (readForm row.masks) (readE row.target) := by
  obtain ⟨hl, rfl⟩ := linEvalRow_inv S _ w lay r h
  have hl' : row.psi.length = S.kCol := hl
  obtain ⟨ht, hk⟩ := addLaid_keeps w lay [Tensor.eq (memberClaim row).psi]
    { units := (memberClaim row).masks, target := (memberClaim row).target }
  refine ⟨hk, ?_⟩
  unfold readRow LinF.eval
  refine congrArg₂ RowF.mk (funext fun o => funext fun part => funext fun i => ?_)
    (congrArg readE ht)
  show coefAt _ o part i = _
  rw [coefAt_addLaid]
  refine congrArg₂ (· + ·) ?_ ?_
  · have e := congrArg (fun q : RowF => q.coef o part i)
      (readRow_addMasks row.masks row.target)
    rw [addMasks_eq] at e
    refine Eq.trans ?_ e
    show coefAt _ o part i = coefAt _ o part i
    refine congrArg (fun u => coefAt ({ units := u, target := row.target } : Row) o part i) ?_
    show (row.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray = _
    simp only [Array.empty_append]
    rfl
  · split
    · have hs := sum_onTable lay row.psi.length [Tensor.eq row.psi]
        (fun t ht => by
          obtain rfl := List.mem_singleton.1 ht
          exact ⟨vars_eqTensor _ _, rfl⟩) (by rw [hl']; exact hb) i
      refine hs.trans ?_
      unfold laid
      beta_reduce
      rw [List.length_map]
      split
      · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, readE_eqList,
          readE_one, one_mul, List.length_map]
      · rfl
    · rfl

/-! ## The row that ties Omega to the folded row -/

/-- What the program's row on Omega and the folded row is made of. -/
theorem linFoldRow_inv (S : LinShape) (psi zeta : List E) (u : FoldedRow) (omega : ℕ)
    (lay : VectorLay) (r : Row) (h : linFoldRow S psi zeta u omega lay = some r) :
    psi.length = S.kCol ∧ zeta.length = S.kRow ∧ ∃ onOmega onU,
      tensorBelow (Tensor.eq zeta) 0 S.kRow S.matrixRows = some onOmega ∧
      tensorBelow (Tensor.eq (psi.take S.kLo ++ zeta) (negE oneE)) S.kLo S.kRow S.matrixRows =
        some onU ∧
      r = u.addAll (addLaid {} omega lay onOmega) onU := by
  unfold linFoldRow at h
  by_cases hl : psi.length = S.kCol
  · by_cases hz : zeta.length = S.kRow
    · cases hp : tensorBelow (Tensor.eq zeta) 0 S.kRow S.matrixRows with
      | none => simp [hl, hz, hp] at h
      | some a =>
        cases hm : tensorBelow (Tensor.eq (psi.take S.kLo ++ zeta) (negE oneE)) S.kLo S.kRow
            S.matrixRows with
        | none => simp [hl, hz, hp, hm] at h
        | some b =>
          simp [hl, hz, hp, hm] at h
          exact ⟨hl, hz, a, b, rfl, rfl, h.symm⟩
    · simp [hl, hz] at h
  · simp [hl] at h

/-- A cut that is there: the tensor has the variables that are cut, and the length is at most the
number of their values. -/
theorem tensorBelow_some (v : Tensor) (hv : v.denseVars = []) (start count len : ℕ)
    (l : List Tensor) (h : tensorBelow v start count len = some l) :
    start + count ≤ v.vars ∧ len ≤ 2 ^ count := by
  rw [tensorBelow_plain_at v hv] at h
  by_contra hno
  rw [if_pos] at h
  · cases h
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega

/-- **The program's row on Omega and the folded row, read.** -/
theorem read_fold (S : LinShape) (psi zeta : List E) (u : FoldedRow) (omega : ℕ) (lay : VectorLay)
    (r : Row) (hbO : S.kRow ≤ lay.bits) (hbU : S.kLo + S.kRow ≤ u.lay.bits)
    (h : linFoldRow S psi zeta u omega lay = some r) :
    r.kind = .plain ∧
      readRow r = LinF.fold S.matrixRows S.kLo lay omega u.lay u.oracle
        ((psi.take S.kLo).map readE) (zeta.map readE) := by
  obtain ⟨_, hz, onOmega, onU, hO, hU, rfl⟩ := linFoldRow_inv S psi zeta u omega lay r h
  obtain ⟨_, hmR⟩ := tensorBelow_some _ rfl _ _ _ _ hO
  obtain ⟨hvU, _⟩ := tensorBelow_some _ rfl _ _ _ _ hU
  have hvarsO : (Tensor.eq zeta).vars = S.kRow := (vars_eqTensor _ _).trans hz
  have hvarsU : (Tensor.eq (psi.take S.kLo ++ zeta) (negE oneE)).vars = S.kLo + S.kRow := by
    rw [vars_eqTensor] at hvU ⊢
    rw [List.length_append, List.length_take, hz] at hvU ⊢
    omega
  obtain ⟨t1, k1⟩ := addLaid_keeps omega lay onOmega {}
  obtain ⟨t2, k2⟩ := addLaid_keeps u.oracle u.lay onU (addLaid {} omega lay onOmega)
  refine ⟨k2.trans k1, ?_⟩
  unfold readRow LinF.fold
  refine congrArg₂ RowF.mk (funext fun o => funext fun part => funext fun i => ?_)
    ((congrArg readE (t2.trans t1)).trans readE_zero)
  show coefAt (addLaid (addLaid {} omega lay onOmega) u.oracle u.lay onU) o part i = _
  rw [coefAt_addLaid, coefAt_addLaid, coefAt_empty, zero_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · split
    · rw [sum_onTable lay S.kRow onOmega
        (fun w hw => by
          obtain ⟨a, b⟩ := tensorBelow_shape _ rfl _ _ _ hO w hw
          exact ⟨a.trans hvarsO, b⟩) hbO i]
      unfold laid
      beta_reduce
      have hsum : (onOmega.map fun t => readE (t.entry (lay.entryAt (i % 2 ^ lay.bits)))).sum = _ :=
        sum_tensorBelow rdE _ rfl _ _ _ hO (lay.entryAt (i % 2 ^ lay.bits))
      rw [hsum]
      by_cases he : lay.entryAt (i % 2 ^ lay.bits) < 2 ^ S.kRow
      · rw [if_pos he, Nat.mod_eq_of_lt he]
        split
        · show readE _ = _
          rw [readE_eqList, readE_one, one_mul]
        · rfl
      · rw [if_neg he, if_neg (by omega)]
    · rfl
  · split
    · rw [sum_onTable u.lay (S.kLo + S.kRow) onU
        (fun w hw => by
          obtain ⟨a, b⟩ := tensorBelow_shape_at _ rfl _ _ _ _ hU w hw
          exact ⟨a.trans hvarsU, b⟩) hbU i]
      unfold laid
      beta_reduce
      have hsum : (onU.map fun t => readE (t.entry (u.lay.entryAt (i % 2 ^ u.lay.bits)))).sum = _ :=
        sum_tensorBelow_at rdE _ rfl _ _ _ _ hU (u.lay.entryAt (i % 2 ^ u.lay.bits))
      rw [hsum]
      by_cases he : u.lay.entryAt (i % 2 ^ u.lay.bits) < 2 ^ (S.kLo + S.kRow)
      · have hq : u.lay.entryAt (i % 2 ^ u.lay.bits) / 2 ^ S.kLo < 2 ^ S.kRow := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
          exact he
        rw [if_pos he, Nat.mod_eq_of_lt hq]
        split
        · show readE _ = _
          rw [readE_eqList, readE_neg, readE_one, List.map_append]
          ring
        · rfl
      · rw [if_neg he, if_neg]
        intro hlt
        apply he
        have h1 : u.lay.entryAt (i % 2 ^ u.lay.bits) / 2 ^ S.kLo < 2 ^ S.kRow :=
          lt_of_lt_of_le hlt hmR
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm] at h1
        exact h1
    · rfl

end OnBytes.Slice
