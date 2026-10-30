-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsSem.lean: the row that the program's code switch hands on, read in the field, is
the claim after the library's code switch.

The program's code switch ends with a batching. The old claim on the new tables, the new oracle
message's sample row and, for each drawn position, three rows of generator matrices become one row
on the new group, under the powers of one drawn element. OnBytes/Slice/BlkCsRows.lean reads each of
these rows in the field, except the sample row. This file adds them up and compares the sum with
`csNext` (OnBytes/Slice/CsSim.lean), the claim after the library's code switch with its form written
as a vector.

The course. The program's claim and its sample row are written into the format's records (`sRowOf`,
`gRowOf`). On both new tables the program's batched row then has the entries of the row that the
format's own code switch computes from these records (`rows_main`, `rows_mask`, by the closed
forms of OnBytes/Slice/SimCs.lean). What that row is at each place of the library's layout is known
(`cs_at`, OnBytes/Slice/CsAt.lean).

What is taken as given: that the batched row is the sum of the rows (`Batched`, `BatchedAt`); that
the frame of the switch is as OnBytes/Slice/BlkCsRows.lean asks, with the old stage's codes; that
the sample row has the coefficients of the library's sample; that the symbols read are the long
symbols of a word.

Main definitions: `Batched`, `BatchedAt`, `sRowOf`, `gRowOf`, `fmtRow`, `csRowsB`.
Main theorems: `hornerSum_draws`, `rows_main`, `rows_mask`; `cs_rows_vec`, `cs_rows_target` (on the
sums of the rows, whatever the layout of the new group); `batchedAt_of_index`,
`cs_batchedAt_sem` (on the batched row, read with the new group's own row bits), `cs_batched_sem`
(if these are the stage's).

Not claimed. Nothing on the run of the block. Nothing on a group with more than one member.
-/
import OnBytes.Iop.RowLaws
import OnBytes.Slice.BlkCsRows
import OnBytes.Slice.CsSim
import OnBytes.Slice.SimLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open Fmt.M1 (SRow GRow Col sumRows)

variable {s s' : Sg}

/-! ## A batched row -/

/-- A row on a group is the sum of rows on its one member g under the powers of θ: entry by
entry on the first nM entries of the main table and the first nD of the mask table, and in the
target. -/
structure Batched (row : GroupRow) (rows : List Row) (g : ℕ) (θ : GE) (nM nD : ℕ) : Prop where
  main : ∀ J, J < nM → formAt row.c J = hornerSum θ (rows.map fun r => coefAt r g .main J)
  mask : ∀ J, J < nD → readV row.d J = hornerSum θ (rows.map fun r => coefAt r g .mask J)
  target : readE row.target = hornerSum θ (rows.map fun r => readE r.target)

/-- The two ways to write a sum under the powers of θ from the inside out are one. -/
theorem hornerSum_eq (θ : GE) : ∀ l : List GE, hornerSum θ l = horner θ l
  | [] => rfl
  | a :: l => congrArg (fun t => a + θ * t) (hornerSum_eq θ l)

/-- The sum under the powers of θ of two entries and three for each draw, sorted by draws. -/
theorem hornerSum_draws (θ a b : GE) (xs : List ℕ) (A B C : ℕ → GE) :
    hornerSum θ (a :: b :: xs.flatMap fun x => [A x, B x, C x])
      = a + θ * b + ∑ i ∈ Finset.range xs.length,
          θ ^ (2 + 3 * i) * (A (xs.getD i 0) + θ * B (xs.getD i 0) + θ ^ 2 * C (xs.getD i 0)) := by
  have e : ∑ i ∈ Finset.range xs.length,
        θ ^ (2 + 3 * i) * (A (xs.getD i 0) + θ * B (xs.getD i 0) + θ ^ 2 * C (xs.getD i 0))
      = θ ^ 2 * horner θ (xs.flatMap fun x => [A x, B x, C x]) := by
    rw [horner_draws, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, hornerSum_eq]
  show a + θ * (b + θ * horner θ (xs.flatMap fun x => [A x, B x, C x])) = _
  ring

/-- A reading of all rows of a switch, if it is known on the three rows of each draw. -/
theorem map_rows (F : Row → GE) (a b : Row) (xs : List ℕ) (G : ℕ → List Row) (A B C : ℕ → GE)
    (h : ∀ x ∈ xs, (G x).map F = [A x, B x, C x]) :
    (a :: b :: xs.flatMap G).map F = F a :: F b :: xs.flatMap fun x => [A x, B x, C x] := by
  rw [List.map_cons, List.map_cons, List.map_flatMap]
  refine congrArg (fun l => F a :: F b :: l) ?_
  rw [List.flatMap_def, List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left h)

/-! ## The program's data in the format's records -/

/-- An array that is made from a function on the numbers below n reads as that function, cut at
n. -/
theorem vec_ofFn_cut (n : ℕ) (F : ℕ → Fmt.M1.E) :
    vec (Array.ofFn (n := n) fun j => F j.val) = cut n fun j => toE (F j) := by
  funext i
  rw [vec_ofFn]
  by_cases h : i < n
  · rw [dif_pos h, cut_of_lt h]
  · rw [dif_neg h, cut_of_le (by omega)]

/-- The program's claim on three folded rows, in the format's record: the first n coefficients on
the main row's message, written out, and the rest as it is. -/
def sRowOf (n : ℕ) (old : SingleRows) : SRow :=
  ⟨Array.ofFn (n := n) fun j => (old.c.entry j.val).triple, (old.d.getD 0 #[]).map E.triple,
    (old.d.getD 1 #[]).map E.triple, old.target.triple, old.gamma.map E.triple⟩

/-- A row of the program on the oracle message g, in the format's record: its first nM coefficients
on the main table and its first nD on the mask table, written out. -/
def gRowOf (nM nD : ℕ) (r : Row) (g : ℕ) : GRow :=
  ⟨Array.ofFn (n := nM) fun j => (r.coefficient g .main j.val).triple,
    Array.ofFn (n := nD) fun j => (r.coefficient g .mask j.val).triple, r.target.triple⟩

/-- The translated claim's coefficients on the main row's message. -/
theorem vec_sRowOf_c (n : ℕ) (old : SingleRows) :
    vec (sRowOf n old).c = cut n (formAt old.c) :=
  vec_ofFn_cut n fun j => (old.c.entry j).triple

/-- The translated claim's coefficients on the carried mask row's message. -/
theorem vec_sRowOf_d0 (n : ℕ) (old : SingleRows) :
    vec (sRowOf n old).d0 = readV (old.d.getD 0 #[]) :=
  funext fun i => (readV_eq_vec _ i).symm

/-- The translated claim's coefficients on the fresh mask row's message. -/
theorem vec_sRowOf_d1 (n : ℕ) (old : SingleRows) :
    vec (sRowOf n old).d1 = readV (old.d.getD 1 #[]) :=
  funext fun i => (readV_eq_vec _ i).symm

/-- The translated row's coefficients on the main table. -/
theorem vec_gRowOf_c (nM nD : ℕ) (r : Row) (g : ℕ) :
    vec (gRowOf nM nD r g).c = cut nM (coefAt r g .main) :=
  vec_ofFn_cut nM fun j => (r.coefficient g .main j).triple

/-- The translated row's coefficients on the mask table. -/
theorem vec_gRowOf_d (nM nD : ℕ) (r : Row) (g : ℕ) :
    vec (gRowOf nM nD r g).d = cut nD (coefAt r g .mask) :=
  vec_ofFn_cut nD fun j => (r.coefficient g .mask j).triple

/-- The translated claim has the program's claim's vector. -/
theorem vecMid_sRowOf (s : Sg) (old : SingleRows) : vecMid s (sRowOf s.C.l old) = vecS s old := by
  funext j
  rcases j with j | j | j
  · show vec (sRowOf s.C.l old).c j.val = formAt old.c j.val
    rw [vec_sRowOf_c, cut_of_lt j.isLt]
  · exact congrFun (vec_sRowOf_d0 s.C.l old) j.val
  · exact congrFun (vec_sRowOf_d1 s.C.l old) j.val

/-- The coefficients of the program's row on a group are its entries at the indices of the
tables. -/
theorem vecG_eq (s' : Sg) (G : GroupRow) (j : s'.cIn.J) : vecG s' G j = groupOn G (outAt s' j) := by
  rcases j with x | x <;> rfl

/-- Cutting twice at one length is cutting once. -/
theorem cut_cut (n : ℕ) (F : ℕ → GE) : cut n (cut n F) = cut n F := by
  funext j
  by_cases h : j < n
  · rw [cut_of_lt h]
  · rw [cut_of_le (by omega), cut_of_le (by omega)]

/-! ## The program's new row is the format's new row at the translated data -/

/-- The format's new row, at the program's claim, sample row, draws and element. The columns col
bear on its target alone. -/
def fmtRow (s s' : Sg) (old : SingleRows) (sample : Row) (g : ℕ) (xs : List ℕ) (theta : E)
    (col : ℕ → Col) : GRow :=
  sumRows .two theta.triple (allRows .two s.st s'.st (sRowOf s.C.l old)
    (gRowOf (2 ^ (s'.h + s'.g) * s'.C.l) (2 ^ s'.h * s'.Z.l) sample g) xs col)

/-- All rows of a switch into a stage, as the batching takes them: first the old claim on the new
tables, then the new oracle message's sample row, then each draw's three rows of generator
matrices, which have the targets t0, t1, t2. -/
def csRowsB (W : SwitchFrame) (old : SingleRows) (sample : Row) (xs : List ℕ) (t0 t1 t2 : ℕ → E) :
    List Row :=
  carriedRow W old :: sample :: xs.flatMap fun x =>
    [genMain W x (t0 x), genMask W x 0 (t1 x), genMask W x 1 (t2 x)]

section
variable {W : SwitchFrame} (hW : FrameOK W) (hC : codeOf W.code = s.C) (hZ : codeOf W.zk = s.Z)
  (old : SingleRows) (hd0 : (old.d.getD 0 #[]).size = W.zk.ell)
  (hd1 : (old.d.getD 1 #[]).size = W.zk.ell) (sample : Row) (xs : List ℕ)
  (hx : ∀ x ∈ xs, x < 2 ^ W.code.logN) (t0 t1 t2 : ℕ → E) (theta : E)
include hW hC hd0 hd1 hx

/-- The sum of the rows' coefficients on an entry of the new main table is the entry of the format's
new row (`fmtRow`). -/
theorem rows_main (hc : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (htb : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ W.tableBits) (col : ℕ → Col) (J : ℕ)
    (hJ : J < 2 ^ (s'.h + s'.g) * s'.C.l) :
    hornerSum (readE theta)
        ((csRowsB W old sample xs t0 t1 t2).map fun r => coefAt r W.g .main J)
      = vec (fmtRow s s' old sample W.g xs theta col).c J := by
  have hJ' : J < 2 ^ W.tableBits := Nat.lt_of_lt_of_le hJ htb
  have hl : W.code.ell = s.C.l := congrArg Fmt.M1.Code.l hC
  unfold csRowsB
  rw [map_rows _ _ _ xs _ (fun x => wM (codeOf W.code) x J) (fun _ => 0)
    (fun _ => 0) (fun x hx' => gen_main hW x _ _ _ (hx x hx') J hJ'), hornerSum_draws,
    carried_main hW old hd0 hd1 hc J hJ', hC, hl]
  unfold fmtRow
  rw [vec_cs_c]
  show _ = cut (2 ^ (s'.h + s'.g) * s'.C.l) (fun j =>
    cut s.C.l (vec (sRowOf s.C.l old).c) j + toE theta.triple * vec (gRowOf _ _ sample W.g).c j
      + ∑ i ∈ Finset.range xs.length, toE theta.triple ^ (2 + 3 * i) * wM s.C (xs.getD i 0) j) J
  rw [cut_of_lt hJ, vec_sRowOf_c, cut_cut, vec_gRowOf_c, cut_of_lt hJ, ← readE_def]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

include hZ in
/-- The sum of the rows' coefficients on an entry of the new mask table is the entry of the format's
new row (`fmtRow`). -/
theorem rows_mask (hrb : 2 ^ s'.h * s'.Z.l ≤ 2 ^ W.restBits) (col : ℕ → Col) (J : ℕ)
    (hJ : J < 2 ^ s'.h * s'.Z.l) :
    hornerSum (readE theta)
        ((csRowsB W old sample xs t0 t1 t2).map fun r => coefAt r W.g .mask J)
      = vec (fmtRow s s' old sample W.g xs theta col).d J := by
  have hJ' : J < 2 ^ W.restBits := Nat.lt_of_lt_of_le hJ hrb
  have e1 : W.zk.ell = s.Z.l := congrArg Fmt.M1.Code.l hZ
  have e2 : W.code.r = s.C.r := congrArg Fmt.M1.Code.r hC
  have e3 : W.zk.r = s.Z.r := congrArg Fmt.M1.Code.r hZ
  unfold csRowsB
  rw [map_rows _ _ _ xs _ _ _ _
    (fun x hx' => gen_mask hW x _ _ _ (hx x hx') J hJ'), hornerSum_draws,
    carried_mask hW old hd0 hd1 J, hC, hZ, e1, e2, e3]
  unfold fmtRow
  rw [vec_cs_d]
  show _ = cut (2 ^ s'.h * s'.Z.l) (fun j =>
    cut s.Z.l (vec (sRowOf s.C.l old).d0) j + moved s.Z.l (cut s.Z.l (vec (sRowOf s.C.l old).d1)) j
      + toE theta.triple * vec (gRowOf _ _ sample W.g).d j
      + ∑ i ∈ Finset.range xs.length, toE theta.triple ^ (2 + 3 * i) *
          (moved (2 * s.Z.l) (wT s.C (xs.getD i 0)) j
          + toE theta.triple * (wM s.Z (Fmt.M1.cp s.Z (xs.getD i 0)) j
            + moved (2 * s.Z.l + s.C.r) (wT s.Z (Fmt.M1.cp s.Z (xs.getD i 0))) j)
          + toE theta.triple ^ 2 * (moved s.Z.l (wM s.Z (Fmt.M1.cp s.Z (xs.getD i 0))) j
            + moved (2 * s.Z.l + s.C.r + s.Z.r) (wT s.Z (Fmt.M1.cp s.Z (xs.getD i 0))) j))) J
  rw [cut_of_lt hJ, vec_sRowOf_d0, vec_sRowOf_d1, vec_gRowOf_d, cut_of_lt hJ, ← readE_def]

end

/-! ## From a batched row to the claim after the library's switch -/

/-- The translated sample row has the program's sample row's coefficients, on the new tables. -/
theorem tabAt_gRowOf (s' : Sg) (r : Row) (g : ℕ) (j : s'.cIn.J) :
    tabAt (gRowOf (2 ^ (s'.h + s'.g) * s'.C.l) (2 ^ s'.h * s'.Z.l) r g) (outAt s' j)
      = rowOn r g (outAt s' j) := by
  rcases j with x | x
  · show vec (gRowOf _ _ r g).c (idxOf x) = coefAt r g .main (idxOf x)
    rw [vec_gRowOf_c, cut_of_lt (idxOf_lt x)]
  · show vec (gRowOf _ _ r g).d (idxOf x) = coefAt r g .mask (idxOf x)
    rw [vec_gRowOf_d, cut_of_lt (idxOf_lt x)]

/-- The sum of the rows of the program's code switch, under the powers of theta, is the vector of
the claim after the library's switch, at each entry of the new tables. W: the frame of the
switch, with the codes of the old stage s. old: the program's claim on the three folded rows.
sample: the sample row of the new oracle message. xs: the drawn positions. ρo: the seed as the
library reads it. hsmp: the sample row has the coefficients of the library's sample at ρo. The
target τ₀, the word y and the answer ans do not bear on the vector. -/
theorem cs_rows_vec (hf : CsFit s s') {W : SwitchFrame} (hW : FrameOK W)
    (hC : codeOf W.code = s.C) (hZ : codeOf W.zk = s.Z) (old : SingleRows)
    (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
    (hc : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (htb : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ W.tableBits)
    (hrb : 2 ^ s'.h * s'.Z.l ≤ 2 ^ W.restBits) (sample : Row) (xs : List ℕ)
    (hxs : xs.length = s.t) (hx : ∀ x ∈ xs, x < 2 ^ W.code.logN) (t0 t1 t2 : ℕ → E)
    (theta : E) (ρo : (Fin s'.st.na → GE) × GEˣ)
    (hsmp : ∀ n, rowOn sample W.g (outAt s' (csPlace hf n)) = (csSample hf).mat ρo () n)
    (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = xs.getD i.val 0) (τ₀ ans : GE)
    (y : s.cMid.Word) (j : s'.cIn.J) :
    hornerSum (readE theta)
        ((csRowsB W old sample xs t0 t1 t2).map fun r => rowOn r W.g (outAt s' j))
      = (csNext hf τ₀ (vecS s old) y ρo ans (Qs, readE theta)).2 j := by
  obtain ⟨n, rfl⟩ := (csPlace hf).surjective j
  have hrow : hornerSum (readE theta) ((csRowsB W old sample xs t0 t1 t2).map fun r =>
        rowOn r W.g (outAt s' (csPlace hf n)))
      = tabAt (fmtRow s s' old sample W.g xs theta fun _ => default)
          (outAt s' (csPlace hf n)) := by
    rcases csPlace hf n with x | x
    · exact rows_main hW hC old hd0 hd1 sample xs hx t0 t1 t2 theta hc htb _ _ (idxOf_lt x)
    · exact rows_mask hW hC hZ old hd0 hd1 sample xs hx t0 t1 t2 theta hrb _ _ (idxOf_lt x)
  rw [hrow, csNext_snd]
  unfold fmtRow
  rw [cs_at hf _ _ xs theta.triple _ n, vecMid_sRowOf, tabAt_gRowOf, hsmp, hxs, Finset.sum_range,
    ← readE_def]
  simp only [hQ]

/-- The sum of the rows' targets is the target of the claim after the library's switch. y: a
word whose long symbols at the drawn positions are the symbols read. -/
theorem cs_rows_target (hf : CsFit s s') (W : SwitchFrame) (old : SingleRows) (sample : Row)
    (xs : List ℕ) (hxs : xs.length = s.t) (t0 t1 t2 : ℕ → E) (theta : E)
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (hans : readE sample.target = ans)
    (y : s.cMid.Word) (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = xs.getD i.val 0)
    (hy0 : ∀ i, s.cMid.T y (Qs i) (.inl ()) = readE (t0 (Qs i).val))
    (hy1 : ∀ i, s.cMid.T y (Qs i) (.inr (.inl ())) = readE (t1 (Qs i).val))
    (hy2 : ∀ i, s.cMid.T y (Qs i) (.inr (.inr ())) = readE (t2 (Qs i).val))
    (v : s.cMid.J → GE) :
    hornerSum (readE theta) ((csRowsB W old sample xs t0 t1 t2).map fun r => readE r.target)
      = (csNext hf (readE old.target) v y ρo ans (Qs, readE theta)).1 := by
  unfold csRowsB
  rw [map_rows _ _ _ xs _ (fun x => readE (t0 x)) (fun x => readE (t1 x))
    (fun x => readE (t2 x)) (fun x _ => gen_target x _ _ _), hornerSum_draws, csNext_fst, hxs,
    Finset.sum_range, target_carriedRow, hans]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  show _ = readE theta ^ (2 + 3 * i.val) * (s.cMid.T y (Qs i) _
    + readE theta * s.cMid.T y (Qs i) _ + readE theta ^ 2 * s.cMid.T y (Qs i) _)
  rw [hy0, hy1, hy2, hQ]

/-- A row on a group with 2^k main rows and 2^h mask rows is the sum of rows on its member g under
the powers of θ: at each entry of the stage s', the group's index on the left and the member's on
the right, and in the target. -/
structure BatchedAt (s' : Sg) (k h : ℕ) (row : GroupRow) (rows : List Row) (g : ℕ) (θ : GE) :
    Prop where
  vec : ∀ j : s'.cIn.J,
    vecGk s' k h row j = hornerSum θ (rows.map fun r => rowOn r g (outAt s' j))
  target : readE row.target = hornerSum θ (rows.map fun r => readE r.target)

/-- From the place to which the group's layout carries an entry of its member to the entries of the
stage: if the member's blocks begin at row 0 of the group's tables and have the stage's numbers of
rows, a row that is the sum of the rows at each such place is so in the sense of `BatchedAt`. -/
theorem batchedAt_of_index (s' : Sg) (k h : ℕ) (row : GroupRow) (rows : List Row) (g : ℕ) (θ : GE)
    (hmain : ∀ idx, idx < 2 ^ (s'.h + s'.g) * s'.C.l →
      formAt row.c (groupIndex idx (s'.h + s'.g) 0 k)
        = hornerSum θ (rows.map fun r => coefAt r g .main idx))
    (hmask : ∀ idx, idx < 2 ^ s'.h * s'.Z.l → readV row.d (groupIndex idx s'.h 0 h)
      = hornerSum θ (rows.map fun r => coefAt r g .mask idx))
    (ht : readE row.target = hornerSum θ (rows.map fun r => readE r.target)) :
    BatchedAt s' k h row rows g θ where
  vec := fun j => by
    rcases j with e | e
    · show formAt row.c (Sz.rowNo e.1 + 2 ^ k * e.2.val)
        = hornerSum θ (rows.map fun r => coefAt r g .main (idxOf e))
      rw [← hmain (idxOf e) (idxOf_lt e)]
      unfold idxOf
      rw [groupIndex_closed _ _ _ _ _ (rowNo_lt e.1), Nat.zero_add]
    · show readV row.d (Sz.rowNo e.1 + 2 ^ h * e.2.val)
        = hornerSum θ (rows.map fun r => coefAt r g .mask (idxOf e))
      rw [← hmask (idxOf e) (idxOf_lt e)]
      unfold idxOf
      rw [groupIndex_closed _ _ _ _ _ (rowNo_lt e.1), Nat.zero_add]
  target := ht

/-- The row that the program's code switch hands on, read with the new group's own row bits, is the
claim after the library's switch. row: the batched row. k, h: the row bits of the new
group's two tables. The other parameters as in `cs_rows_vec` and `cs_rows_target`. -/
theorem cs_batchedAt_sem (hf : CsFit s s') {W : SwitchFrame} (hW : FrameOK W)
    (hC : codeOf W.code = s.C) (hZ : codeOf W.zk = s.Z) (old : SingleRows)
    (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
    (hc : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (htb : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ W.tableBits)
    (hrb : 2 ^ s'.h * s'.Z.l ≤ 2 ^ W.restBits) (sample : Row) (xs : List ℕ)
    (hxs : xs.length = s.t) (hx : ∀ x ∈ xs, x < 2 ^ W.code.logN) (t0 t1 t2 : ℕ → E)
    (row : GroupRow) (theta : E) (k h : ℕ)
    (hB : BatchedAt s' k h row (csRowsB W old sample xs t0 t1 t2) W.g (readE theta))
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (hans : readE sample.target = ans)
    (hsmp : ∀ n, rowOn sample W.g (outAt s' (csPlace hf n)) = (csSample hf).mat ρo () n)
    (y : s.cMid.Word) (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = xs.getD i.val 0)
    (hy0 : ∀ i, s.cMid.T y (Qs i) (.inl ()) = readE (t0 (Qs i).val))
    (hy1 : ∀ i, s.cMid.T y (Qs i) (.inr (.inl ())) = readE (t1 (Qs i).val))
    (hy2 : ∀ i, s.cMid.T y (Qs i) (.inr (.inr ())) = readE (t2 (Qs i).val)) :
    stmGk s' k h row = csNext hf (readE old.target) (vecS s old) y ρo ans (Qs, readE theta) :=
  Prod.ext
    (hB.target.trans (cs_rows_target hf W old sample xs hxs t0 t1 t2 theta ρo ans hans y Qs hQ
      hy0 hy1 hy2 _))
    (funext fun j => (hB.vec j).trans (cs_rows_vec hf hW hC hZ old hd0 hd1 hc htb hrb sample xs hxs
      hx t0 t1 t2 theta ρo hsmp Qs hQ _ ans y j))

/-- The same, if the new group's tables are the new oracle message's own. -/
theorem cs_batched_sem (hf : CsFit s s') {W : SwitchFrame} (hW : FrameOK W)
    (hC : codeOf W.code = s.C) (hZ : codeOf W.zk = s.Z) (old : SingleRows)
    (hd0 : (old.d.getD 0 #[]).size = W.zk.ell) (hd1 : (old.d.getD 1 #[]).size = W.zk.ell)
    (hc : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (htb : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ W.tableBits)
    (hrb : 2 ^ s'.h * s'.Z.l ≤ 2 ^ W.restBits) (sample : Row) (xs : List ℕ)
    (hxs : xs.length = s.t) (hx : ∀ x ∈ xs, x < 2 ^ W.code.logN) (t0 t1 t2 : ℕ → E)
    (row : GroupRow) (theta : E)
    (hB : Batched row (carriedRow W old :: sample :: xs.flatMap fun x =>
      [genMain W x (t0 x), genMask W x 0 (t1 x), genMask W x 1 (t2 x)]) W.g (readE theta)
      (2 ^ (s'.h + s'.g) * s'.C.l) (2 ^ s'.h * s'.Z.l))
    (ρo : (Fin s'.st.na → GE) × GEˣ) (ans : GE) (hans : readE sample.target = ans)
    (hsmp : ∀ n, rowOn sample W.g (outAt s' (csPlace hf n)) = (csSample hf).mat ρo () n)
    (y : s.cMid.Word) (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = xs.getD i.val 0)
    (hy0 : ∀ i, s.cMid.T y (Qs i) (.inl ()) = readE (t0 (Qs i).val))
    (hy1 : ∀ i, s.cMid.T y (Qs i) (.inr (.inl ())) = readE (t1 (Qs i).val))
    (hy2 : ∀ i, s.cMid.T y (Qs i) (.inr (.inr ())) = readE (t2 (Qs i).val)) :
    stmG s' row = csNext hf (readE old.target) (vecS s old) y ρo ans (Qs, readE theta) := by
  refine Prod.ext ?_ (funext fun j => ?_)
  · exact hB.target.trans (cs_rows_target hf W old sample xs hxs t0 t1 t2 theta ρo ans hans y Qs hQ
      hy0 hy1 hy2 _)
  · refine Eq.trans ?_ (cs_rows_vec hf hW hC hZ old hd0 hd1 hc htb hrb sample xs hxs hx t0 t1 t2
      theta ρo hsmp Qs hQ _ ans y j)
    show vecG s' row j = _
    rw [vecG_eq]
    rcases j with x | x
    · exact hB.main _ (idxOf_lt x)
    · exact hB.mask _ (idxOf_lt x)

end OnBytes.Slice

#print axioms OnBytes.Slice.hornerSum_eq
#print axioms OnBytes.Slice.hornerSum_draws
#print axioms OnBytes.Slice.map_rows
#print axioms OnBytes.Slice.vec_ofFn_cut
#print axioms OnBytes.Slice.vec_sRowOf_c
#print axioms OnBytes.Slice.vec_sRowOf_d0
#print axioms OnBytes.Slice.vec_sRowOf_d1
#print axioms OnBytes.Slice.vec_gRowOf_c
#print axioms OnBytes.Slice.vec_gRowOf_d
#print axioms OnBytes.Slice.vecMid_sRowOf
#print axioms OnBytes.Slice.vecG_eq
#print axioms OnBytes.Slice.cut_cut
#print axioms OnBytes.Slice.rows_main
#print axioms OnBytes.Slice.rows_mask
#print axioms OnBytes.Slice.tabAt_gRowOf
#print axioms OnBytes.Slice.cs_rows_vec
#print axioms OnBytes.Slice.cs_rows_target
#print axioms OnBytes.Slice.batchedAt_of_index
#print axioms OnBytes.Slice.cs_batchedAt_sem
#print axioms OnBytes.Slice.cs_batched_sem
