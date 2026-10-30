-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxFold.lean: the program's fold, read in the field, for a row whose form may have
a written-out factor; and a fold that receives its own mask.

OnBytes/Slice/BlkFoldSem.lean reads a run of the program's fold in the field for a row whose form
has no written-out factor (PlainForm). In a key's third chain a row has such a factor, and a fold
fixes row variables alone, so the factor stays from stage to stage. The law on fixing variables
holds of every form that passes Form.fits (OnBytes/Iop/FixLaws.lean: Form.fixLow_val_of_fits), and
the program's fold makes that test itself (foldRowOk). This file restates the reading from that
test, so that nothing has to be known of the row's form beforehand.

Main theorems.
  eqVal_eqW            the program's weight of a row at a point, read in the field.
  formAt_fixLow_fits   a form that fits, with its low variables fixed, in the terms of the library's
                       fold.
  fixLaw_of_fits       the law that the joint before the base case asks (FixLaw).
  vecS_foldOutput_fits the three vectors that the program's fold hands on.
  foldOutput_fit       what is public of the claim after a fold in which nothing is kept.
  fold_sem             a run of the program's fold on the view of a fold's written rounds.
  foldShapeOk_mono     the fold's test of the shape still holds after oracle messages were added.
  foldVerify_none      a fold that receives its mask is the receiving, then a fold whose mask has
                       come.

Not claimed. Nothing on soundness. That the form after a fold passes Form.fits: only the number of
variables of its tensors is shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Iop.FixLaws
import OnBytes.Slice.BaseLast
import OnBytes.Slice.BlkFoldOut
import OnBytes.Slice.BlkFoldSem
import OnBytes.Slice.BlkSendRun

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb _root_.Run

/-! ## Fixing the low variables of a form that fits -/

/-- A sum over a list of the first numbers, as a sum over a finite set. -/
theorem sum_list_range (F : ℕ → GE) : ∀ n : ℕ,
    ((List.range n).map F).sum = ∑ b ∈ Finset.range n, F b
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_list_range F n,
      Finset.sum_range_succ]
    simp

/-- The program's weight of the row number b at the point g, read in the field. -/
theorem eqVal_eqW : ∀ (g : List E) (b : ℕ), eqVal rdE g b = eqW g.length (readL g) b
  | [], b => (eqW_zero _ _).symm
  | x :: g, b => by
    rw [eqVal_cons, eqVal_eqW g (b / 2), List.length_cons, eqW_succ', Nat.testBit_zero]
    have e : (fun t => readL (x :: g) (t + 1)) = readL g := funext fun _ => rfl
    rw [e]
    congr 1
    by_cases h : b % 2 = 1 <;> simp [h] <;> rfl

/-- The tensors of a form that fits have the given number of variables and are in order. -/
theorem fits_tensors (f : Form) (n : ℕ) (h : f.fits n = true) :
    ∀ v ∈ f.tensors, v.vars = n ∧ v.InOrder := by
  intro v hv
  unfold Form.fits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨e1, e2⟩ := h.1 v hv
  exact ⟨e1, v.inOrder_of_ok e2⟩

/-- A form that fits, with its low variables fixed, as a sum over the numbers below 2^k. -/
theorem formAt_fixLow_range_fits (f : Form) (n : ℕ) (hf : f.fits n = true) (g : List E)
    (hg : g.length ≤ n) (times : E) (p : ℕ) :
    formAt (f.fixLow g times) p =
      (∑ b ∈ Finset.range (2 ^ g.length),
        eqW g.length (readL g) b * formAt f (b + 2 ^ g.length * p)) * readE times := by
  have h := Form.fixLow_val_of_fits rdE f n hf g hg times p
  unfold lowSum at h
  rw [sum_list_range] at h
  refine h.trans ?_
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [eqVal_eqW]; rfl

/-- A form that fits, with its low variables fixed, in the terms of the library's fold: for entry p,
each row β gives the entry (β, p) times the weight of β at the point; these are added, and the total
is multiplied by the factor. -/
theorem formAt_fixLow_fits (f : Form) (n : ℕ) (hf : f.fits n = true) (k : ℕ) (g : List E)
    (hg : g.length = k) (hk : k ≤ n) (times : E) (p : ℕ) :
    formAt (f.fixLow g times) p =
      (∑ β : Fin k → Bool, formAt f (Sz.rowNo β + 2 ^ k * p)
        * Alg.eqk (readP k g) β) * readE times := by
  subst hg
  rw [formAt_fixLow_range_fits f n hf g hk times p, sum_range_cube]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [eqW_rowNo, mul_comm]
  rfl

/-- The law that the joint before the base case asks, of a form that fits. -/
theorem fixLaw_of_fits (f : Form) (n : ℕ) (hf : f.fits n = true) (g : List E)
    (hg : g.length ≤ n) : FixLaw f g := fun p => formAt_fixLow_range_fits f n hf g hg oneE p

/-! ## What the program's fold hands on -/

/-- The program's test of a row's sizes says that the row's form fits. -/
theorem fits_of_foldRowOk (S : Statement) (F : FoldShape) (row : GroupRow)
    (h : foldRowOk S F row = true) :
    row.c.fits (F.layout.k + ceilLog2 (S.codes.base.getD F.code default).ell) = true := by
  unfold foldRowOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- The coefficients after the program's fold, read in the field, are those of the library's fold
(midVec), if the row has passed the program's own test of its sizes. -/
theorem vecS_foldOutput_fits (s : Sg) (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : ℕ)
    (eps : E) (gamma : List E) (claim : E) (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hg : gamma.length = s.h + s.g) (hok : foldRowOk S F row = true)
    (hZ : (S.codes.mask.getD F.maskCode default).ell = s.Z.l) :
    vecS s (foldOutput S F row fresh eps gamma claim) =
      midVec s s.Z.l (vecG s row) (readE eps) (readP (s.h + s.g) gamma) := by
  have hd : row.d.size = s.Z.l * 2 ^ s.h := by rw [(of_foldRowOk S F row hok).2, hZ, hh]
  funext j
  rcases j with j | j | j
  · show formAt (foldOutput S F row fresh eps gamma claim).c j.val = _
    rw [foldOutput_c]
    exact formAt_fixLow_fits row.c _ (fits_of_foldRowOk S F row hok) (s.h + s.g) gamma hg
      (by rw [hk]; exact Nat.le_add_right _ _) eps j.val
  · show readV ((foldOutput S F row fresh eps gamma claim).d.getD 0 #[]) j.val = _
    rw [foldOutput_d]
    show readV (foldMaskForm F.layout.h row.d eps gamma) j.val = _
    rw [hh]
    exact readV_foldMaskForm s.h s.g row.d eps gamma hg s.Z.l hd j.val
  · show readV ((foldOutput S F row fresh eps gamma claim).d.getD 1 #[]) j.val = _
    rw [foldOutput_d]
    show readV (foldMaskWeights F.layout.k F.layout.h
      (S.codes.mask.getD F.maskCode default).ell gamma.toArray) j.val = _
    have hz : (fun t : Fin (s.h + s.g) => readV gamma.toArray t.val) =
        fun t : Fin (s.h + s.g) => readL gamma t.val :=
      funext fun t => readV_toArray gamma t.val
    rw [hk, hh, readV_foldMaskWeights s.h s.g _ gamma.toArray j.val, hz]
    show _ = hideW s.h s.g s.Z.l (readP (s.h + s.g) gamma) j.val
    unfold hideW
    rw [if_pos j.isLt]
    rfl

/-- Every tensor of the form on the main row has the variables of one message of the code. -/
theorem vars_foldOutput_fits (S : Statement) (F : FoldShape) (row : GroupRow) (o : ℕ) (eps : E)
    (gamma : List E) (claim : E) (hg : gamma.length = F.layout.k)
    (hr : foldRowOk S F row = true) : ∀ v ∈ (foldOutput S F row o eps gamma claim).c.tensors,
      v.vars = ceilLog2 (S.codes.base.getD F.code default).ell := by
  intro v hv
  rw [foldOutput_c] at hv
  have h := (Form.fixLow_shape row.c gamma eps _
    (fits_tensors row.c _ (fits_of_foldRowOk S F row hr)) v hv).1
  rw [h, hg]
  omega

/-- What is public of the claim after a fold in which nothing is kept: six facts together. -/
theorem foldOutput_fit (S : Statement) (F : FoldShape) (row : GroupRow) (o : ℕ) (eps : E)
    (gamma : List E) (claim : E) (hg : gamma.length = F.layout.k)
    (hr : foldRowOk S F row = true) (hhk : F.layout.h ≤ F.layout.k)
    (hcol : foldMaskColumns F.layout.k F.layout.h ≤ (S.codes.mask.getD F.maskCode default).ell)
    (h0 : row.kept = #[])
    (hk : ∀ i, i < F.layout.members.size → F.layout.kept.getD i false = false) :
    (foldOutput S F row o eps gamma claim).kept = #[] ∧
    switchKept (foldOutput S F row o eps gamma claim) = #[] ∧
    (foldOutput S F row o eps gamma claim).keptRows = 0 ∧
    ((foldOutput S F row o eps gamma claim).d.getD 0 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell ∧
    ((foldOutput S F row o eps gamma claim).d.getD 1 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell ∧
    (∀ v ∈ (foldOutput S F row o eps gamma claim).c.tensors,
      v.vars = ceilLog2 (S.codes.base.getD F.code default).ell) :=
  ⟨foldOutput_kept_nil S F row o eps gamma claim h0,
    switchKept_foldOutput S F row o eps gamma claim hk,
    foldOutput_keptRows_zero S F row o eps gamma claim hk,
    size_foldOutput_d0 S F row o eps gamma claim hg hr hhk,
    size_foldOutput_d1 S F row o eps gamma claim hhk hcol,
    vars_foldOutput_fits S F row o eps gamma claim hg hr⟩

/-- A run of the program's fold on the view of a fold's written rounds returns, read in the field,
the claim after that fold. The run marks the mask as spent (c1) and takes the fold's rounds and
nothing else. The program's three public conditions on the shape, on the mask and on the row held.
Nothing is asked of the row's form. -/
theorem fold_sem (s : Sg) (F : FoldShape) (hk : F.layout.k = s.h + s.g)
    (hh : F.layout.h = s.h) (row : GroupRow) (o : ℕ) (dE dT : PQ.RD)
    (m : (wRound dE).Msg) (ch : (wRound dE).Chal)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate (s.h + s.g) dT))) (rest : List Fmt.RoundView)
    (c c' : Ctx) (out : SingleRows) (hd : c.ch.dry = false)
    (hZ : (c.st.codes.mask.getD F.maskCode default).ell = s.Z.l)
    (hp : c.ch.pending =
      PQ.rvSL (ckP .two) (dE :: List.replicate (s.h + s.g) dT) (m, ch, τ) ++ rest)
    (h : (foldVerify F row (some o)).Yields c out c') :
    stmS s out =
      (claimF dT _ (sentAt dE m 0 + (stmG s row).1 * gOne _ (valsOf dE ch)) τ,
        midVec s s.Z.l (stmG s row).2 (gOne _ (valsOf dE ch)) (ptF dT _ τ)) ∧
    ∃ (c1 : Ctx) (eps claim : E) (gamma : List E),
      (Blk.spendAsMask o).Yields c () c1 ∧ out = foldOutput c1.st F row o eps gamma claim ∧
      readP (s.h + s.g) gamma = ptF dT _ τ ∧ gamma.length = s.h + s.g ∧
      RanRounds (s.h + s.g + 1) rest c1 c' ∧ foldShapeOk c.st F = true ∧
      foldMaskOk c.st F o = true ∧ foldRowOk c1.st F row = true := by
  obtain ⟨c1, eps, claim, gamma, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    foldVerify_at F _ hk row o dE dT m ch τ rest c c' out hd hp h
  have hcodes : c1.st.codes = c.st.codes := by rw [Blk.spendAsMask_inv o c c1 h1]
  have hvec := vecS_foldOutput_fits s c1.st F row o eps gamma claim hk hh h8 h4
    (by rw [hcodes]; exact hZ)
  refine ⟨?_, c1, eps, claim, gamma, h1, h5, h7, h8, h10, h2, h3, h4⟩
  rw [h5]
  refine Prod.ext ?_ ?_
  · exact h9
  · show vecS s (foldOutput c1.st F row o eps gamma claim) = _
    rw [hvec, h6, h7]
    rfl

/-! ## A fold that receives its own mask -/

/-- The fold's test of the shape still holds in a statement with the same codes that has each
oracle message of the first. -/
theorem foldShapeOk_mono (S S' : Statement) (F : FoldShape) (hc : S'.codes = S.codes)
    (ho : ∀ (o : ℕ) (x : Oracle), S.oracles[o]? = some x → S'.oracles[o]? = some x)
    (h : foldShapeOk S F = true) : foldShapeOk S' F = true := by
  unfold foldShapeOk at h ⊢
  rw [hc]
  cases hb : S.codes.base[F.code]? with
  | none => rw [hb] at h; cases h
  | some cd =>
    cases hz : S.codes.mask[F.maskCode]? with
    | none => rw [hb, hz] at h; cases h
    | some zk =>
      rw [hb, hz] at h
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨⟨hA, hall⟩, hany⟩ := h
      refine ⟨⟨hA, ?_⟩, ?_⟩
      · rw [List.all_eq_true] at hall ⊢
        intro i hi
        have h1 := hall i hi
        cases hx : S.oracles[F.layout.members.getD i noId]? with
        | none => rw [hx] at h1; cases h1
        | some x =>
          rw [hx] at h1
          rw [ho _ _ hx]
          exact h1
      · rw [List.any_eq_true] at hany ⊢
        obtain ⟨i, hi, h1⟩ := hany
        refine ⟨i, hi, ?_⟩
        cases hx : S.oracles[F.layout.members.getD i noId]? with
        | none => rw [hx] at h1; cases h1
        | some x =>
          rw [hx] at h1
          rw [ho _ _ hx]
          exact h1

/-- A fold that receives its mask is the receiving of one oracle message, then a fold whose mask
has come. -/
theorem foldVerify_none (F : FoldShape) (row : GroupRow) (out : SingleRows) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (foldVerify F row none).Yields c out c') :
    ∃ ids z o, (Blk.receiveOracles #[foldMaskNotice F]).Yields c ids z ∧ ids[0]? = some o ∧
      (foldVerify F row (some o)).Yields z out c' := by
  unfold foldVerify at h
  obtain ⟨s1, x1, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  unfold foldStartVerify at k1
  obtain ⟨S0, y0, a0, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨hS0, hy0⟩ := (Blk.yields_statement _ _ _).1 a0
  rw [hS0, hy0] at a1
  obtain ⟨_, y1, a2, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hshape, hy1⟩ := (Blk.yields_must _ _ _).1 a2
  rw [hy1] at a3
  obtain ⟨ids, z, b1, b2⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨o, z2, b3, b4⟩ := (Blk.yields_bind _ _ _ _ _).1 b2
  obtain ⟨hi, hz⟩ := (Blk.yields_get _ _ _ _).1 b3
  rw [hz] at b4
  refine ⟨ids, z, o, b1, hi, ?_⟩
  obtain ⟨lay, _, _, _, ez⟩ := receiveOracles_inv _ ids c z hd b1
  have hsh : foldShapeOk z.st F = true := by
    rw [ez]
    refine foldShapeOk_mono c.st _ F rfl (fun o x hx => ?_) hshape
    have hlt : o < c.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    exact (Array.getElem?_append_left hlt).trans hx
  unfold foldVerify
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨s1, x1, ?_, k2⟩
  unfold foldStartVerify
  exact (Blk.yields_bind _ _ _ _ _).2 ⟨z.st, z, (Blk.yields_statement _ _ _).2 ⟨rfl, rfl⟩,
    (Blk.yields_bind _ _ _ _ _).2 ⟨(), z, (Blk.yields_must _ _ _).2 ⟨hsh, rfl⟩,
      (Blk.yields_bind _ _ _ _ _).2 ⟨o, z, (Blk.yields_pure _ _ _ _).2 ⟨rfl, rfl⟩, b4⟩⟩⟩

end OnBytes.Slice.ProxRun
