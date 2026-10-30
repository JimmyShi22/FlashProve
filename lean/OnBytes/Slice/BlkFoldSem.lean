-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkFoldSem.lean: the claim that the program's fold returns is the claim after a fold
of the written protocol, in the field.

OnBytes/Slice/FoldPeel.lean gives the claim after a fold in the field, from the claim before it and
the written rounds: the target `claimF`, the vector `midVec`, at the drawn point `ptF`.
OnBytes/Slice/BlkFold.lean says what a run of the program's fold reads of these rounds, and
OnBytes/Slice/BlkFoldVec.lean reads the vectors of coefficients that it returns. This file joins the
two: the statement that the run returns, read in the field (OnBytes/Slice/BlkRead.lean: `stmS`), is
that claim, made from the reading of the row that the run was given (`stmG`).

What is asked: the shape has the stage's numbers of variables, the mask code has the stage's message
length, and no tensor of the row's form on the main table has a written-out factor.

Main theorems: `foldVerify_at`, `blk_fold_sem`.
Not claimed. Nothing on kept members of a group. Nothing on the dry run. Nothing on soundness.
-/
import OnBytes.Slice.BlkFold
import OnBytes.Slice.BlkFoldVec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-- `foldVerify_sem` with the number of variables under a name of its own. -/
theorem foldVerify_at (F : FoldShape) (k : ℕ) (hk : F.layout.k = k) (row : GroupRow) (o : ℕ)
    (dE dT : PQ.RD) (m : (wRound dE).Msg) (ch : (wRound dE).Chal)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))) (rest : List Fmt.RoundView)
    (c c' : Ctx) (out : SingleRows) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) (dE :: List.replicate k dT) (m, ch, τ) ++ rest)
    (h : (foldVerify F row (some o)).Yields c out c') :
    ∃ (c1 : Ctx) (eps claim : E) (gamma : List E),
      (Blk.spendAsMask o).Yields c () c1 ∧ foldShapeOk c.st F = true ∧
      foldMaskOk c.st F o = true ∧ foldRowOk c1.st F row = true ∧
      out = foldOutput c1.st F row o eps gamma claim ∧
      readE eps = gOne _ (valsOf dE ch) ∧ readP k gamma = ptF dT k τ ∧ gamma.length = k ∧
      readE claim = claimF dT k (sentAt dE m 0 + readE row.target * gOne _ (valsOf dE ch)) τ ∧
      RanRounds (k + 1) rest c1 c' := by
  subst hk
  exact foldVerify_sem F row o dE dT m ch τ rest c c' out hd hp h

/-- A run of the program's fold on the view of a fold's written rounds returns, read in the field,
the claim after that fold. The run marks the mask as spent (c1) and takes the fold's rounds and
nothing else. The program's three public conditions on the shape, on the mask and on the row held.
The file's head says what `hk`, `hh`, `hZ` and `hpl` ask. -/
theorem blk_fold_sem (s : Sg) (F : FoldShape) (hk : F.layout.k = s.h + s.g)
    (hh : F.layout.h = s.h) (row : GroupRow) (hpl : PlainForm row.c) (o : ℕ) (dE dT : PQ.RD)
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
  have hvec := vecS_foldOutput_ok s c1.st F row o eps gamma claim hk hh h8 hpl h4
    (by rw [hcodes]; exact hZ)
  refine ⟨?_, c1, eps, claim, gamma, h1, h5, h7, h8, h10, h2, h3, h4⟩
  rw [h5]
  refine Prod.ext ?_ ?_
  · exact h9
  · show vecS s (foldOutput c1.st F row o eps gamma claim) = _
    rw [hvec, h6, h7]
    rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.foldVerify_at
#print axioms OnBytes.Slice.blk_fold_sem
