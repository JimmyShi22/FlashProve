-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/FoldErrIx.lean: THE COUNT OF A STORED TABLE's BAD FOLD POINTS, FOR AN INDEX ALONE:
the statement of Johnson/Bridge/FoldErrLin.lean said of an `LdIx` (Cb/Ld/LdFoldEq.lean: a code's
matrix, a decoder's radius, the number of row variables, the places of the message part, a sample, a
rank) and a radius, without the test on the table (`LdLinP`) around it: so that whoever has
instanced the index, and not the test's three families of messages, can spend it.

Of the q^v fold points at most v b q^(v - 1) + L (v q^(v - 1)) are bad (`LdIx.Bad`: there is a full
message u whose codeword is within e' of the fold of the stored words, that has the record's folded
answers, and whose message part is not the fold of the decoded index, or the index does not decode),
for every table of stored words f and every record rec without a collision at the record's seed
(`LdIx.Coll`).

It rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/: files adapted
from ArkLib and Mathlib
(lean/LIMITS.md, L15). The proofs are applications: `ldFe_cnt` (Cb/Ld/LdFoldEqProofs.lean) with the
three facts that Johnson/Bridge/FoldErrLin.lean's head names.
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Main names, in the namespace `Cb.Bridge`:
  `foldErr_ix`: at letters: b the integer part of `Cb.bchksBound`, L the Johnson bound's list.
  `foldErr_ix_ptCount`: at the planner's count `ptCount`.
In the namespace `Johnson.Bridge`:
  `PointPlace.bad_le_top`: FROM A YES OF THE PLACE's TEST `good`: at most `PointPlace.top`, a
    natural number made off the planner's record of the table and a radius.

Limits: the index X is a parameter: no file's index is written here. That its matrix is the format's
code's, its number of row variables the table's, and its two radii the place's, are hypotheses. HOW
OFTEN A TABLE HAS A COLLISION AT A SEED IS NOT SAID HERE. That `top` is small is the comparison of
Johnson/Bridge/PlanPoints.lean. Nothing on the soundness of the check of a file.

-/
import Johnson.Bridge.PlanPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin

variable (C : Fmt.M1.Code) {J : Type} [Fintype J]
  (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J)

/-- **The bad fold points of an index, below the Johnson radius.** -/
theorem foldErr_ix (e' : ℕ) (ha : C.a ≤ 32) (hk : 0 < C.r + C.l - 1) (hr : C.r + C.l ≤ 2 ^ C.a)
    (hG : X.G = genOf C) (he : 0 < e') (hle : e' ≤ X.eM)
    (hM : X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) e')
    (f : X.Row → Fin (2 ^ C.a) → GE) (rec : X.Rec) (hc : ¬ X.Coll f rec.1) :
    cnt (X.Bad f rec e') ≤
      X.v * ⌊bchksBound (2 ^ C.a) (C.r + C.l - 1) e'⌋₊ * Fintype.card GE ^ (X.v - 1) +
        listMax (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) e' *
          (X.v * Fintype.card GE ^ (X.v - 1)) := by
  have hd : HasDist X.G (2 ^ C.a - (C.r + C.l) + 1) := by
    rw [hG]
    exact hasDist_genOf C ha hr
  have e1 : C.r + C.l - 1 = 2 ^ C.a - (2 ^ C.a - (C.r + C.l) + 1) := by omega
  have hj : 2 ^ C.a * (C.r + C.l - 1) < (2 ^ C.a - e') ^ 2 := by
    rw [e1]
    exact hJ
  exact ldFe_cnt X _ e' _ _ f rec hd hM hle
    (mcaEq_bchksAt (bchks46At GF GE) C ha hk X hG e' he hj) (list_johnson C ha hr X hG e' hJ f) hc

/-- **The same at `ptCount`.** -/
theorem foldErr_ix_ptCount (T : TableSize) (e' : ℕ) (hn : (wordOf T.code).n = 2 ^ C.a)
    (hw : (wordOf T.code).k = C.r + C.l - 1) (hv : X.v = T.v) (ha : C.a ≤ 32)
    (hk : 0 < C.r + C.l - 1) (hr : C.r + C.l ≤ 2 ^ C.a) (hG : X.G = genOf C) (he : 0 < e')
    (hle : e' ≤ X.eM) (hM : X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) e')
    (f : X.Row → Fin (2 ^ C.a) → GE) (rec : X.Rec) (hc : ¬ X.Coll f rec.1) :
    cnt (X.Bad f rec e') ≤ ptCount T e' (Fintype.card GE) := by
  have e3 : 2 ^ C.a - (C.r + C.l - 1) = 2 ^ C.a - (C.r + C.l) + 1 := by omega
  rw [ptCount_eq T _ _ _ X.v (Fintype.card GE) e' hn hw e3 hv]
  exact foldErr_ix C X e' ha hk hr hG he hle hM hJ f rec hc

end Cb.Bridge

namespace Johnson.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin
open Cb.Bridge

/-- **From a yes of the place's test: at most `top` fold points are bad**, at an index with the
place's code, number of row variables and radius, for every table and record without a collision at
the record's seed. -/
theorem PointPlace.bad_le_top {x : PointPlace} (hg : x.good = true) {J : Type} [Fintype J]
    (X : LdIx GE (Fin (2 ^ (codeOfSize x.T.code).a))
      (Fin ((codeOfSize x.T.code).r + (codeOfSize x.T.code).l)) J)
    (hM : X.eM = x.e) (hG : X.G = genOf (codeOfSize x.T.code)) (hv : X.v = x.T.v)
    (f : X.Row → Fin (2 ^ (codeOfSize x.T.code).a) → GE) (rec : X.Rec)
    (hc : ¬ X.Coll f rec.1) : Prob.cnt (X.Bad f rec x.e) ≤ x.top := by
  have hg' := hg
  simp only [PointPlace.good, Bool.and_eq_true] at hg'
  obtain ⟨hn, hw, ha, hk, hr, he0, hle, hM', hJ⟩ := foldTest_sound hg'.1
  have h := foldErr_ix_ptCount (codeOfSize x.T.code) X x.T x.e hn hw hv ha hk hr hG he0
    (by rw [hM]) (by rw [hM]; exact hM') hJ f rec hc
  rw [Cb.Gl.gl_card.2.1] at h
  exact le_trans h (PointPlace.ptCount_le hg)

end Johnson.Bridge

#print axioms Cb.Bridge.foldErr_ix
#print axioms Cb.Bridge.foldErr_ix_ptCount
#print axioms Johnson.Bridge.PointPlace.bad_le_top
