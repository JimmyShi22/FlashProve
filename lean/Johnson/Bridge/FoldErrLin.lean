-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/FoldErrLin.lean: the condition on the fold that the test on a stored table asks
(`LdLinP.FoldErr`, Cb/Ld/LdLin.lean) holds at a radius below the Johnson radius, for a test whose
rows are coded by the format's code, for every table without a collision at the record's seed (two
tables within the decoder's radius with the same answers). Of the q^v fold points at most
v b q^(v - 1) + L (v q^(v - 1)) are bad: the table has 2^v rows, q is the size of the field `GE`, b
the integer part of `Cb.bchksBound`, L the Johnson bound on lists (`Cb.listMax`).

The proofs are applications, with three equations on numbers. `ldLin_foldErr`
(Cb/Ld/LdLinProofs.lean) gives the condition from a distance (`hasDist_genOf`,
OnBytes/Slice/CodeFacts.lean), a count of exceptional fold points (`mcaEq_bchksAt`,
OnBytes/Slice/LinkRecBchks.lean, under the statement on codes) and a bound on the lists of tables
(`list_johnson`, the same file, without that statement). `link_sound_bchks` in that file takes the
same three steps for the written link with records.
Main names, in the namespace `Cb.Bridge`:
  `foldErr_lin_of`: with the statement on codes, `Cb.BCHKS46At GF GE`, as a hypothesis.
  `foldErr_lin`: without it: `Cb.Bridge.bchks46At` (Cb/Bridge/CodeListRSProved.lean) is used for it.
  `ptCount_eq`: the count `ptCount` (OnBytes/Tie/Pv/LinPortAt.lean) written out: an identity on
    numbers.
  `foldErr_lin_ptCount`: `foldErr_lin` at `ptCount`. With that count, `pt_covered_at` (the same
    file) shows under its own premises that the planner's round "LIN point" covers the point's error
    for one instance.
`foldErr_lin` and `foldErr_lin_ptCount` rest on the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.
Limits: the test P is a parameter: no file's test is written here. That its matrix is the format's,
and the conditions on its radii and sizes, are hypotheses; those on numbers hold together at two
sets of numbers (`Sz.radJ_full`, `Sz.radJ_small`, OnBytes/Slice/LinkRecBchks.lean). How often a
table has a collision is not said. No number is evaluated, so nothing says that the count is small:
close to the Johnson radius it can pass q^v, and the statement then says nothing. Nothing on the
soundness of the check of a file.

-/
import Cb.Ld.LdLinProofs
import OnBytes.Slice.LinkRecBchks
import OnBytes.Tie.Pv.LinPortAt
import Cb.Bridge.CodeListRSProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin

variable (C : Fmt.M1.Code) {J Y : Type} [Fintype J]
  (P : LdLinP GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J Y)

/-- **The condition on the fold below the Johnson radius, under the statement on codes.** -/
theorem foldErr_lin_of (hA : BCHKS46At GF GE) (ha : C.a ≤ 32) (hk : 0 < C.r + C.l - 1)
    (hr : C.r + C.l ≤ 2 ^ C.a) (hG : P.D.X.G = genOf C) (he : 0 < P.e') (hle : P.e' ≤ P.D.X.eM)
    (hM : P.D.X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e') :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1)
      (P.D.X.v * ⌊bchksBound (2 ^ C.a) (C.r + C.l - 1) P.e'⌋₊ * Fintype.card GE ^ (P.D.X.v - 1) +
        listMax (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e' *
          (P.D.X.v * Fintype.card GE ^ (P.D.X.v - 1))) := by
  have hd : HasDist P.D.X.G (2 ^ C.a - (C.r + C.l) + 1) := by
    rw [hG]
    exact hasDist_genOf C ha hr
  have e1 : C.r + C.l - 1 = 2 ^ C.a - (2 ^ C.a - (C.r + C.l) + 1) := by omega
  have hj : 2 ^ C.a * (C.r + C.l - 1) < (2 ^ C.a - P.e') ^ 2 := by
    rw [e1]
    exact hJ
  exact ldLin_foldErr P _ _ _ hd hM hle (mcaEq_bchksAt hA C ha hk P.D.X hG P.e' he hj)
    (fun f => list_johnson C ha hr P.D.X hG P.e' hJ f)

/-- **The same with the hypothesis on codes filled.** -/
theorem foldErr_lin (ha : C.a ≤ 32) (hk : 0 < C.r + C.l - 1)
    (hr : C.r + C.l ≤ 2 ^ C.a) (hG : P.D.X.G = genOf C) (he : 0 < P.e') (hle : P.e' ≤ P.D.X.eM)
    (hM : P.D.X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e') :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1)
      (P.D.X.v * ⌊bchksBound (2 ^ C.a) (C.r + C.l - 1) P.e'⌋₊ * Fintype.card GE ^ (P.D.X.v - 1) +
        listMax (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e' *
          (P.D.X.v * Fintype.card GE ^ (P.D.X.v - 1))) :=
  foldErr_lin_of C P (bchks46At GF GE) ha hk hr hG he hle hM hJ

/-- The planner's count, written out: an identity on numbers, at letters. -/
theorem ptCount_eq (T : TableSize) (n K d v q e : ℕ) (hn : (wordOf T.code).n = n)
    (hw : (wordOf T.code).k = K) (hd : n - K = d) (hv : v = T.v) :
    ptCount T e q =
      v * ⌊bchksBound n K e⌋₊ * q ^ (v - 1) + listMax n d e * (v * q ^ (v - 1)) := by
  subst hv
  unfold ptCount
  rw [hn, hw, hd]
  ring

/-- **The same at `ptCount`** (OnBytes/Tie/Pv/LinPortAt.lean): the count at which that file's
`pt_tied_at` shows, under its own premises (among them a radius of at most (1 - a) n), that the
planner's round "LIN point" covers `errPt`, the error of one instance. -/
theorem foldErr_lin_ptCount (T : TableSize) (hn : (wordOf T.code).n = 2 ^ C.a)
    (hw : (wordOf T.code).k = C.r + C.l - 1) (hv : P.D.X.v = T.v)
    (ha : C.a ≤ 32) (hk : 0 < C.r + C.l - 1)
    (hr : C.r + C.l ≤ 2 ^ C.a) (hG : P.D.X.G = genOf C) (he : 0 < P.e') (hle : P.e' ≤ P.D.X.eM)
    (hM : P.D.X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e') :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1) (ptCount T P.e' (Fintype.card GE)) := by
  have e3 : 2 ^ C.a - (C.r + C.l - 1) = 2 ^ C.a - (C.r + C.l) + 1 := by omega
  rw [ptCount_eq T _ _ _ P.D.X.v (Fintype.card GE) P.e' hn hw e3 hv]
  exact foldErr_lin C P ha hk hr hG he hle hM hJ

end Cb.Bridge

#print axioms Cb.Bridge.foldErr_lin_of
#print axioms Cb.Bridge.foldErr_lin
#print axioms Cb.Bridge.ptCount_eq
#print axioms Cb.Bridge.foldErr_lin_ptCount
