-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PointBoth.lean: the shared point of the test on a stored table, for at most N
requests. At one and the same count, `ptCount` (OnBytes/Tie/Pv/LinPortAt.lean), the library's
condition on the fold holds (`LdLinP.FoldErr`, Cb/Ld/LdLin.lean) and the planner's round "LIN point"
covers the block's error (`LdLinP.errPtB`, Cb/Ld/LdLinB.lean).

One statement, `point_both`, in the namespace `Cb.Bridge`: a pair of two applications.
`foldErr_lin_ptCount` (Johnson/Bridge/FoldErrLin.lean) has the condition; `pt_tiedB_at`
(OnBytes/Tie/Pv/LinPortB.lean) has the cover, in any scope, for N at most `x.instances`, the sizes'
number of requests that share the point. The first holds of every larger count, the second of every
smaller one; the head of OnBytes/Tie/Pv/LinPort.lean says of the two: "That both hold of one εf is
not shown here."
It rests on the files under ThirdParty/, through `Cb.Bridge.bchks46At`: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.
Limits: the test P, the code C, the table T, the setting s and the sizes x are parameters. That they
fit each other, and all that the two statements ask, are hypotheses: twenty. No number is evaluated.
That the round's price, or the count, is small is not said: `Covered` compares with whatever the
plan holds of the round. The limits of OnBytes/Tie/Pv/LinPortB.lean on scopes hold here. The
condition speaks of the tables without a collision at the record's seed. Nothing on the soundness of
the check of a file.

-/
import Johnson.Bridge.FoldErrLin
import OnBytes.Tie.Pv.LinPortB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin

variable (C : Fmt.M1.Code) {J Y : Type} [Fintype J]
  (P : LdLinP GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J Y)

/-- **The condition on the fold and the planner's cover for at most N requests, N at most
`x.instances`, at one count** (not all hypotheses are named here: see the statement below). -/
theorem point_both {s : Setting} {T : TableSize} {x : LinSize} (c : Scope) {N : ℕ}
    (hn : (wordOf T.code).n = 2 ^ C.a) (hw : (wordOf T.code).k = C.r + C.l - 1)
    (hv : P.D.X.v = T.v) (ha : C.a ≤ 32) (hk : 0 < C.r + C.l - 1) (hr : C.r + C.l ≤ 2 ^ C.a)
    (hG : P.D.X.G = genOf C) (he : 0 < P.e') (hle : P.e' ≤ P.D.X.eM)
    (hM : P.D.X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (hJ : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) P.e')
    (hm : T.distances.mOnce ≠ 0) (hp : s.printed = true)
    (gc : (linProx s T x).count.bad = false)
    (hrad : (P.e' : ℝ) ≤
      (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ))
    (hN : N ≤ x.instances) (hq : Fintype.card GE = s.cardE) (hkl : P.D.klo = x.kLo)
    (hg : (linPoint s T x).Good s c) :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1) (ptCount T P.e' s.cardE) ∧
      Covered s c (P.errPtB (ptCount T P.e' s.cardE) N, Fintype.card P.D.Pt) (linPoint s T x) := by
  refine ⟨?_, pt_tiedB_at P c hm hp gc (by rw [hw]; exact hk) hrad hN hq hv hkl hg⟩
  rw [← hq]
  exact foldErr_lin_ptCount C P T hn hw hv ha hk hr hG he hle hM hJ

end Cb.Bridge

#print axioms Cb.Bridge.point_both
