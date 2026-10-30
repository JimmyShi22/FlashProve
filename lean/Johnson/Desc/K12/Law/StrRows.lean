-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StrRows.lean: `strOf` against `wordAt`: one form. A definition, a statement and
its proof.

`strOf` (Johnson/Desc/K12/Law/StrOf.lean) is "the word as sent" off a written oracle; `wordAt`
(Johnson/Desc/Sound/MsgSig.lean) is one member's word off plain strings. This file does not import
that one: `rowAtW` below is its `rowAt`, three lines copied (a row's symbol out of a tenant's words
at a leaf; there it stands in a "noncomputable section", here the keyword is written). The two texts
are one, the name and blanks apart, by a program's comparison of the characters. That is not held by
a compile: whether RowTy, toF and toE are the same constants under the opens there as under these is
for one line "example : rowAtW = rowAt := rfl" in a file that imports both. The lemma is free of
both frames: it takes the tenant's main and mask words at each leaf as letters.
Main names:
  `rowAtW`: the copy of `rowAt`: over the base field: word number k; over the extension field: the
    three words from 3 k on.
  `strOf_rowAt`: mainW x, maskW x: the tenant's main and mask words at the leaf x. If word number k
    of mainW x, for k below the shape's main rows times their degree, is word number L.oM + k of the
    written oracle's column at x, and the like for the mask words (below three times the mask rows;
    from L.oZ on), and the main degree is 1 or 3: then strOf cs sh e0 L d o is the string ".inl x ↦
    rowAtW _ (mainW x) r, .inr x ↦ rowAtW _ (maskW x) r": the text of `wordAt` at mainW x :=
    ((wordOf G y tree tenant x).map (·.main)).getD [] and the like for the mask.
Limits: what is left between the two is the two premises: that a tenant's words at a leaf are the
stretch of the written oracle's column from the tenant's first word on: `wordOf` and `Strs`
(Johnson/Desc/Msg.lean) against the law's written oracles W0 and skM, skZ: the two frames' tie at
the first stage. Not shown. No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.StrOf

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice Johnson.Pack
open _root_.Run

/-- A row's symbol out of a tenant's words at a leaf: row number k. -/
noncomputable def rowAtW : (b : Bool) → List UInt64 → ℕ → RowTy b
  | true, ws, k => toF (ws.getD k 0)
  | false, ws, k => toE (ws.getD (3 * k) 0, ws.getD (3 * k + 1) 0, ws.getD (3 * k + 2) 0)

/-- strOf is the string that wordAt (Johnson/Desc/Sound/MsgSig.lean) writes, where the tenant's
words at each leaf are the stretch of the written oracle's column from the tenant's first word on.
-/
theorem strOf_rowAt (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) (L : OnBytes.Slice.Lay)
    (d : PQ.RD) (o : (wRound d).Orc) (mainW maskW : ℕ → List UInt64)
    (hdeg : sh.mainDeg = 1 ∨ sh.mainDeg = 3)
    (hM : ∀ x k, k < sh.mainRows * sh.mainDeg → (mainW x).getD k 0 = wordAt d o x (L.oM + k))
    (hZ : ∀ x k, k < sh.maskRows * 3 → (maskW x).getD k 0 = wordAt d o x (L.oZ + k)) :
    strOf cs sh e0 L d o = fun p =>
      match p with
      | .inl x => fun r => rowAtW (sh.mainDeg == 1) (mainW x.val) r.1.val
      | .inr x => fun r => rowAtW false (maskW x.val) r.1.val := by
  funext p
  rcases p with x | x
  · funext r
    have hr : r.1.val < sh.mainRows := r.1.isLt
    show rowOf (sh.mainDeg == 1) _ _ = rowAtW (sh.mainDeg == 1) (mainW x.val) r.1.val
    rcases hdeg with h1 | h3
    · have hb : (sh.mainDeg == 1) = true := by simp [h1]
      rw [hb]
      show toF _ = toF _
      rw [hM x.val r.1.val (by rw [h1]; omega)]
    · have hb : (sh.mainDeg == 1) = false := by simp [h3]
      rw [hb]
      show symW d o x.val (L.oM + 3 * r.1.val) = toE _
      rw [hM x.val (3 * r.1.val) (by rw [h3]; omega),
        hM x.val (3 * r.1.val + 1) (by rw [h3]; omega),
        hM x.val (3 * r.1.val + 2) (by rw [h3]; omega)]
      rfl
  · funext r
    have hr : r.1.val < sh.maskRows := r.1.isLt
    show symW d o x.val (L.oZ + 3 * r.1.val) = toE _
    rw [hZ x.val (3 * r.1.val) (by omega), hZ x.val (3 * r.1.val + 1) (by omega),
      hZ x.val (3 * r.1.val + 2) (by omega)]
    rfl

end H2K.Pin

#print axioms H2K.Pin.strOf_rowAt
