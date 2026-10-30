-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/SeamW.lean: the claims on the committed weights give the rows on the batched sumcheck's
end values that are tensor claims.

The batched sumcheck of a layers' sub-proof (Cb/Pv/Lay/At/Inner.lean) leaves, for each piece of its
second side that belongs to a weight panel, a row on an end value: the piece's extension at the end
point, plus a mask entry times the last challenge, is the value that was shown. The last stretch
(Cb/Pv/Lay/At/FootW.lean) starts from one claim for each such piece: the value of a pair (γ, ε) on
the committed matrix, plus that mask entry times that challenge, is that value. This file fills the
last stretch's letters from those of the batched sumcheck, with the pairs tenAt of
Cb/Pv/Lay/At/TnSplit.lean, and shows that its claims give these rows.

Main names.
  Piece: the names of the pieces of the weight panels.
  InnPar0.wPar: the letters of the last stretch. num: a numbering of the pieces, a letter.
  InnPar0.st7: what the last stretch reads of an output statement of the batched sumcheck.
  InnPar0.piece_pan, piece_row: a piece's map at a point is the library's TnPan, TnRow.
  InnPar0.piece_map: it is the value of the piece's pair on the matrix.
  InnPar0.seam_w: the claims of the last stretch give the rows on the pieces' end values.

The hypotheses of seam_w: the weights are those that the layout reads in a matrix Wn m; L0 is even;
a layer has twice an expert's hidden units; at most 64 heads; every piece's layer is a layer of the
model; the matrix has room for all units.

Limits. The programs' numbering of the claims is not looked at. What St7 holds for the first group
alone (two further points, the tokens) is laid as 0 here.


-/
import Cb.Pv.Lay.At.Inner
import Cb.Pv.Lay.At.TnSplit
import Cb.Pv.Lay.At.TnExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At

open Cb Finset
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.Layout.Tensor (matOf)
open Inst.Model.FFSeg (Dim Pan pans lamS layerR)

noncomputable section

/-- The names of the pieces of the weight panels. -/
abbrev Piece (D : Dim) : Type := Σ p : {p : Pan // p ∈ pans D}, Fin (cntB D p.1)

variable {E : Type} [Field E] [Fintype E] [scl : Scl]

omit scl in
/-- A piece belongs to a weight panel. -/
theorem piece_weight {D : Dim} (i : Piece D) : i.1.1.weight = true := by
  by_contra h
  have e : cntB D i.1.1 = 0 := by
    unfold cntB
    rw [if_neg h]
  exact Nat.not_lt_zero _ (lt_of_lt_of_eq i.2.isLt e)

omit scl in
/-- A panel with three factors has one piece, number 0. -/
theorem piece_zero {D : Dim} (i : Piece D) (h3 : i.1.1.three = true) : (i.2 : ℕ) = 0 := by
  have e : cntB D i.1.1 = 1 := by
    unfold cntB
    rw [if_pos (piece_weight i), if_pos h3]
  have h2 := lt_of_lt_of_eq i.2.isLt e
  omega

namespace InnPar0
variable (P : InnPar0 E)

/-- The letters of the last stretch, from those of the batched sumcheck. k, h: the column bits and
the rows of the matrix; Wn: how the entries are read as the matrix; num: a numbering of the pieces;
wAt, cAt: the last sumcheck's own masks. -/
def wPar (k h n : ℕ) (Wn : (P.J → E) → ℕ → ℕ → E) (num : Fin n ≃ Piece P.D)
    (wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 1]) → P.J) (cAt : P.J) : FootW0 E where
  J := P.J
  k := k
  h := h
  n := n
  Wm := fun m => matOf (Wn m)
  ten := fun a st => tenAt P.D P.tb P.L0 k h (if (num a).1.1.late then st.zl else st.z) st.zh
    st.zeta (num a).1.1 (num a).2
  nm := fun a => P.cI (.inr (.inr (num a)))
  wAt := wAt
  cAt := cAt

/-- What the last stretch reads of an output statement of the batched sumcheck. -/
def st7 {n : ℕ} (num : Fin n ≃ Piece P.D) (o : P.inn.toSum.T.par.Out) : St7 E n where
  zeta := Blocks.nat (P.inn.Kp.outPt P.inn.Mk o)
  z := o.st.z
  zh := P.rt o.st
  zl := o.st.o3.st
  pa := fun _ => 0
  pb := fun _ => 0
  tok := fun _ => 0
  be := P.inn.Kp.outB P.inn.Mk o
  v := fun a => o.vals (.inr (.inr (num a)))

/-- The map of a piece, written out. -/
theorem piece_F (st : P.St) (m : P.J → E) (i : Piece P.D) (zz : Fin (kS P.D) → E) :
    P.inn.F st m (.inr (.inr i)) zz =
      extAt (if i.1.1.three then i.1.1.wid P.D else i.1.1.wcol P.D)
        (kS P.D - if i.1.1.three then i.1.1.wid P.D else i.1.1.wcol P.D)
        (if i.1.1.three then P.VB st m i.1.1
          else fun ι => if ι < i.1.1.nc P.D then P.FB st m i.1.1 i.2 ι else 0) (Blocks.nat zz) :=
  rfl

/-- On a panel with three factors the second side's public factors are 1. -/
theorem κB_three (st : P.St) (p : Pan) (h3 : p.three = true) (ρ : ℕ) : P.κB st p ρ = 1 := by
  cases p <;> first | rfl | cases h3

/-- The map of the piece of a panel with three factors is the library's value of the panel. -/
theorem piece_pan (st : P.St) (m : P.J → E) (i : Piece P.D) (h3 : i.1.1.three = true)
    (zz : Fin (kS P.D) → E) :
    P.inn.F st m (.inr (.inr i)) zz =
      i.1.1.TnPan P.D (P.rP st m i.1.1) P.tb P.L0 (P.rw m) (P.zP st i.1.1) (P.rt st)
        (Blocks.nat zz) := by
  have hk : kS P.D - i.1.1.wid P.D = lamS P.D - i.1.1.wid P.D := by rw [kS_eq]
  rw [piece_F, if_pos h3, if_pos h3, hk,
    ← pan_ext P.D (P.rP st m i.1.1) P.tb P.L0 (P.rw m) (P.zP st i.1.1) (P.rt st) (Blocks.nat zz)
      i.1.1 (wid_le P.D i.1.2)]
  refine extAt_congr (fun y _ => ?_) _
  unfold VB cellOf
  simp only [P.κB_three st i.1.1 h3, one_mul]
  rfl

/-- The map of a piece of a panel with two factors is the library's value of the row. -/
theorem piece_row (st : P.St) (m : P.J → E) (i : Piece P.D) (h3 : ¬ i.1.1.three = true)
    (zz : Fin (kS P.D) → E) :
    P.inn.F st m (.inr (.inr i)) zz =
      i.1.1.TnRow P.D (P.rP st m i.1.1) P.tb P.L0 (P.rw m) (P.zP st i.1.1) (P.rt st)
        (Blocks.nat zz) i.2 := by
  have hk : kS P.D - i.1.1.wcol P.D = lamS P.D - i.1.1.wcol P.D := by rw [kS_eq]
  rw [piece_F, if_neg h3, if_neg h3, hk,
    ← row_ext P.D (P.rP st m i.1.1) P.tb P.L0 (P.rw m) (P.zP st i.1.1) (P.rt st) (Blocks.nat zz)
      i.1.1 i.2]
  rfl

/-- A piece's extension at a point is the value of its pair on the matrix. -/
theorem piece_map (k h : ℕ) (Wn : (P.J → E) → ℕ → ℕ → E) (st : P.St) (m : P.J → E)
    (hrw : P.rw m = fun l => layerR P.D.P k (Wn m) (P.L0 + l)) (h0 : P.L0 % 2 = 0)
    (hf : P.D.f = 2 * P.D.fe) (hh : P.D.P.nq + P.D.P.nkv ≤ 64) (i : Piece P.D)
    (hL : P.L0 + layerOfRow i.1.1 i.2 < P.D.P.layers)
    (hH : off k (units P.D.P) (units P.D.P).length ≤ h) (zz : Fin (kS P.D) → E) :
    P.inn.F st m (.inr (.inr i)) zz =
      tval (tenAt P.D P.tb P.L0 k h (P.zP st i.1.1) (P.rt st) (Blocks.nat zz) i.1.1 i.2)
        (matOf (Wn m)) := by
  have hw := piece_weight i
  by_cases h3 : i.1.1.three = true
  · have e0 := piece_zero i h3
    rw [e0] at hL
    rw [P.piece_pan st m i h3 zz, hrw, e0]
    exact (tenAt_pan P.D P.tb k h (P.zP st i.1.1) (P.rt st) (Blocks.nat zz) (P.rP st m i.1.1) h0
      hf i.1.1 hw h3 hL hH (Wn m)).symm
  · rw [P.piece_row st m i h3 zz, hrw]
    exact (tenAt_row P.D P.tb k h (P.zP st i.1.1) (P.rt st) (Blocks.nat zz) (P.rP st m i.1.1) h0
      hf hh i.1.1 hw (by simpa using h3) i.2 hL hH (Wn m)).symm

/-- The claims of the last stretch give the rows on the end values of the pieces of the weight
panels. -/
theorem seam_w (k h n : ℕ) (Wn : (P.J → E) → ℕ → ℕ → E) (num : Fin n ≃ Piece P.D)
    (wAt : PIdx (ldPartFmt E k (fun _ => 2) ++ [pDummy E 1]) → P.J) (cAt : P.J)
    (o : P.inn.toSum.T.par.Out) (m : P.J → E)
    (hrw : P.rw m = fun l => layerR P.D.P k (Wn m) (P.L0 + l)) (h0 : P.L0 % 2 = 0)
    (hf : P.D.f = 2 * P.D.fe) (hh : P.D.P.nq + P.D.P.nkv ≤ 64)
    (hL : ∀ i : Piece P.D, P.L0 + layerOfRow i.1.1 i.2 < P.D.P.layers)
    (hH : off k (units P.D.P) (units P.D.P).length ≤ h)
    (hc : ∀ a, (P.wPar k h n Wn num wAt cAt).wt.val (P.st7 num o) m a =
      (P.wPar k h n Wn num wAt cAt).wt.sh a (P.st7 num o)) :
    ∀ i : Piece P.D, P.inn.toSum.T.par.EHolds o m (.inr (.inr i)) := by
  intro i
  obtain ⟨a, rfl⟩ := num.surjective i
  rw [InnL.ev_iff, P.piece_map k h Wn o.st m hrw h0 hf hh (num a) (hL _) hH]
  have e := hc a
  rw [FootW0.wt_val] at e
  exact e

end InnPar0

end

end Cb.Pv.Lay.At
