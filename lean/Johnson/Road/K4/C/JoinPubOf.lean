-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/JoinPubOf.lean: CONDITIONAL.

What is here. SIX PUBLIC HYPOTHESES OF THE LAWS ON THE LOOKUP's SIDE OF THE JOIN, EACH FROM FEWER.
The laws that carry the lookup's own sentence to the feed-forward layers' own rounds (sub-protocol
K4) ask public facts on the layout, the sizes and the calls one by one. Here six of them follow
from two facts: that the layout is the verifier's own return at a shape with routed experts (hy,
hp3), and that the sizes agree with the shape (`Sized`, `SizedW`); layers_lt takes besides that the
weights' shape has the shape's number of layers (hsL) and that the group is one of the layout's
(hg). WHO CALLS THEM: Johnson/Desc/ProofFile/Honest/K4/Law/JoinWholeFew.lean all six;
Law/W/TokOfFine.lean `T_of`. Lemmas on variables: calls of the library's facts on a layout, and
arithmetic.

  `lam_even`, `layers_lt`   a group begins at an even layer; its layers are the model's.
  `T_of`, `dh_even`, `ch_pos`   the layout's number of positions is the sizes'; the width of a head
      is even (the shape's h.dh), and not 0 (the sizes' D.P.ch: one number by `Sized`).
  `fo_ok`   the layout's shape of the lookup passes the lookup's test on numbers.

Not shown here. That a layout is returned anywhere, nor that the sizes agree with the shape there
(`Sized`, `SizedW`, hsL and hg together with hy): `Sized` alone has a member (the library's
`sized_dimOf`); hsL HAS NO PAYER. Each of the six is CONDITIONAL on the hypotheses in its own
binders; the docstrings do not name them. Nothing on what a form is worth.

No property is claimed.
-/
import Johnson.Road.FormsKeysFits
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysQK
import Johnson.Road.FormsKeysWLay
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicShape
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay layout)
open Inst.Model.FFSeg (Dim)

/-- A group begins at an even layer. -/
theorem lam_even {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (hp3 : h.p3 = true) (g : ℕ) : g * y.Lam % 2 = 0 := by
  have A := (admitted_of_layout hy hp3).laid
  obtain ⟨k, hk⟩ : ∃ k, y.h.ll = k + 1 := ⟨y.h.ll - 1, by have := A.ll; omega⟩
  rw [A.Lam, hk, Nat.pow_succ, ← Nat.mul_assoc]
  generalize g * 2 ^ k = t
  omega

/-- The layers of a group are layers of the model. -/
theorem layers_lt {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (hp3 : h.p3 = true) {D : Dim} (Z : Sized h D) {s : WsShape} (ZW : SizedW s D.P)
    (hsL : s.L = h.L) {g : ℕ} (hg : g < y.NGr) : ∀ l < D.nl, g * y.Lam + l < D.P.layers := by
  intro l hl
  have A := admitted_of_layout hy hp3
  have e1 : D.nl = 2 ^ h.ll := by
    show 2 ^ D.lL = _
    rw [Z.lL]
  have e2 : y.Lam = 2 ^ h.ll := by rw [A.laid.Lam, A.shape]
  rw [← ZW.L, hsL, e2]
  rw [e1] at hl
  rw [A.NGr] at hg
  generalize 2 ^ h.ll = q at hl hg ⊢
  have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) hl
  have h1 : (g + 1) * q ≤ h.L := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt hg)
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- The layout's number of positions is the sizes'. -/
theorem T_of {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (hp3 : h.p3 = true) {D : Dim} (Z : Sized h D) : y.T = D.T := by
  rw [(headsLaid_of_layout hy).T, (admitted_of_layout hy hp3).shape]
  show _ = 2 ^ D.lT
  rw [Z.lT]

/-- The width of a head is even. -/
theorem dh_even {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (hp3 : h.p3 = true) : h.dh % 2 = 0 := by
  have L := headsLaid_of_layout hy
  obtain ⟨k, hk⟩ : ∃ k, y.ldh = k + 1 := ⟨y.ldh - 1, by have := L.two; omega⟩
  rw [← (admitted_of_layout hy hp3).shape, L.pow, hk, Nat.pow_succ]
  generalize 2 ^ k = t
  omega

/-- The width of a head is not 0. -/
theorem ch_pos {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (hp3 : h.p3 = true) {D : Dim} (Z : Sized h D) : 0 < D.P.ch := by
  rw [Z.ch, ← (admitted_of_layout hy hp3).shape, (headsLaid_of_layout hy).pow]
  exact Nat.two_pow_pos _

/-- The layout's shape of the lookup passes the lookup's test on numbers. -/
theorem fo_ok {h : Layer.Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y) :
    FoNums.ok y.fo = true :=
  _root_.Fo.Pay.shapeOf_ok (_root_.Fo.layout_shape hy)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.lam_even
#print axioms OnBytes.Road.K4.C.layers_lt
#print axioms OnBytes.Road.K4.C.T_of
#print axioms OnBytes.Road.K4.C.dh_even
#print axioms OnBytes.Road.K4.C.ch_pos
#print axioms OnBytes.Road.K4.C.fo_ok
