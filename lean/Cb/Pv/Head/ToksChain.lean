-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/ToksChain.lean: the output head's batch of row products and its three token sumchecks,
in a row.

The verifier's routine hear (OnBytes/Model/HeadHeard.lean) runs hearProducts, hearStream and
hearLogits one behind the other. Here the blocks of Cb/Pv/Head/BatTok.lean and Cb/Pv/Head/Tok.lean
are joined in that order, by the rule of Cb/Pv/Head/TokSeat.lean.

HtFrame: the letters. P is what is public before the row products are sent: it holds the norm's
point and the two points that the lookup has left, and whatever else rides. The tables of the three
sumchecks are read off P and the entries. xi is what the caller claims of nine scalars together: the
seven row products, and the scalars for the second and for the third sum. The verifier's later
claims name all of these, some in one claim, so they have one letter.

The joints. Before (htIn): what rides, and xi of the true products and of the two true sums, each
sum with its mask entry. After (seatH.out, written out by ht_out): what rides; xi of the hidden
products and of the two scalars that were sent; the hidden products add up, under the powers of the
batching element, to the hidden value of the first sumcheck's first scalar; and the output claims
of all three sumchecks hold.

ht_knowAt: the four items of soundness for the row of blocks. ht_nums: its errors are 6, then the
three written lists.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of this block (in a row of blocks: of the first block) is drawn.
That is the caller's to show.

What is not claimed: see Cb/Pv/Head/Tok.lean and Cb/Pv/Head/Batch.lean. Three things more. The two
outer seams are not here: from the joint after the sum of squares to htIn, where xi is still a
letter, and from the third sumcheck's second end value to the merge of the claims on the committed
weights. The two facts of format that a link of a chain owes are not stated. And the joints after
the second and the third sumcheck have the empty exact relation (the field rel of rest is False):
the four items of soundness do not read it, but no honest side can be had of this row of blocks as
it stands.


-/
import Cb.Pv.Head.TokSeat
import Cb.Pv.Head.BatTok
import Cb.Pv.Head.Toks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole Cb.Pv.Head.Bat

/-- The three kinds, from the slot of the first row product. -/
abbrev kV (lt sPv : ℕ) : TokKind := kindTV lt sPv
abbrev kN (lt sPv : ℕ) : TokKind := kindTN lt ((kV lt sPv).sCl + (kV lt sPv).slots)
abbrev kH (lt lPd sPv : ℕ) : TokKind := kindTH lt lPd ((kN lt sPv).sCl + (kN lt sPv).slots)

/-- The letters: see the head of this file. -/
structure HtFrame (E : Type) (lt lPd sPv : ℕ) where
  P : Type
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  msk : ℕ → J
  pv : P → Fin lt → E
  ztN : P → Fin lt → E
  ztH : P → Fin lt → E
  tabV : P → (J → E) → Fin 4 → ℕ → E
  tabN : P → (J → E) → Fin 2 → ℕ → E
  tabH : P → (J → E) → Fin 2 → ℕ → E
  Kc : Type
  M : Type
  Wp : Type
  Ex : ExtSpec
  A0 : IOR.Rels Kc P Ex (M × Wp)
  msg : M → J → E
  xi : P → (Fin 7 → E) → E → E → (J → E) → Prop

attribute [instance] HtFrame.finJ HtFrame.decJ

noncomputable section
variable {E : Type} [Field E] {lt lPd sPv : ℕ} (Fr : HtFrame E lt lPd sPv)

/-- The entries and tables of the three sumchecks, with P as what is public. -/
@[reducible] def HtFrame.wV : TokWorld E (kV lt sPv) where
  Pb := Fr.P
  J := Fr.J
  msk := Fr.msk
  tab := Fr.tabV
@[reducible] def HtFrame.wN : TokWorld E (kN lt sPv) where
  Pb := Fr.P
  J := Fr.J
  msk := Fr.msk
  tab := Fr.tabN
@[reducible] def HtFrame.wH : TokWorld E (kH lt lPd sPv) where
  Pb := Fr.P
  J := Fr.J
  msk := Fr.msk
  tab := Fr.tabH

/-- The true row products. -/
def HtFrame.prodV (x : Fr.P) (m : Fr.J → E) : Fin 7 → E :=
  fun j => trueP (kV lt sPv) Fr.wV ⟨Fr.pv x, fun _ => 0, x⟩ m j

/-- The second and the third true sum, each plus the mask entry of its first slot. -/
def HtFrame.sumN (x : Fr.P) (m : Fr.J → E) : E :=
  Blocks.ext (kN lt sPv).vars (tokAt (kN lt sPv) Fr.wN ⟨Fr.ztN x, fun _ => 1, x⟩ m)
    (Blocks.nat (TokSt.pt (k := kN lt sPv) (Pb := Fr.P) ⟨Fr.ztN x, fun _ => 1, x⟩)) +
    m (Fr.msk (kN lt sPv).sCl)
def HtFrame.sumH (x : Fr.P) (m : Fr.J → E) : E :=
  Blocks.ext (kH lt lPd sPv).vars (tokAt (kH lt lPd sPv) Fr.wH ⟨Fr.ztH x, fun _ => 1, x⟩ m)
    (Blocks.nat (TokSt.pt (k := kH lt lPd sPv) (Pb := Fr.P) ⟨Fr.ztH x, fun _ => 1, x⟩)) +
    m (Fr.msk (kH lt lPd sPv).sCl)

/-- The joint before the row of blocks. -/
def htIn : IOR.Rels Fr.Kc Fr.P Fr.Ex (Fr.M × Fr.Wp) where
  rel := fun x y w => Fr.A0.rel x y w ∧
    Fr.xi x (Fr.prodV x (Fr.msg w.1)) (Fr.sumN x (Fr.msg w.1)) (Fr.sumH x (Fr.msg w.1))
      (Fr.msg w.1)
  relR := fun a w => Fr.A0.relR a w ∧
    Fr.xi a.1 (Fr.prodV a.1 (Fr.msg w.1)) (Fr.sumN a.1 (Fr.msg w.1)) (Fr.sumH a.1 (Fr.msg w.1))
      (Fr.msg w.1)
  on := Fr.A0.on
  core := Fr.A0.core

/-- The frame of the batch with the first sumcheck: the two later sums stand at their true
values. -/
def HtFrame.btV : BtFrame E (kV lt sPv) Fr.wV where
  Kc := Fr.Kc
  M := Fr.M
  Wp := Fr.Wp
  Ex := Fr.Ex
  A0 :=
    ⟨fun x y w => Fr.A0.rel x.2 y w, fun a w => Fr.A0.relR (a.1.2, a.2) w,
      fun a => Fr.A0.on (a.1.2, a.2), Fr.A0.core⟩
  msg := Fr.msg
  phi := fun x V m => Fr.xi x.2 V (Fr.sumN x.2 m) (Fr.sumH x.2 m) m

variable [Fintype E]

/-- What the first sumcheck hands on. -/
abbrev HtFrame.X1 : Type :=
  (TokSt E (Fr.P × (Fin (kV lt sPv).np → E)) (kV lt sPv) × E) ×
    (tokT (kV lt sPv) Fr.wV.behind).par.Out

/-- What was public at the beginning, read off it. -/
def HtFrame.pub1 (x : Fr.X1) : Fr.P := x.1.1.pb.1

/-- The hidden row products, read off it and the entries. -/
def HtFrame.hidV (x : Fr.X1) (m : Fr.J → E) : Fin 7 → E := Fr.btV.bat.hid x.1.1.pb.2 m

/-- What the first sumcheck leaves beside xi: the hidden products add up, under the weights, to the
hidden value of its first scalar; and its output claims. -/
def HtFrame.leftV (x : Fr.X1) (m : Fr.J → E) : Prop :=
  ∑ j : Fin (kV lt sPv).np, x.1.1.om j * Fr.btV.bat.hid x.1.1.pb.2 m j =
      x.1.2 - m (Fr.msk (kV lt sPv).sCl) ∧
    (tokT (kV lt sPv) Fr.wV.behind).par.OutHolds x.2 m

/-- The second sumcheck behind the first. -/
@[reducible] def HtFrame.seatN : Seat E (kN lt sPv) Fr.X1 where
  J := Fr.J
  msk := Fr.msk
  zt := fun x => Fr.ztN (Fr.pub1 x)
  om := fun _ _ => 1
  tab := fun x => Fr.tabN (Fr.pub1 x)
  Kc := Fr.Kc
  M := Fr.M
  Wp := Fr.Wp
  Ex := Fr.Ex
  msg := Fr.msg
  rest :=
    ⟨fun _ _ _ => False,
      fun a w => Fr.A0.relR (Fr.pub1 a.1, a.2) w ∧ Fr.leftV a.1 (Fr.msg w.1),
      fun a => Fr.A0.on (Fr.pub1 a.1, a.2), Fr.A0.core⟩
  psi := fun x t m => Fr.xi (Fr.pub1 x) (Fr.hidV x m) t (Fr.sumH (Fr.pub1 x) m) m

/-- What the second sumcheck hands on. -/
abbrev HtFrame.X2 : Type :=
  (TokSt E Fr.X1 (kN lt sPv) × E) × (tokT (kN lt sPv) Fr.seatN.world).par.Out

/-- The third sumcheck behind the second. -/
@[reducible] def HtFrame.seatH : Seat E (kH lt lPd sPv) Fr.X2 where
  J := Fr.J
  msk := Fr.msk
  zt := fun x => Fr.ztH (Fr.pub1 x.1.1.pb)
  om := fun _ _ => 1
  tab := fun x => Fr.tabH (Fr.pub1 x.1.1.pb)
  Kc := Fr.Kc
  M := Fr.M
  Wp := Fr.Wp
  Ex := Fr.Ex
  msg := Fr.msg
  rest :=
    ⟨fun _ _ _ => False,
      fun a w => (Fr.A0.relR (Fr.pub1 a.1.1.1.pb, a.2) w ∧ Fr.leftV a.1.1.1.pb (Fr.msg w.1)) ∧
        (tokT (kN lt sPv) Fr.seatN.world).par.OutHolds a.1.2 (Fr.msg w.1),
      fun a => Fr.A0.on (Fr.pub1 a.1.1.1.pb, a.2), Fr.A0.core⟩
  psi := fun x t m => Fr.xi (Fr.pub1 x.1.1.pb) (Fr.hidV x.1.1.pb m) x.1.2 t m

/-- The batch with the first sumcheck, from P. -/
def htRV : IOR Fr.P Fr.Ex Fr.X1 Fr.Ex :=
  (btR (kV lt sPv) Fr.wV Fr.Ex).pre (fun x => some (Fr.pv x, x)) (ExtMap.id Fr.Ex)

/-- The row of blocks. -/
def htR : IOR Fr.P Fr.Ex
    ((TokSt E Fr.X2 (kH lt lPd sPv) × E) × (tokT (kH lt lPd sPv) Fr.seatH.world).par.Out) Fr.Ex :=
  ((htRV Fr).seq Fr.seatN.R).seq Fr.seatH.R

/-- Its errors. -/
def htErr : Err (htR Fr).shape :=
  Err.app
    (Err.app
      (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
        (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex))
      (tokErr (kN lt sPv) Fr.seatN.world Fr.Ex))
    (tokErr (kH lt lPd sPv) Fr.seatH.world Fr.Ex)

theorem htV_knowAt :
    KnowAt (htRV Fr) (htIn Fr) (tokOut (kV lt sPv) Fr.wV.behind Fr.btV.tok)
      (fun _ _ _ wp => wp)
      (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
        (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex)) :=
  knowAt_preMap (A' := htIn Fr) (A := batIn Fr.btV.bat) (fun x : Fr.P => (Fr.pv x, x))
    (fun _ _ h => h) (fun _ _ _ _ h => h) (bt_knowAt Fr.btV)

theorem htVN_knowAt :
    KnowAt ((htRV Fr).seq Fr.seatN.R) (htIn Fr) Fr.seatN.out (fun _ _ _ wp => wp)
      (Err.app
        (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
          (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex))
        (tokErr (kN lt sPv) Fr.seatN.world Fr.Ex)) :=
  tok_behind Fr.seatN (htV_knowAt Fr) (fun _ _ h => h)
    fun _ _ _ _ h0 h1 => ⟨h0.1, ⟨h1, h0.2.1⟩, h0.2.2⟩

/-- **The four items of soundness for the row of blocks.** -/
theorem ht_knowAt : KnowAt (htR Fr) (htIn Fr) Fr.seatH.out (fun _ _ _ wp => wp) (htErr Fr) :=
  tok_behind Fr.seatH (htVN_knowAt Fr) (fun _ _ h => h)
    fun _ _ _ _ h0 h1 => ⟨h0.1, h1, h0.2⟩

/-- What the joint after the row of blocks says. -/
theorem ht_out (b : (TokSt E Fr.X2 (kH lt lPd sPv) × E) ×
      (tokT (kH lt lPd sPv) Fr.seatH.world).par.Out) (y : Fr.Ex.Str) (w : Fr.M × Fr.Wp) :
    Fr.seatH.out.relR (b, y) w ↔
      ((Fr.A0.relR (Fr.pub1 b.1.1.pb.1.1.pb, y) w ∧ Fr.leftV b.1.1.pb.1.1.pb (Fr.msg w.1)) ∧
        (tokT (kN lt sPv) Fr.seatN.world).par.OutHolds b.1.1.pb.2 (Fr.msg w.1)) ∧
      Fr.xi (Fr.pub1 b.1.1.pb.1.1.pb) (Fr.hidV b.1.1.pb.1.1.pb (Fr.msg w.1)) b.1.1.pb.1.2 b.1.2
        (Fr.msg w.1) ∧
      (tokT (kH lt lPd sPv) Fr.seatH.world).par.OutHolds b.2 (Fr.msg w.1) :=
  Iff.rfl

/-- The errors: 6, then the three written lists. -/
theorem ht_nums : errList (htErr Fr) =
    6 :: ((kV lt sPv).errs ++ (kN lt sPv).errs ++ (kH lt lPd sPv).errs) := by
  have e3 : errList (htErr Fr) =
      errList (Err.app
        (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
          (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex))
        (tokErr (kN lt sPv) Fr.seatN.world Fr.Ex)) ++
      errList (tokErr (kH lt lPd sPv) Fr.seatH.world Fr.Ex) := errList_app _ _
  have e2 : errList (Err.app
        (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
          (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex))
        (tokErr (kN lt sPv) Fr.seatN.world Fr.Ex)) =
      errList (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
        (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex)) ++
      errList (tokErr (kN lt sPv) Fr.seatN.world Fr.Ex) := errList_app _ _
  have e1 : errList (Err.app (batErr E ((Fin (kV lt sPv).lt → E) × Fr.P) (kV lt sPv).np Fr.Ex)
        (tokErr (kV lt sPv) Fr.wV.behind Fr.Ex)) = ((kV lt sPv).np - 1) :: (kV lt sPv).errs :=
    bt_nums (k := kV lt sPv) (W := Fr.wV) Fr.Ex
  rw [e3, e2, e1, tok_nums, tok_nums]
  rfl

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.ht_knowAt
#print axioms Cb.Pv.Head.Tok.ht_nums
