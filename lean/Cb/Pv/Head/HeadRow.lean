-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/HeadRow.lean: the output head's own rounds behind its lookup, up to the third token
sumcheck, as one row of blocks.

Cb/Pv/Head/Norm2.lean leads from "the 17 identities of the final norm hold at every position" to the
joint after the first token sumcheck. Cb/Pv/Head/TokSeat2.lean seats two token sumchecks behind any
block. This file joins the two, in the order of the verifier's routine hear
(OnBytes/Model/HeadHeard.lean): the norm's point; nine sums and their batch; the layer of the sum of
squares with its line; seven row products and their batch; the three token sumchecks.

Letters beside those of Norm2.lean. ztN, ztH: the points over the positions that the lookup has left
for the second and the third token sumcheck. tabN, tabH: their tables. All four are read off what is
public before the norm's point is drawn. join: what the caller claims of the two scalars for the
second and the third sum. Q0: what else rides.

The joints. Before: the 17 identities hold at every position; Q0; and join of the two true sums,
each plus its mask entry (rowQ). After (written out by two_out, Cb/Pv/Head/TokSeat2.lean): the joint
after the first token sumcheck with Q0; join of the two scalars that were sent; the output claims of
the second and the third token sumcheck.

row_knowAt: the four items of soundness for the row, where 2 is not 0 in the field.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the norm's point is drawn. That is the caller's to show.

What is not claimed. As in Norm2.lean and TokSeat2.lean. What join is at the verifier's claims, and
that it follows at the true sums from what the lookup leaves, is not said here.


-/
import Cb.Pv.Head.Norm2
import Cb.Pv.Head.TokSeat2
import Cb.Pv.Head.ToksChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole Finset Inst.Model Tok

noncomputable section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E)
variable (msk : ℕ → J) (sW : ℕ) (Ex : ExtSpec) (msg : M → J → E)
variable (Q0 : IOR.Rels Kc P Ex (M × Wp)) (s : SqSize)
variable (ztN ztH : P → Fin s.lt → E) (tabN tabH : P → (J → E) → Fin 2 → ℕ → E)
variable (join : P → E → E → (J → E) → Prop)

/-- What the first token sumcheck hands on. -/
abbrev RowX1 : Type :=
  (TokSt E (SqOut limb msk sW P s × (Fin (kindTV s.lt (sPvOf sW s)).np → E))
      (kindTV s.lt (sPvOf sW s)) × E) ×
    (tokT (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind).par.Out

/-- What was public before the norm's point, read off it. -/
def rowPub (x : RowX1 (P := P) limb dig msk sW s) : P := x.1.1.pb.1.1.st.pub

/-- The two later token sumchecks behind the first. -/
@[reducible] def rowSeat :
    Seat2 E (kN s.lt (sPvOf sW s)) (kH s.lt s.lPd (sPvOf sW s))
      (RowX1 (P := P) limb dig msk sW s) where
  J := J
  msk := msk
  ztN := fun x => ztN (rowPub limb dig msk sW s x)
  ztH := fun x => ztH (rowPub limb dig msk sW s x)
  tabN := fun x => tabN (rowPub limb dig msk sW s x)
  tabH := fun x => tabH (rowPub limb dig msk sW s x)
  Kc := Kc
  M := M
  Wp := Wp
  Ex := Ex
  msg := msg
  rest := tokOut (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind
    (tvFrame np limb dig msk sW Ex msg Q0 s).tok
  join := fun x => join (rowPub limb dig msk sW s x)

/-- The two true sums, each plus the mask entry of its first slot, from what is public before the
norm's point. -/
def rowSumN (x : P) (m : J → E) : E :=
  Blocks.ext (kN s.lt (sPvOf sW s)).vars
    (tokAt (kN s.lt (sPvOf sW s)) ⟨P, J, msk, tabN⟩ ⟨ztN x, fun _ => 1, x⟩ m)
    (Blocks.nat (TokSt.pt (k := kN s.lt (sPvOf sW s)) (Pb := P) ⟨ztN x, fun _ => 1, x⟩)) +
    m (msk (kN s.lt (sPvOf sW s)).sCl)
def rowSumH (x : P) (m : J → E) : E :=
  Blocks.ext (kH s.lt s.lPd (sPvOf sW s)).vars
    (tokAt (kH s.lt s.lPd (sPvOf sW s)) ⟨P, J, msk, tabH⟩ ⟨ztH x, fun _ => 1, x⟩ m)
    (Blocks.nat (TokSt.pt (k := kH s.lt s.lPd (sPvOf sW s)) (Pb := P) ⟨ztH x, fun _ => 1, x⟩)) +
    m (msk (kH s.lt s.lPd (sPvOf sW s)).sCl)

/-- What rides from the beginning: Q0, and the caller's claim at the two true sums. -/
def rowQ : IOR.Rels Kc P Ex (M × Wp) :=
  ⟨fun x y w => Q0.rel x y w ∧
      join x (rowSumN msk sW s ztN tabN x (msg w.1)) (rowSumH msk sW s ztH tabH x (msg w.1))
        (msg w.1),
    fun a w => Q0.relR a w ∧
      join a.1 (rowSumN msk sW s ztN tabN a.1 (msg w.1)) (rowSumH msk sW s ztH tabH a.1 (msg w.1))
        (msg w.1),
    Q0.on, Q0.core⟩

/-- The row of blocks. -/
def rowR :=
  ((norm2R (P := P) limb dig msk sW Ex s).seq
    (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatN.R).seq
    (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatH.R

/-- **The four items of soundness for the row.** -/
theorem row_knowAt (h2 : (2 : E) ≠ 0) :
    KnowAt (rowR np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join)
      (pointA Ex (normD np limb dig msg s)
        (rowQ msk sW Ex msg Q0 s ztN ztH tabN tabH join) ⟨s.lt, 17⟩)
      (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatH.out
      (fun _ _ _ wp => wp)
      (Err.app
        (Err.app (norm2Err (P := P) (Kc := Kc) limb dig msk sW Ex s)
          (tokErr (kN s.lt (sPvOf sW s))
            (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatN.world Ex))
        (tokErr (kH s.lt s.lPd (sPvOf sW s))
          (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatH.world Ex)) :=
  two_behind (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join)
    (norm2_knowAt np limb dig msk sW Ex msg
      (rowQ msk sW Ex msg Q0 s ztN ztH tabN tabH join) s h2)
    (fun _ _ h => h) fun _ _ _ _ h0 h1 => ⟨⟨⟨h0.1.1, h1⟩, h0.1.2⟩, h0.2⟩

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.row_knowAt
