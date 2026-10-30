-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/GroupRowsKept.lean: a group of sent oracle messages on which a fold begins, some of
whose main rows are kept, and its shape for the fold, with their conditions.

The data are those of a group without kept rows (`Rows`, Johnson/Top/H/GroupRows.lean) and three
more: a finite type of kept slots, which slot a main row has, if any, and which row stands in a
slot. A main row without a slot stands on the cube, at the corner that `Rows` gives it. A main row
with a slot stands at no corner: the shape (`GShape`, Cb/Ld/LdGroupFold.lean) repeats it in that
slot of every super-row, so that the fold returns it. The group, its positions, its radius and the
mask rows are those of `Rows`. Definitions, statements and proofs.
Main names:
  `RowsK S`: the data. `RowsK.Sh`: the shape, over the group `Rows.G` of the data beneath.
  `RowsK.Good`: the conditions: those of `Rows.Good`, with the two on corners of main rows asked of
    the rows without a slot alone, and: a row with a slot is the row in that slot.
  `RowsK.sh_ok`: under them the shape has its laws.
  `RowsK.list`: the group's complex has lists by the Johnson bound.
  `RowsK.hypK`: the conditions of the fold, for all rows' forms and coefficients: from
    `RowsK.Good`, `InJ` and `CountsAt` (Johnson/Top/H/StageJ.lean), at the numbers of `Rows.hypK`.
    `RowsK.hypKAt`: the same at any form on the fold's input code.
  `RowsK.rho_fix`: a code word close to an arranged word is arranged (`Reshape.Fix`), below the
    stage's distance, if that holds of every member's change of shape.
  `RowsK.good_of_rows`: the conditions from `Rows.Good` of the data beneath.
  `Rows.noKept`, `Rows.noKept_sh`, `Rows.noKept_good`: the data of `Rows` with no slot: the same
    shape, the same conditions.
  `Rows.keep R kp`: whole members are kept: each main row of a member with kp has a slot of its
    own. So it is in the layout of the verifier written after the programs: a kept member's main
    rows have no place on the cube (`GroupLayout`, OnBytes/Iop/Ground.lean).
    `Rows.KeepGood`, `Rows.keep_good`: its conditions: the corners are asked of the other members.
    `Rows.keep_card`: a super-row then has 1 + (the kept members' main rows) base rows.
Limits: that the joint radius implies each member's own (`Grp.Fits`) is not shown here; the group
is that of `Rows`, so what is shown of it there holds. `CountsAt` is asked and not proved here. That
a slot's row names that slot is not asked: two slots may hold the same row, and a slot may hold a
row that stands on the cube. A slot that holds no row cannot be written: `GShape.kept` is total.
That a kept member has no mask rows is not asked. That the program puts a member's rows in these
blocks or slots is not shown. The form that the arrangement carries (`GShape.form`) is 0 at every
corner that holds no member's row; by a reading of the programs' text theirs is not 0 on the rows of
a member's block that the member did not send. No data are written here.

-/
import Johnson.Top.H.GroupRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb

/-- A group of sent messages with kept main rows: the data. -/
structure RowsK (S : Sig GE) extends Rows S where
  /-- the kept slots -/
  Kp : Type
  [finKp : Fintype Kp]
  [decKp : DecidableEq Kp]
  /-- the slot of a main row; none: the row stands on the cube -/
  slot : (Σ a : {o // mem o}, Fin (nM a)) → Option Kp
  /-- the row in a slot -/
  kept : Kp → Σ a : {o // mem o}, Fin (nM a)

attribute [instance] RowsK.finKp RowsK.decKp

namespace RowsK
variable {S : Sig GE} (R : RowsK S)

open Classical in
/-- The row without a slot whose corner has the number i, if there is one. -/
noncomputable def rowAt (i : ℕ) : Option (Σ a : R.G.A, Fin (R.nM a)) :=
  if h : ∃ r, R.slot r = none ∧ R.atM r = i then some h.choose else none

open Classical in
/-- The shape: a row with a slot in that slot, every other row of a member in its block. -/
noncomputable def Sh : GShape R.G where
  Cb := R.s.cM
  Zb := R.s.cZ
  Kp := R.Kp
  h := R.s.h
  g := R.s.g
  Rm := fun a => Fin (R.nM a)
  Rz := fun a => Fin (R.nZ a)
  view := Reshape.fam R.view
  dst := fun r => (R.slot r).elim (Sum.inl (vtx (R.s.h + R.s.g) (R.atM r))) Sum.inr
  ord := fun b => R.rowAt (Sz.rowNo b)
  kept := R.kept
  dstZ := fun r => vtx R.s.h (R.atZ r)
  ordZ := fun b => if h : ∃ r, R.atZ r = Sz.rowNo b then some h.choose else none
  n := 2
  Ch := GE
  val := id
  AaW := Unit
  TW := R.s.cZ.T
  srcW := R.s.cZ.src
  pk := fun _ _ => 0
  Qw := fun z j => hideW R.s.h R.s.g R.s.Z.l z j.val

/-- The conditions on the data. -/
structure Good : Prop where
  sized : R.s.Sized
  view : ∀ a, (R.view a).Laws
  /-- a row with a slot is the row in that slot -/
  held : ∀ r j, R.slot r = some j → R.kept j = r
  fitM : ∀ r, R.slot r = none → R.atM r < 2 ^ (R.s.h + R.s.g)
  injM : ∀ r r', R.slot r = none → R.slot r' = none → R.atM r = R.atM r' → r = r'
  fitZ : ∀ r, R.atZ r < 2 ^ R.s.h
  injZ : Function.Injective R.atZ
  one : 1 ≤ R.s.h + R.s.g

/-- The row at the number of a row without a slot is that row. -/
theorem rowAt_atM (h : R.Good) (r : Σ a : R.G.A, Fin (R.nM a)) (hr : R.slot r = none) :
    R.rowAt (R.atM r) = some r := by
  have hex : ∃ r', R.slot r' = none ∧ R.atM r' = R.atM r := ⟨r, hr, rfl⟩
  unfold rowAt
  rw [dif_pos hex]
  exact congrArg some (h.injM _ _ hex.choose_spec.1 hr hex.choose_spec.2)

open Classical in
/-- The laws of the shape. -/
theorem sh_ok (h : R.Good) : R.Sh.OK where
  view := (ldShape_fam GE R.s.Ps R.G.A _ _ R.view h.view).1
  base := (Sg.fit_cM h.sized).laws
  mask := (Sg.fit_cZ h.sized).laws
  main := fun r => by
    have hd : R.Sh.dst r =
        (R.slot r).elim (Sum.inl (vtx (R.s.h + R.s.g) (R.atM r))) Sum.inr := rfl
    rcases hs : R.slot r with _ | j
    · rw [hs] at hd
      rw [hd]
      show R.rowAt (Sz.rowNo (vtx (R.s.h + R.s.g) (R.atM r))) = some r
      have e : Sz.rowNo (vtx (R.s.h + R.s.g) (R.atM r)) = R.atM r :=
        (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt (h.fitM r hs))
      rw [e]
      exact R.rowAt_atM h r hs
    · rw [hs] at hd
      rw [hd]
      exact h.held r j hs
  rowsZ := fun r => by
    have e : Sz.rowNo (vtx R.s.h (R.atZ r)) = R.atZ r :=
      (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt (h.fitZ r))
    have hex : ∃ r', R.atZ r' = Sz.rowNo (vtx R.s.h (R.atZ r)) := ⟨r, e.symm⟩
    show (if h : ∃ r', R.atZ r' = Sz.rowNo (vtx R.s.h (R.atZ r)) then
      some h.choose else none) = some r
    rw [dif_pos hex]
    exact congrArg some (h.injZ (hex.choose_spec.trans e))
  one := h.one

/-- The group's complex has lists by the Johnson bound. -/
theorem list (h : R.Good) (hj : InJ R.s R.e) : R.G.C.ListAt R.G.e (lstJ R.s R.e) :=
  ldGroup_list GE S R.G R.Sh R.e (lstJ R.s R.e) (R.sh_ok h)
    (listJ_of ((((Sg.fit_cM h.sized).il (Option R.Kp)).il _).pair ((Sg.fit_cZ h.sized).il _)) hj)

/-- The conditions of the fold at any form on the fold's input code. -/
theorem hypKAt {St : Type} (F : Slf GE St R.Sh.Cin.J) (h : R.Good) {bC bZ : ℕ}
    (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ) :
    (R.Sh.par.reform F).HypK R.s.d R.e (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ)
      (fun _ => bZ) := by
  have hC : Fit (R.s.cM.il (Option R.Kp)) R.s.d := (Sg.fit_cM h.sized).il _
  have hZ := Sg.fit_cZ h.sized
  have k : Spec.CodesOK GE R.s.Ps (R.s.cM.il (Option R.Kp)) R.s.cZ R.s.cZ R.s.d R.e :=
    ⟨⟨hC.laws, hZ.laws, hZ.laws⟩, ⟨hC.dist, hZ.dist, hZ.dist⟩, hj.1⟩
  have g := errOK_joh (R.Sh.par.reform F) R.s.d R.e bC bZ bZ k
    (by
      show InJohnson (Fintype.card R.s.Ps) R.s.d R.e
      rw [card_Ps]
      exact hj.2)
    ((Sg.fit_cM h.sized).mcaRows hc.main _) hc.mask hc.mask
  have e : Fintype.card R.G.P = 2 ^ R.s.C.a := card_Ps R.s
  rw [e] at g
  exact ⟨k, g, Function.injective_id, le_rfl, fun j => hideW_deg R.s.h R.s.g R.s.Z.l j.val⟩

/-- The conditions of the fold, for all rows' forms and coefficients. -/
theorem hypK {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
    (Z : Evader GE (R.G.Row B)) (h : R.Good) {bC bZ : ℕ} (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ) :
    (R.Sh.fold Sb sl Z).HypK R.s.d R.e (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ)
      (fun _ => bZ) :=
  R.hypKAt (R.Sh.form Sb sl Z) h hj hc

/-- A code word close to an arranged word is arranged, if that holds member by member. -/
theorem rho_fix (h : R.Good) {e : ℕ} (he : e < R.s.d) (hv : ∀ a, (R.view a).Fix e) :
    R.Sh.rho.Fix e :=
  (ldGroup_shape_laws GE S R.G R.Sh (R.sh_ok h)).2 R.s.d R.s.d e (Sg.fit_cM h.sized).dist he
    (Sg.fit_cZ h.sized).dist he ((ldShape_fam GE R.s.Ps R.G.A _ _ R.view h.view).2 e hv)

/-- The conditions hold if those of the group without kept rows do and each row with a slot is
the row in that slot. -/
theorem good_of_rows (h : R.toRows.Good) (hk : ∀ r j, R.slot r = some j → R.kept j = r) :
    R.Good :=
  ⟨h.sized, h.view, hk, fun r _ => h.fitM r, fun _ _ _ _ k => h.injM k, h.fitZ, h.injZ, h.one⟩

end RowsK

namespace Rows
variable {S : Sig GE} (R : Rows S)

/-- The data of a group without kept rows: no slot. -/
@[reducible] def noKept : RowsK S where
  toRows := R
  Kp := Empty
  slot := fun _ => none
  kept := fun j => j.elim

/-- The chosen witness is the same for two predicates that are equal. -/
theorem choose_same {α : Type} {p q : α → Prop} (e : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst e
  rfl

/-- With no slot the row at a number is the row that the group without kept rows has there. -/
theorem noKept_rowAt (b : Fin (R.s.h + R.s.g) → Bool) :
    R.noKept.rowAt (Sz.rowNo b) = R.Sh.ord b := by
  have p : (fun r => R.noKept.slot r = none ∧ R.atM r = Sz.rowNo b) =
      fun r => R.atM r = Sz.rowNo b :=
    funext fun r => propext ⟨fun k => k.2, fun k => ⟨rfl, k⟩⟩
  by_cases hx : ∃ r, R.atM r = Sz.rowNo b
  · have hx' : ∃ r, R.noKept.slot r = none ∧ R.atM r = Sz.rowNo b :=
      hx.elim fun r k => ⟨r, rfl, k⟩
    have a : R.noKept.rowAt (Sz.rowNo b) = some hx'.choose := by
      unfold RowsK.rowAt
      exact dif_pos hx'
    have c : R.Sh.ord b = some hx.choose := by
      unfold Rows.Sh
      exact dif_pos hx
    rw [a, c, choose_same p hx' hx]
  · have hx' : ¬ ∃ r, R.noKept.slot r = none ∧ R.atM r = Sz.rowNo b :=
      fun k => k.elim fun r k => hx ⟨r, k.2⟩
    have a : R.noKept.rowAt (Sz.rowNo b) = none := by
      unfold RowsK.rowAt
      exact dif_neg hx'
    have c : R.Sh.ord b = none := by
      unfold Rows.Sh
      exact dif_neg hx
    exact a.trans c.symm

/-- With no slot the shape is that of the group without kept rows. -/
theorem noKept_sh : R.noKept.Sh = R.Sh := by
  have e : (fun b => R.noKept.rowAt (Sz.rowNo b)) = R.Sh.ord := funext fun b => R.noKept_rowAt b
  exact congrArg (fun o => ({ R.Sh with ord := o } : GShape R.G)) e

/-- With no slot the conditions are those of the group without kept rows. -/
theorem noKept_good : R.noKept.Good ↔ R.Good :=
  ⟨fun h => ⟨h.sized, h.view, fun r => h.fitM r rfl, fun r r' k => h.injM r r' rfl rfl k, h.fitZ,
      h.injZ, h.one⟩,
    fun h => ⟨h.sized, h.view, fun _ j => j.elim, fun r _ => h.fitM r,
      fun _ _ _ _ k => h.injM k, h.fitZ, h.injZ, h.one⟩⟩

variable (kp : {o // R.mem o} → Prop) [DecidablePred kp]

/-- Whole members are kept: each main row of a member with kp has a slot of its own. -/
@[reducible] def keep : RowsK S where
  toRows := R
  Kp := Σ a : {a // kp a}, Fin (R.nM a.1)
  slot := fun r => if h : kp r.1 then some ⟨⟨r.1, h⟩, r.2⟩ else none
  kept := fun j => ⟨j.1.1, j.2⟩

/-- The conditions where whole members are kept: the corners are asked of the other members. -/
structure KeepGood : Prop where
  sized : R.s.Sized
  view : ∀ a, (R.view a).Laws
  fitM : ∀ r, ¬ kp r.1 → R.atM r < 2 ^ (R.s.h + R.s.g)
  injM : ∀ r r', ¬ kp r.1 → ¬ kp r'.1 → R.atM r = R.atM r' → r = r'
  fitZ : ∀ r, R.atZ r < 2 ^ R.s.h
  injZ : Function.Injective R.atZ
  one : 1 ≤ R.s.h + R.s.g

/-- A row of a kept member has a slot, and no other row has one. -/
theorem keep_slot_none (r : Σ a : {o // R.mem o}, Fin (R.nM a)) :
    (R.keep kp).slot r = none ↔ ¬ kp r.1 := by
  show (if h : kp r.1 then some (⟨⟨r.1, h⟩, r.2⟩ : Σ a : {a // kp a}, Fin (R.nM a.1)) else none) =
    none ↔ _
  by_cases h : kp r.1
  · simp [h]
  · simp [h]

/-- Under `KeepGood` the data with whole members kept meet `RowsK.Good`. -/
theorem keep_good (h : R.KeepGood kp) : (R.keep kp).Good where
  sized := h.sized
  view := h.view
  held := fun r j k => by
    have k' : (if h : kp r.1 then some (⟨⟨r.1, h⟩, r.2⟩ : Σ a : {a // kp a}, Fin (R.nM a.1))
      else none) = some j := k
    by_cases hk : kp r.1
    · rw [dif_pos hk] at k'
      rw [← Option.some.inj k']
    · rw [dif_neg hk] at k'
      exact absurd k' (by simp)
  fitM := fun r k => h.fitM r ((R.keep_slot_none kp r).1 k)
  injM := fun r r' k k' => h.injM r r' ((R.keep_slot_none kp r).1 k)
    ((R.keep_slot_none kp r').1 k')
  fitZ := h.fitZ
  injZ := h.injZ
  one := h.one

/-- The base rows of a super-row: one and the kept members' main rows. -/
theorem keep_card :
    Fintype.card (Option (R.keep kp).Kp) = 1 + ∑ a : {a // kp a}, R.nM a.1 := by
  rw [Fintype.card_option, Fintype.card_sigma, Nat.add_comm]
  simp

end Rows

end Johnson.Top.H
