-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/GroupRows.lean: a group of sent oracle messages on which a proximity test begins,
and its shape for the first fold, for any signature and any number of members, with their
conditions.

A member's code, read at the group's positions, is rows under the main code beside rows under the
mask code of the test's first stage (`Sg`, OnBytes/Slice/Stage.lean), up to a change of shape that
is given member by member (`Reshape`, Cb/Ld/LdBatShape.lean). A mask row has a symbol at each
position of the stage (`Sg.cZ`: `ldRep`, OnBytes/Slice/LinkAt.lean): in a tree of the programs
every leaf holds its own copy. Each member's rows stand in a block of the cube. The fold has a
public weight on each entry of the fresh mask row (`hideW` at `s.Z.l`,
OnBytes/Slice/FoldPeel.lean). The records are `Grp` (Cb/Ld/LdBatSig.lean) and `GShape`
(Cb/Ld/LdGroupFold.lean). Definitions, statements and proofs.
Main names:
  `Rows S`: the data: the stage, the radius, the members, where each is read, its numbers of rows,
    the first corners of its blocks, its change of shape.
  `Rows.G`, `Rows.Sh`: the group; the shape: no kept slot; row i of a member at the corner with
    the number (first corner + i), the lowest digit first (`vtx`, OnBytes/Slice/KeyPlaces.lean).
  `Rows.Good`: the conditions on these data. `Rows.sh_ok`: under them the shape has its laws.
  `Rows.list`: the group's complex has lists by the Johnson bound (`ldGroup_list`).
  `Rows.hypK`: the conditions of the first fold, for all rows' forms and coefficients: from
    `Rows.Good`, `InJ` and `CountsAt` (Johnson/Top/H/StageJ.lean).
Limits: that the joint radius implies each member's own (`Grp.Fits`) is not shown here. `CountsAt`
is asked and not proved here. A group with kept slots is not treated. That the program puts a
member's rows in these blocks is not shown. The form that the arrangement carries (`GShape.form`)
is 0 at every corner that holds no member's row; by a reading of the programs' text theirs is not
0 on the rows of a member's block that the member did not send. The stages at any form are in
Johnson/Top/H/FirstAt.lean.

-/
import Cb.Ld.LdGroupFoldProofs
import Cb.Ld.LdBatShapeProofs
import Cb.Ent.TowerKnow
import OnBytes.Slice.KeyPlaces
import Johnson.Top.H.StageJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb

/-- A group of sent messages: the data. -/
structure Rows (S : Sig GE) where
  /-- the first stage of the test -/
  s : Sg
  /-- the joint radius -/
  e : ℕ
  mem : S.O → Prop
  [decMem : DecidablePred mem]
  /-- where a member is read for a position of the stage -/
  pos : ∀ a : {o // mem o}, s.Ps → (S.om a.1).P
  /-- a member's main rows and mask rows -/
  nM : {o // mem o} → ℕ
  nZ : {o // mem o} → ℕ
  /-- the first corners of its two blocks -/
  oM : {o // mem o} → ℕ
  oZ : {o // mem o} → ℕ
  /-- its code as read is rows under the two codes -/
  view : ∀ a, Reshape ((S.om a.1).C.atPos (pos a))
    ((s.cM.il (Fin (nM a))).pair (s.cZ.il (Fin (nZ a))))

attribute [instance] Rows.decMem

namespace Rows
variable {S : Sig GE} (R : Rows S)

/-- The group. -/
@[reducible] def G : Grp S where
  P := R.s.Ps
  mem := R.mem
  pos := R.pos
  e := R.e

instance : Nonempty R.G.P := ⟨⟨0, Nat.two_pow_pos _⟩⟩

/-- The corner's number of a main row, and of a mask row. -/
def atM (r : Σ a : R.G.A, Fin (R.nM a)) : ℕ := R.oM r.1 + r.2.val
def atZ (r : Σ a : R.G.A, Fin (R.nZ a)) : ℕ := R.oZ r.1 + r.2.val

open Classical in
/-- The shape: no kept slot; each member's rows in its blocks. -/
noncomputable def Sh : GShape R.G where
  Cb := R.s.cM
  Zb := R.s.cZ
  Kp := Empty
  h := R.s.h
  g := R.s.g
  Rm := fun a => Fin (R.nM a)
  Rz := fun a => Fin (R.nZ a)
  view := Reshape.fam R.view
  dst := fun r => Sum.inl (vtx (R.s.h + R.s.g) (R.atM r))
  ord := fun b => if h : ∃ r, R.atM r = Sz.rowNo b then some h.choose else none
  kept := fun j => j.elim
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
  fitM : ∀ r, R.atM r < 2 ^ (R.s.h + R.s.g)
  injM : Function.Injective R.atM
  fitZ : ∀ r, R.atZ r < 2 ^ R.s.h
  injZ : Function.Injective R.atZ
  one : 1 ≤ R.s.h + R.s.g

open Classical in
/-- The laws of the shape. -/
theorem sh_ok (h : R.Good) : R.Sh.OK where
  view := (ldShape_fam GE R.s.Ps R.G.A _ _ R.view h.view).1
  base := (Sg.fit_cM h.sized).laws
  mask := (Sg.fit_cZ h.sized).laws
  main := fun r => by
    have e : Sz.rowNo (vtx (R.s.h + R.s.g) (R.atM r)) = R.atM r :=
      (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt (h.fitM r))
    have hex : ∃ r', R.atM r' = Sz.rowNo (vtx (R.s.h + R.s.g) (R.atM r)) := ⟨r, e.symm⟩
    show (if h : ∃ r', R.atM r' = Sz.rowNo (vtx (R.s.h + R.s.g) (R.atM r)) then
      some h.choose else none) = some r
    rw [dif_pos hex]
    exact congrArg some (h.injM (hex.choose_spec.trans e))
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
    (listJ_of ((((Sg.fit_cM h.sized).il (Option Empty)).il _).pair ((Sg.fit_cZ h.sized).il _)) hj)

/-- The conditions of the first fold, for all rows' forms and coefficients. -/
theorem hypK {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
    (Z : Evader GE (R.G.Row B)) (h : R.Good) {bC bZ : ℕ} (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ) :
    (R.Sh.fold Sb sl Z).HypK R.s.d R.e (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ)
      (fun _ => bZ) := by
  have hC : Fit (R.s.cM.il (Option Empty)) R.s.d := (Sg.fit_cM h.sized).il _
  have hZ := Sg.fit_cZ h.sized
  have k : Spec.CodesOK GE R.s.Ps (R.s.cM.il (Option Empty)) R.s.cZ R.s.cZ R.s.d R.e :=
    ⟨⟨hC.laws, hZ.laws, hZ.laws⟩, ⟨hC.dist, hZ.dist, hZ.dist⟩, hj.1⟩
  have g := errOK_joh (R.Sh.fold Sb sl Z) R.s.d R.e bC bZ bZ k
    (by
      show InJohnson (Fintype.card R.s.Ps) R.s.d R.e
      rw [card_Ps]
      exact hj.2)
    ((Sg.fit_cM h.sized).mcaRows hc.main _) hc.mask hc.mask
  have e : Fintype.card R.G.P = 2 ^ R.s.C.a := card_Ps R.s
  rw [e] at g
  exact ⟨k, g, Function.injective_id, le_rfl, fun j => hideW_deg R.s.h R.s.g R.s.Z.l j.val⟩

end Rows

end Johnson.Top.H

#print axioms Johnson.Top.H.Rows.sh_ok
#print axioms Johnson.Top.H.Rows.list
#print axioms Johnson.Top.H.Rows.hypK
