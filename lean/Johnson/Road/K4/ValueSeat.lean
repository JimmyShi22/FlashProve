-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ValueSeat.lean: THE VALUE OF Johnson/Road/K4/ValueSlots.lean AT A SEAT OF K4's TEXT:
the statement in front is K4's part T of the carried record; what the lookup left is read off it
(Johnson/Road/K4/LookLeft.lean); the cells are entries of the segment's committed matrices, at the
Road's own addresses. Four definitions, a record and six theorems.

  `addrOf y D q`: the matrix, row and column at which the cell named q lies: the address inside
    `cellsOf D (cellsAt y M)` (Johnson/Road/FormsKeysFits.lean, FormsKeysMat.lean). `cellsOf_addr`.
  `Plan4K M T`: the letters that stay: the layout y, the sizes D, the tables tb, the first layer L0;
    bounds nM nR nC on the matrices' numbers, rows and columns, and how a tuple of messages is read
    as matrices (`mats`), as the own mask row, as the committed matrix of weights and as the
    index-mask message; the seat L; the first free slot n0; the numbers and numberings of end values
    and weight claims; the conditions on sizes.
  `Plan4K.toL : Plan4L Cb.Gl.E M T`, `Plan4K.plan : Plan4 Cb.Gl.E M T`: the value.
  `zOf_look`, `kTg_look`, `kIncS_look`: where the seat holds the lookup's return fo, the three
    letters are `zAt fo`, `kTgAt fo (L.fork x)`, `kIncAt fo (L.fork x)`.
  `cells_eq`: if the matrices read as 0 outside the bounds, the value's cells are
    `cellsOf D (cellsAt y (mats m))`: the cells of which the Road's laws on true reads speak.
  `keys_iff`: where the seat holds fo, and fo's end form names no entry of a virtual row and only
    slots up to ns: `Keys x m` says: the sum over the calls of weight times KF at the lookup's point
    is `keysPub fo` less the end form's value in the ledger's world at the own mask row.

Limits. A cell whose address is outside the bounds reads as 0; a name that is not valid reads as
whatever stands at its address. NOTHING HERE SAYS THAT THE LETTERS ARE A PLAN's: y, D, tb, L0, the
bounds, n0 and the numberings are tied to nothing. That a tuple of messages is what the statement's
oracles decode to is the table of joints' matter. Those of Value.lean, ValueSlots.lean,
LookLeft.lean.
-/
import Johnson.Road.K4.ValueSlots
import Johnson.Road.K4.ValueSays
import Johnson.Road.K4.LookLeft
import Johnson.Road.FormsKeysMat
import Johnson.Road.FormsKeysFits
import OnBytes.Desc.First.K4.Steps
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes.Model (Reading Fork Forest.Heard)
open OnBytes.Model.Layer (Lay)
open OnBytes.Desc.First.K4 (Seat)
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.FFSeg (Dim Cell lF lFe wc KF)

noncomputable section

/-- The matrix, row and column at which a cell lies. -/
def addrOf (y : Lay) (D : Dim) (q : Cell) : ℕ × ℕ × ℕ :=
  (firstM y (mxNo q.X.mx) +
      Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) / colsM y (mxNo q.X.mx),
    Inst.Model.FFSeg.feat D q.X q.k q.inst q.j % fcM y (mxNo q.X.mx) * y.T + q.i,
    Inst.Model.FFSeg.feat D q.X q.k q.inst q.j / fcM y (mxNo q.X.mx) % colsM y (mxNo q.X.mx))

theorem cellsOf_addr {K : Type} (y : Lay) (D : Dim) (Mt : Mats K) (q : Cell) :
    cellsOf D (cellsAt y Mt) q = Mt (addrOf y D q).1 (addrOf y D q).2.1 (addrOf y D q).2.2 := rfl

/-- The letters that stay at a seat. -/
structure Plan4K (M T : Type) [scl : Scl] where
  y : Lay
  D : Dim
  tb : Tables
  L0 : ℕ
  /-- bounds on the matrices' numbers, rows and columns; the messages as matrices -/
  nM : ℕ
  nR : ℕ
  nC : ℕ
  mats : M → Mats Cb.Gl.E
  ns : ℕ
  kW : ℕ
  hW : ℕ
  nx : ℕ
  maskAt : M → ℕ → Cb.Gl.E
  matAt : M → ℕ → ℕ → Cb.Gl.E
  idxAt : M → ℕ → Cb.Gl.E
  /-- how K4's text reads its part of the carried record -/
  L : Seat T
  n0 : ℕ
  nT : ℕ
  nI : ℕ
  v7 : ℕ
  numT : ShA D → ℕ
  numI : IA D ⊕ IB D → ℕ
  nW : ℕ
  num : Fin nW ≃ Piece D
  h5 : 9 ≤ D.lL + lF D + D.lT
  h6 : 9 ≤ D.lL - 1 + (lFe D + D.lT)
  hfe : D.fe ≤ D.f
  h0 : L0 % 2 = 0
  hf : D.f = 2 * D.fe
  hh : D.P.nq + D.P.nkv ≤ 64
  hLay : L0 + D.nl ≤ D.P.layers
  hH : off kW (units D.P) (units D.P).length ≤ hW

variable [scl : Scl] {M T : Type}

namespace Plan4K
variable (Q : Plan4K M T)

/-- A cell's name: its address, if inside the bounds. -/
def nameOf (q : Cell) : Option (Fin Q.nM × Fin Q.nR × Fin Q.nC) :=
  if h : (addrOf Q.y Q.D q).1 < Q.nM ∧ (addrOf Q.y Q.D q).2.1 < Q.nR ∧
      (addrOf Q.y Q.D q).2.2 < Q.nC then
    some (⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩)
  else none

/-- The letters of ValueSlots.lean. -/
def toL : Plan4L Cb.Gl.E M T where
  D := Q.D
  tb := Q.tb
  L0 := Q.L0
  Jc := Fin Q.nM × Fin Q.nR × Fin Q.nC
  nameOf := Q.nameOf
  ns := Q.ns
  kW := Q.kW
  hW := Q.hW
  nx := Q.nx
  cellAt := fun m j => Q.mats m j.1 j.2.1 j.2.2
  maskAt := Q.maskAt
  matAt := Q.matAt
  idxAt := Q.idxAt
  two := Cb.Pv.Head.gl_two_ne_zero
  zOf := fun x => match Q.L.look x with
    | some fo => zAt fo
    | none => fun _ => 0
  kTg := fun x => match Q.L.look x with
    | some fo => kTgAt fo (Q.L.fork x)
    | none => 0
  kIncS := fun x => match Q.L.look x with
    | some fo => kIncAt fo (Q.L.fork x)
    | none => fun _ => 0
  n0 := Q.n0
  nT := Q.nT
  nI := Q.nI
  v7 := Q.v7
  numT := Q.numT
  numI := Q.numI
  nW := Q.nW
  num := Q.num
  h5 := Q.h5
  h6 := Q.h6
  hfe := Q.hfe
  h0 := Q.h0
  hf := Q.hf
  hh := Q.hh
  hLay := Q.hLay
  hH := Q.hH

/-- The letters of Value.lean. -/
def plan : Plan4 Cb.Gl.E M T := Q.toL.plan

theorem zOf_look {x : T} {fo : Forest.Heard} (h : Q.L.look x = some fo) :
    Q.plan.zOf x = zAt fo := by
  show (match Q.L.look x with
    | some fo => zAt fo
    | none => fun _ => 0) = _
  rw [h]

theorem kTg_look {x : T} {fo : Forest.Heard} (h : Q.L.look x = some fo) :
    Q.plan.kTg x = kTgAt fo (Q.L.fork x) := by
  show (match Q.L.look x with
    | some fo => kTgAt fo (Q.L.fork x)
    | none => 0) = _
  rw [h]

theorem kIncS_look {x : T} {fo : Forest.Heard} (h : Q.L.look x = some fo) :
    Q.plan.kIncS x = kIncAt fo (Q.L.fork x) := by
  show (match Q.L.look x with
    | some fo => kIncAt fo (Q.L.fork x)
    | none => fun _ => 0) = _
  rw [h]

/-- **The value's cells are the Road's**, if the matrices read as 0 outside the bounds. -/
theorem cells_eq (m : M)
    (hz : ∀ a b c, ¬ (a < Q.nM ∧ b < Q.nR ∧ c < Q.nC) → Q.mats m a b c = 0) :
    Q.plan.cells m = cellsOf Q.D (cellsAt Q.y (Q.mats m)) := by
  funext q
  rw [cellsOf_addr]
  by_cases h : (addrOf Q.y Q.D q).1 < Q.nM ∧ (addrOf Q.y Q.D q).2.1 < Q.nR ∧
      (addrOf Q.y Q.D q).2.2 < Q.nC
  · have e : Q.plan.nameOf q = some (⟨_, h.1⟩, ⟨_, h.2.1⟩, ⟨_, h.2.2⟩) := dif_pos h
    exact Q.plan.rd_valid (Q.plan.msg m) e
  · have e : Q.plan.nameOf q = none := dif_neg h
    rw [hz _ _ _ h]
    exact Q.plan.rd_invalid (Q.plan.msg m) e

/-- **What `Keys` says at a seat that holds the lookup's return.** -/
theorem keys_iff {x : T} {fo : Forest.Heard} (h : Q.L.look x = some fo) (m : M)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (he : fo.cEnd.ents = #[])
    (hs : ∀ s ∈ fo.cEnd.slots.toList, s.1 < Q.ns + 1) :
    Q.plan.Keys x m ↔
      ∑ c, wc Q.D (zAt fo) c *
          KF Q.D (Q.plan.cells m) Q.tb Q.L0 (Q.plan.weights m) (zAt fo) c =
        keysPub fo -
          fo.cEnd.value Reading.gl ((Q.L.fork x).worldOf Reading.gl (Q.maskAt m) entry) := by
  unfold Plan4.Keys
  rw [Q.zOf_look h, Q.kTg_look h, Q.kIncS_look h]
  exact Eq.congr_right (kEnd_at fo (Q.L.fork x) (Q.ns + 1) (Q.maskAt m) entry he hs)

end Plan4K
end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.cells_eq
#print axioms OnBytes.Road.K4.Plan4K.keys_iff
