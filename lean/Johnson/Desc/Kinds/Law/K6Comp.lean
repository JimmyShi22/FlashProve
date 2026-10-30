-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Comp.lean: THE FORM OF THE COMPONENTS THAT K6's RULE READS, OFF THE TABLE's
WITNESS, WITH THE CELLS BY THE LIBRARY's OWN MAP: comp w := (K6's record of cells MADE OF Hd.cellsH
h L b (own w), the weights off the stored table's cells; the mask row): own w : THE SEGMENT's
MATRICES IN INTEGERS, a letter here, meant to be ownQ … w 24 (the integers whose packing the
committed symbols are, read through the one accessor). SO THE EQUATION "THE LIBRARY's RECORD MADE OF
K6's CELLS IS Hd.cellsH h L b (own w)" HOLDS BY MAKE, FOR EVERY own, A CONSTANT ONE TOO: THE DEBT IS
NOT PAID BY IT BUT MOVED, WHOLE, INTO THE ONE LETTER own: that own w IS what the committed symbols
spell is still owed, through ownQ (Johnson/P5J/CellQ.lean): STATED AND PROVED.
  cellsBack t Wh K6's record of cells made of the library's: the inverse of Law/LibJoinNorm.lean's
      cellsN: cellsN_back (rfl).
  ReadAlike two witnesses read alike through the one accessor at every member of ms, inside its
      ranges.
  compOf             the form.     comp_cells : cellsN (compOf … w).1 = Hd.cellsH h L b (own w).
  readsPinnedW_comp where own and the mask row read pinned places alone (each: alike witnesses give
      one value), compOf has Law/K6OwnW.lean's ReadsPinnedW: K6's HALF OF (pin) COMES DOWN
      TO THESE TWO SENTENCES ON own AND mask.
  k06_whole_own Law/K06Means.lean's assembly at one record, at compOf: its conclusion is
      Policy.HeadCl (Hd.npOf W.hS) (polOf W.hS) Wz x (Hd.cellsH W.hS L b (own w)): the middle clause
      of HeadOrdLB at Mh := own w, TO THE LETTER where b = borderOf y.
WHAT IT DOES NOT SAY. **own, wh AND mask ARE LETTERS**: that own := ownQ … w 24 reads pinned places
alone is Law/K6Own24.lean's ownQ_alike, under conditions on public letters. The silly fillings
(constants) stay. Where the committed symbols are no packing of small integers
ownQ is 0 in that column (its own limit): the item "constr 4 small" says that they are one. All that
Law/K6OwnW.lean and Law/K06Means.lean do not say. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6OwnW
import Johnson.Desc.Kinds.Law.K06Means

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Inst.Model (ppref Instance)
open OnBytes.Road (Mats)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Mem MsgT memTab InMsg)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)

/-- **K6's record of cells made of the library's.** -/
def cellsBack (t : Inst.Model.Head.Cells Int) (Wh : Nat → Nat → Int) : NCells where
  cell := fun M f i =>
    match M with
    | .wide => t.hf f i
    | .act => t.hd f i
    | .row => t.hr f i
  Wh := Wh
  stream := t.x

theorem cellsN_back (t : Inst.Model.Head.Cells Int) (Wh : Nat → Nat → Int) :
    cellsN (cellsBack t Wh) = t := rfl

variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : Nat → Nat → Nat) (ms : List Mem)

/-- Two witnesses read alike through the one accessor at every member of ms, inside its ranges. -/
def ReadAlike (w w' : Wit Cells Tok MsgT) : Prop :=
  ∀ x ∈ ms, ∀ mask row place, InMsg cs (x.1.l.get x.2).1 mask row place →
    memTab cs arr w x mask row place = memTab cs arr w' x mask row place

variable (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL) (b : OnBytes.Model.Head.Border)
  (own : Wit Cells Tok MsgT → Mats Int) (wh : Cells → Nat → Nat → Int)
  (mask : Wit Cells Tok MsgT → Nat → E)

/-- **The form of the components.** -/
def compOf (w : Wit Cells Tok MsgT) : Pinned :=
  (cellsBack (OnBytes.Road.Hd.cellsH h L b (own w)) (wh w.cells), mask w)

namespace Came

/-- The library's record made of K6's cells is Hd.cellsH at own w: by make, whatever own is. -/
theorem comp_cells (w : Wit Cells Tok MsgT) :
    cellsN (compOf h L b own wh mask w).1 = OnBytes.Road.Hd.cellsH h L b (own w) := rfl

/-- **This kind's half of (pin) comes down to two sentences on own and mask.** -/
theorem readsPinnedW_comp (hown : ∀ w w', ReadAlike cs arr ms w w' → own w = own w')
    (hmask : ∀ w w', ReadAlike cs arr ms w w' → mask w = mask w') :
    ReadsPinnedW cs arr ms (compOf h L b own wh mask) := by
  intro w w' hA hc
  unfold compOf
  rw [hown w w' hA, hmask w w' hA, hc]

/-- **THE ASSEMBLY AT ONE RECORD, AT THE SEGMENT's OWN INTEGERS.** -/
theorem k06_whole_own (W : OnBytes.Model.Verify.Public) (s : S) (y : Nat) (x : Instance ppref)
    (Wz : Inst.Model.Mat) (tab : Nat → Nat) (w : Wit Cells Tok MsgT) (hon : K6On W s)
    (hin : K6In W s (compOf W.hS L b own wh mask w))
    (hy : Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y)
    (hlook : LookCallsAt W tab s y (compOf W.hS L b own wh mask w).1)
    (hrider : RiderAt W s y (compOf W.hS L b own wh mask w).1)
    (hsmall : ∀ m f t, ((compOf W.hS L b own wh mask w).1.cell m f t).natAbs < 2 ^ 18)
    (hsmallS : ∀ f t, ((compOf W.hS L b own wh mask w).1.stream f t).natAbs < 2 ^ 18)
    (hF : FullH W.hS) (h8 : W.hS.digSh = 8) (hr : s.rowR = x.r) (he : s.rowE = x.e)
    (htok : ∀ t, t < 1024 → s.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : wh w.cells = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf W.hS) (OnBytes.Road.Hd.polOf W.hS) Wz x
      (OnBytes.Road.Hd.cellsH W.hS L b (own w)) :=
  k06_whole W s y x Wz tab (compOf W.hS L b own wh mask w) hon hin hy hlook hrider hsmall hsmallS
    hF h8 hr he htok hyx htab hW

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.comp_cells
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readsPinnedW_comp
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole_own
