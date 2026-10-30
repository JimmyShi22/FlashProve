-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/Pins.lean: THE CONDITIONS UNDER WHICH TWO READINGS OF THE COMMITTED CELLS ARE
ONE
(`MaskOne`, Johnson/Road/K4/K4PinsMaskQ.lean; `CellOne`, Johnson/Road/K4/K4PinsCellQ.lean), WITH
THEIR HALVES ON THE RECORD's PART EXCHANGED FOR CONDITIONS ON THE PLAN's LETTERS ALONE. Two records,
two functions that fill the older records, and the older files' theorems called. GLUE.

  `MaskPlan A own R n m`: `MaskOne`'s four lines on the plan; and, in place of its three on the
    record: the plan's term for the mask row's message is a number o (`maskP`); the plan's list
    seats o, among own, at the seat of that member (`seatP`); the plan's shape of o gives its mask
    table no row bits (`rowBitsP`).
  `CellPlan A own R n m T r c`: `CellOne`'s lines on the plan; and, in place of its five on the
    record: the plan's two layouts are one; `whereIsP` finds o; `seatP` seats it at the member's
    seat; the row lies below 2 ^ `rowBitsP`; `BlocksOne` at `rowBitsP` and `placeBitsP`.
  `maskOne_of_plan`, `cellOne_of_plan`: UNDER `RecIs a R n m` (Johnson/Road/K4/Rec/Whole.lean) the
    new record fills the older one at the part a.
  **`mask_dataQ_plan`**, **`cell_dataQ_plan`**, **`raw_dataQ_plan`**: the older files' theorems
  under
    the new records and `RecIs`.

OBJECT: none of its own. USER: none yet; meant: whoever ties the table's item formsT m 3 "own" to
the road's sentence on the forms. LETTERS, filled by nobody: every field of `PinPlan`, own, R, n, m.

Limits. `MaskPlan` AND `CellPlan` ARE PREMISES ON THE PLAN: Props, not yet tests with code; THEY
HAVE
RUN NOWHERE. (Where this and lean/THEOREM.md differ,
the page holds.) `RecIs` IS A PREMISE HERE: `recordIsPlan` gives it under `RecMeans`. `BlocksOne`
stays a line inside `CellPlan`, now at the plan's bits. K04_law, the law of K4's block itself, IS
NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Road.K4.K4PinsMaskQ
import Johnson.Road.K4.K4PinsCellQ
import Johnson.Road.K4.Rec.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4.Rec
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls valAt laidPlace messagesAt
  keptAt szOf)
open VerifiableInference.Desc.First.FillSent (whereIsP maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP)
open VerifiableInference.Desc.Sound (dataQ)

variable {Cells : Type} (A : PinPlan Cells)

/-- **The mask row's conditions, on the plan alone.** -/
structure MaskPlan (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) where
  /-- the number, among the link's messages, of the first with mask rows -/
  mI : ℕ
  first : ((messagesAt A.D A.link).findIdx? fun x => x.shape.maskRows != 0) = some mI
  /-- it is a member of the caller's list, behind the kept ones -/
  member : (keptAt A.D A.link).length + mI < (sigListCalls A.D A.rad A.link).length
  rows : 0 < ((sigListCalls A.D A.rad A.link).get ⟨_, member⟩).1.maskRows
  /-- in place of the record's side -/
  o : ℕ
  oracle : maskP R.shape R.d m = some o
  seated : seatP own R.L.places n o = some (A.seatT ⟨_, member⟩)
  oneRow : rowBitsP R.M n o .mask = 0

/-- Under `RecIs` it fills `MaskOne`. -/
def maskOne_of_plan {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} {a : Part9}
    (H : MaskPlan A own R n m) (h : RecIs a R n m) : MaskOne A own a where
  mI := H.mI
  first := H.first
  member := H.member
  rows := H.rows
  o := H.o
  oracle := h.mask.trans H.oracle
  seated := (h.seat own H.o).trans H.seated
  oneRow := (h.rowBits H.o .mask).trans H.oneRow

/-- **The two readings of the mask row are one**, under `MaskPlan` and `RecIs`, inside the member's
mask row. -/
theorem mask_dataQ_plan {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} {a : Part9}
    (H : MaskPlan A own R n m) (h : RecIs a R n m) (t : PinM Cells) (j : ℕ)
    (hj : j < (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, H.member⟩).1).ell) :
    A.mask t j = (dataQ own a t.1).mask j :=
  mask_dataQ A own a (maskOne_of_plan A H h) t j hj

/-- **The conditions at one cell, on the plan alone.** -/
structure CellPlan (own : List (ℕ × ℕ)) (R : RecPlan) (n m T r c : ℕ) where
  bn : ℕ × String
  named : (A.D.arrayOf.getD A.link #[])[T]? = some bn
  ar : OnBytes.Params.ReqArray
  laid : OnBytes.reqArray A.D.layout bn.1 bn.2 = some ar
  rp : ℕ × ℕ
  place : laidPlace ar.blocks r c = some rp
  /-- the number of the member of the caller's list -/
  k : ℕ
  seat : seatCalls A.D A.link (.cell T r c) = some ⟨k, false, rp.1, rp.2⟩
  member : k < (sigListCalls A.D A.rad A.link).length
  rowIn : rp.1 < ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1.mainRows
  placeIn : rp.2 < (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1).ell
  /-- in place of the record's side -/
  layout : R.layout = A.D.layout
  o : ℕ
  oracle : whereIsP R.d m bn.1 ar.message = some o
  seated : seatP own R.L.places n o = some (A.seatT ⟨k, member⟩)
  rowBelow : rp.1 < 2 ^ rowBitsP R.M n o .main
  blocks : BlocksOne ar.blocks (rowBitsP R.M n o .main) (placeBitsP R.cs R.M n o .main)

/-- Under `RecIs` it fills `CellOne`. -/
def cellOne_of_plan {own : List (ℕ × ℕ)} {R : RecPlan} {n m T r c : ℕ} {a : Part9}
    (H : CellPlan A own R n m T r c) (h : RecIs a R n m) : CellOne A own a T r c where
  bn := H.bn
  named := H.named
  ar := H.ar
  laid := H.laid
  rp := H.rp
  place := H.place
  k := H.k
  seat := H.seat
  member := H.member
  rowIn := H.rowIn
  placeIn := H.placeIn
  layout := h.layout.trans H.layout
  o := H.o
  oracle := (h.whereIs H.bn.1 H.ar.message).trans H.oracle
  seated := (h.seat own H.o).trans H.seated
  rowBelow := by
    rw [h.rowBits H.o .main]
    exact H.rowBelow
  blocks := by
    rw [h.rowBits H.o .main, h.placeBits H.o .main]
    exact H.blocks

/-- **The two readings of a cell are one**, under `CellPlan` and `RecIs`. -/
theorem cell_dataQ_plan {own : List (ℕ × ℕ)} {R : RecPlan} {n m T r c : ℕ} {a : Part9}
    (H : CellPlan A own R n m T r c) (h : RecIs a R n m) (t : PinM Cells) :
    (valAt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) (A.tuple t)
      (.cell T r c)).getD 0 = (dataQ own a t.1).cell H.bn.1 H.bn.2 r c :=
  cell_dataQ A own a T r c (cellOne_of_plan A H h) t

/-- **The value's raw matrices are made of `dataQ`'s cells**, under `CellPlan` at every symbol of
tl's sizes and `RecIs`. -/
theorem raw_dataQ_plan (tl : HTailF2) {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} {a : Part9}
    (H : ∀ (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)), CellPlan A own R n m (tl.gtTree.getD μ.val 0) i.val c'.val)
    (h : RecIs a R n m) (t : PinM Cells) : A.raw tl t = matsOfB A tl (dataQ own a t.1) :=
  raw_dataQ A tl own a (fun μ i c' => cellOne_of_plan A (H μ i c') h) t

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.mask_dataQ_plan
#print axioms OnBytes.Road.K4.Rec.cell_dataQ_plan
#print axioms OnBytes.Road.K4.Rec.raw_dataQ_plan
