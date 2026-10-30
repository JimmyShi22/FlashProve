-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/Arrays.lean: THE CONDITIONS AT A CELL (`CellPlan`,
Johnson/Road/K4/Rec/Pins.lean) ASKED AN ARRAY AT A TIME. Of `CellPlan`'s fields eleven hang on the
array alone; six hang on the cell, and follow from the array's and from a test on the array's
blocks. A walk over every symbol cannot be evaluated at the full size; a walk over arrays and their
blocks can. Definitions with code, a Lean structure, statements and proofs. GLUE: THE COUNTING AND
THE ARITHMETIC ARE CALLED, NOT TYPED: `blocksB` and `laidPlace_some`
(Johnson/Desc/First/Look/K3CallerLaid.lean: under the test every element of the array has a place,
and the place lies in the table); `blocksOneB` (Johnson/Road/K4/MaskCellBools.lean).

  `memberNo D i bn ar`: the number, in the caller's list, of the message that holds an array:
    `seatCalls`' own term (Johnson/Desc/First/Look/K3CallerAtt.lean). `seatCalls_cell`.
  `ArrayPlan A own R n m T I K`: the eleven fields; the member's number; the caller's I rows and K
    columns are at most the layout's array's; `blocksB` at the array's blocks and sizes, at the
    lesser of the member's number of main rows and 2 ^ the plan's row bits, and the member's length.
  `arrayPlanB`, `arrayPlan_of_B`: THE TEST, AN ARRAY AT A TIME; a yes gives the structure.
  **`cellPlan_of_array`**: `ArrayPlan`, r < I, c < K: there is a `CellPlan` at (r, c).
  `arraysPlanB A tl own R n m`: the walk over tl's matrices.
  **`raw_dataQ_arrays`**: a yes of `arraysPlanB`, `RecIs a R n m`: `A.raw tl t = matsOfB A tl (dataQ
    own a t.1)`.

OBJECT: none of its own. USER: none yet; meant: the sheet that evaluates the conditions of K4's row
at the real plan. LETTERS, filled by nobody: every field of `PinPlan`, tl, own, R, n, m.

Limits. NOTHING IS EVALUATED HERE. `RecIs` IS A PREMISE HERE. ONE DIRECTION: a yes gives the
structure. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3CallerLaid
import Johnson.Road.K4.MaskCellBools
import Johnson.Road.K4.Rec.Pins

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqArray)
open Johnson.Road.K4.SeamBools (blocksOneB blocksOne_of_B)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls laidPlace keptAt bornAt szOf
  blocksB laidPlace_some)
open VerifiableInference.Desc.First.FillSent (whereIsP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP)
open VerifiableInference.Desc.Sound (dataQ)

/-! ## The member's number -/

/-- The number, in the caller's list, of the message that holds the array. -/
def memberNo (D : Sent) (i : ℕ) (bn : ℕ × String) (ar : ReqArray) : Option ℕ :=
  if bn.1 == i then some ((keptAt D i).length + ar.message)
  else (bornAt D i).idxOf? (bn.1, ar.message)

/-- The seat of a cell, where the array, its member's number and the cell's place are known. -/
theorem seatCalls_cell {D : Sent} {i T r c k : ℕ} {bn : ℕ × String} {ar : ReqArray} {rp : ℕ × ℕ}
    (h1 : (D.arrayOf.getD i #[])[T]? = some bn) (h2 : OnBytes.reqArray D.layout bn.1 bn.2 = some ar)
    (h3 : laidPlace ar.blocks r c = some rp) (h4 : memberNo D i bn ar = some k) :
    seatCalls D i (.cell T r c) = some ⟨k, false, rp.1, rp.2⟩ := by
  simp only [seatCalls, h1, h2, h3, Option.bind_some]
  unfold memberNo at h4
  split at h4
  · rename_i e
    obtain rfl := Option.some.inj h4
    rw [if_pos e]
  · rename_i e
    rw [if_neg e, h4]
    rfl

/-! ## An array -/

variable {Cells : Type} (A : PinPlan Cells)

/-- **The conditions at an array, on the plan alone.** I, K: the caller's rows and columns. -/
structure ArrayPlan (own : List (ℕ × ℕ)) (R : RecPlan) (n m T I K : ℕ) where
  bn : ℕ × String
  named : (A.D.arrayOf.getD A.link #[])[T]? = some bn
  ar : ReqArray
  laid : OnBytes.reqArray A.D.layout bn.1 bn.2 = some ar
  /-- the number of the member of the caller's list -/
  k : ℕ
  no : memberNo A.D A.link bn ar = some k
  member : k < (sigListCalls A.D A.rad A.link).length
  layout : R.layout = A.D.layout
  o : ℕ
  oracle : whereIsP R.d m bn.1 ar.message = some o
  seated : seatP own R.L.places n o = some (A.seatT ⟨k, member⟩)
  blocks : BlocksOne ar.blocks (rowBitsP R.M n o .main) (placeBitsP R.cs R.M n o .main)
  rowsFit : I ≤ ar.sizeI
  colsFit : K ≤ ar.sizeC
  tiled : blocksB ar.blocks ar.sizeI ar.sizeC
    (min ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1.mainRows (2 ^ rowBitsP R.M n o .main))
    (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1).ell = true

/-- **The test, an array at a time.** -/
def arrayPlanB (own : List (ℕ × ℕ)) (R : RecPlan) (n m T I K : ℕ) : Bool :=
  match (A.D.arrayOf.getD A.link #[])[T]? with
  | none => false
  | some bn =>
    match OnBytes.reqArray A.D.layout bn.1 bn.2 with
    | none => false
    | some ar =>
      match memberNo A.D A.link bn ar with
      | none => false
      | some k =>
        if member : k < (sigListCalls A.D A.rad A.link).length then
          decide (R.layout = A.D.layout) &&
            match whereIsP R.d m bn.1 ar.message with
            | none => false
            | some o =>
              decide (seatP own R.L.places n o = some (A.seatT ⟨k, member⟩)) &&
                blocksOneB ar.blocks (rowBitsP R.M n o .main) (placeBitsP R.cs R.M n o .main) &&
                decide (I ≤ ar.sizeI) && decide (K ≤ ar.sizeC) &&
                blocksB ar.blocks ar.sizeI ar.sizeC
                  (min ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1.mainRows
                    (2 ^ rowBitsP R.M n o .main))
                  (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨k, member⟩).1).ell
        else false

/-- **A yes gives the structure.** -/
theorem arrayPlan_of_B {own : List (ℕ × ℕ)} {R : RecPlan} {n m T I K : ℕ}
    (h : arrayPlanB A own R n m T I K = true) : Nonempty (ArrayPlan A own R n m T I K) := by
  unfold arrayPlanB at h
  split at h
  · cases h
  · rename_i bn hbn
    split at h
    · cases h
    · rename_i ar har
      split at h
      · cases h
      · rename_i k hk
        split at h
        · rename_i member
          rw [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨h1, h⟩ := h
          split at h
          · cases h
          · rename_i o ho
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact ⟨⟨bn, hbn, ar, har, k, hk, member, h1, o, ho, h.1.1.1.1,
              blocksOne_of_B h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩⟩
        · cases h

/-- **The array's structure gives a cell's, at every cell of the caller's sizes.** -/
theorem cellPlan_of_array {own : List (ℕ × ℕ)} {R : RecPlan} {n m T I K r c : ℕ}
    (H : ArrayPlan A own R n m T I K) (hr : r < I) (hc : c < K) :
    Nonempty (CellPlan A own R n m T r c) := by
  obtain ⟨rp, hp, h1, h2⟩ := laidPlace_some H.tiled (Nat.lt_of_lt_of_le hr H.rowsFit)
    (Nat.lt_of_lt_of_le hc H.colsFit)
  exact ⟨{ bn := H.bn
           named := H.named
           ar := H.ar
           laid := H.laid
           rp := rp
           place := hp
           k := H.k
           seat := seatCalls_cell H.named H.laid hp H.no
           member := H.member
           rowIn := Nat.lt_of_lt_of_le h1 (Nat.min_le_left _ _)
           placeIn := h2
           layout := H.layout
           o := H.o
           oracle := H.oracle
           seated := H.seated
           rowBelow := Nat.lt_of_lt_of_le h1 (Nat.min_le_right _ _)
           blocks := H.blocks }⟩

/-- The walk over tl's matrices: an array each. -/
def arraysPlanB (tl : HTailF2) (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) : Bool :=
  (List.finRange (szOf tl).NM).all fun μ =>
    arrayPlanB A own R n m (tl.gtTree.getD μ.val 0) (Alg.symRows ((szOf tl).m μ)) ((szOf tl).k μ)

/-- **The value's raw matrices are made of `dataQ`'s cells**, at a yes of `arraysPlanB`, under
`RecIs`. -/
theorem raw_dataQ_arrays (tl : HTailF2) {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} {a : Part9}
    (hB : arraysPlanB A tl own R n m = true) (h : RecIs a R n m) (t : PinM Cells) :
    A.raw tl t = matsOfB A tl (dataQ own a t.1) :=
  raw_dataQ_plan A tl (fun μ i c' => Classical.choice (cellPlan_of_array A
    (Classical.choice (arrayPlan_of_B A (List.all_eq_true.1 hB μ (List.mem_finRange μ))))
    i.isLt c'.isLt)) h t

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.seatCalls_cell
#print axioms OnBytes.Road.K4.Rec.arrayPlan_of_B
#print axioms OnBytes.Road.K4.Rec.cellPlan_of_array
#print axioms OnBytes.Road.K4.Rec.raw_dataQ_arrays
