-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FirstIsPacked.lean: THE SHARED "SENDING" (the kind K1) AT THE
FIRST SEGMENT's OPENING: WHAT THE LOT's DATA (lotData,
Johnson/Desc/ProofFile/Honest/K1/LotData.lean) ANSWERS THERE, AT THE ROW AND PLACE AT WHICH THE
LAYOUT LAYS AN ELEMENT OF AN ARRAY "M mu": THE PACKED CELLS OF THE READER's CELLS. Three statements
and their proofs. No definition. Public data and a reader of cells as letters: no thread, no run, no
witness, no challenge.

  cells_val     the value that cellsVals (Johnson/Desc/ProofFile/Honest/K1/FirstData.lean) says of
                an array whose name reads as mu: .inl (packedCells S R.cells.cell l mu i c): by its
                text
  fill_val      first_val's sentence of the opening's filling firstFill S q
                (Johnson/Desc/ProofFile/Honest/K1/PlaceFirst.lean), AT ANY PARAMETERS q: no ground
                and no public part in it: first_val is its instance at G.first, behind data_first
  first_val     at message n of the opening, where the seat names (0, a.message), that message fits,
                a lies in it, the layout lays element (i, c) of a at rp, a's name reads as mu, and
                (i, c) lies inside the size that the values say: lotData answers
                some (.inl (packedCells S R.cells.cell 0 mu i c)) at (n, rp.1, rp.2), at whatever
                has been heard

BY CALLS, ALL OF OUR OWN FOLDER: data_first (K1/LotData.lean) · fits_of_msgFits (Law/LaidApart.lean)
· laidBack_iff (Law/LaidLists.lean) · lays_of_back, entry_of_back (Law/LaidSent.lean). All paths
under Johnson/Desc/ProofFile/Honest/.

Limits. Every premise is asked and none is proved here: all are public. That a layout's array bears
the name "M mu" of the matrix number mu is proved nowhere here. ONE PLACE OF TWENTY-FIVE: the other
first sendings stand at places of another kind. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.Law.LaidSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Params (ReqArray)
open OnBytes.HonestTrace (Sz packedCells)

/-- The value of an array whose name reads as mu. -/
theorem cells_val (S : Sz) (R : Readers) (hd : List Fmt.Drawn) (l : ℕ) {name : String} {mu : ℕ}
    (hmu : labelNo name = some mu) (i c : ℕ) :
    (cellsVals S).val R hd l name i c = .inl (packedCells S R.cells.cell l mu i c) := by
  show (match labelNo name with
    | some mu => (.inl (packedCells S R.cells.cell l mu i c) : Cb.Gl.F ⊕ Cb.Gl.E)
    | none => .inl (OnBytes.Slice.toF 0)) = _
  rw [hmu]

/-- **At the opening's filling, at any parameters q, at the layout's place: the packed cells.** -/
theorem fill_val (S : Sz) (q : Params.First) (R : Readers) (hd : List Fmt.Drawn) {n : ℕ}
    {a : ReqArray} (t1 : firstSeat q.shape 0 ⟨firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits q.codes q.shape q.layout 0 a.message = true)
    (ha : a ∈ (q.layout.link.getD 0 []).filter fun y => y.message == a.message) {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {mu : ℕ} (hmu : labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (cellsVals S).size 0 a.name = some z) (hi : i < z.1 ∧ c < z.2) :
    (firstFill S q).forSend R firstAddr hd n rp.1 rp.2 =
      some (.inl (packedCells S R.cells.cell 0 mu i c)) := by
  obtain ⟨R', P', hf⟩ := fits_of_msgFits hfit ha
  have hb : laidBack q.layout 0 a.message rp.1 rp.2 = some (a, i, c) :=
    (laidBack_iff q.layout 0 a.message R' P' hf a i c rp.1 rp.2).2 ⟨ha, hrp⟩
  show (if (firstFill S q).lays ⟨firstAddr, n⟩ rp.1 rp.2 then
    some ((firstFill S q).entry R (hd.take ((firstFill S q).heardAt ⟨firstAddr, n⟩))
      ⟨firstAddr, n⟩ rp.1 rp.2) else none) = _
  have hl : (firstFill S q).lays ⟨firstAddr, n⟩ rp.1 rp.2 = true :=
    lays_of_back q.codes q.shape q.layout (firstSeat q.shape 0) (fun _ => 0) (cellsVals S) t1 hfit
      hb hz hi
  rw [if_pos hl]
  exact congrArg some ((entry_of_back q.codes q.shape q.layout (firstSeat q.shape 0) (fun _ => 0)
    (cellsVals S) R _ t1 hb).trans (cells_val S R _ 0 hmu i c))

/-- **At the opening, at the layout's place, the lot's data answers the packed cells.** -/
theorem first_val (S : Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst) (R : Readers)
    (hd : List Fmt.Drawn) {n : ℕ} {a : ReqArray}
    (t1 : firstSeat G.first.shape 0 ⟨firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message) {i c : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i c = some rp) {mu : ℕ} (hmu : labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (cellsVals S).size 0 a.name = some z) (hi : i < z.1 ∧ c < z.2) :
    (lotData S Z G x).forSend R firstAddr hd n rp.1 rp.2 =
      some (.inl (packedCells S R.cells.cell 0 mu i c)) := by
  rw [data_first]
  exact fill_val S G.first R hd t1 hfit ha hrp hmu hz hi

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cells_val
#print axioms ProofFile.Honest.K1.fill_val
#print axioms ProofFile.Honest.K1.first_val
