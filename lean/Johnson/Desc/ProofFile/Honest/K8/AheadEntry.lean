-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/AheadEntry.lean: the smallness test (K8): A CELL OF AN ARRAY THAT
IS NOT YET SENT, AS THE LAW's ONE TABLE OF CELLS READS IT (`cellsAhead`,
Johnson/Desc/First/K8/CellsAhead.lean), IS THE WITNESS's TABLE's ENTRY AT THE SEAT THAT THE PLAN
GIVES THE ARRAY's MESSAGE, AT THE ROW AND PLACE AT WHICH THE LAYOUT LAYS THE ELEMENT. Two statements
with their proofs; no definition. TWO READINGS OF ONE WITNESS, w A LETTER UNDER "FOR ALL": no
prover, no Script, no input, no coin.

  `cellA_is_entry`       the sum over the array's laid blocks (`cellA`,
                         Johnson/Desc/Sound/FormsAhead.lean) is the reader's entry at the plan's
                         seat, in the main table, at the layout's row and place
  **`cellsAhead_is_entry`**   so is `cellsAhead`, where the state has an open segment's part, the
                         link's list names the array, and the array is ahead
THE SISTER, AT AN ARRAY THAT IS SENT: `cell_is_entry` (Johnson/P1K8R/ShowsJoin.lean): the proof of
`cellA_is_entry` goes its way, by the same four laws of Johnson/Desc/First/Att/K05CellAt.lean
(`blocks_sum`, `laidPlace_one`, `laidIn_row_lt`, `tableIndex_parts`) under the programs' own test
`laidMatrixOk`, here at the PLAN's bits. KIN, NOT CALLED: `cellA_at`
(Johnson/Top/H/Keep/DigitsCellAhead.lean): what a typed message holds at a seat is `cellA` there,
under "the two readers are one". `dataQA_cell_some` (Johnson/Desc/K1/Law/GoAtLaterForms.lean): the
third step of `cellsAhead_is_entry`'s proof is that law's own text. FROM `seatTab` ON TO THE ONE
ACCESSOR `Wit.tab`: `seatTab_of_mem` (Johnson/Desc/Sound/SeatTabMsgs.lean).
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. Every premise is asked and none is proved here: hp, hx, hA on the verifier's state and the
plan; hok, hrp on the layout. Nothing on which seats the plan gives. Nothing on what the witness
holds.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.K8.CellsAhead
import Johnson.Desc.First.Att.K05CellAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open VerifiableInference.Desc.First.Look (laidHolds laidPlace)
open VerifiableInference.Desc.First.Att.P (blocks_sum laidPlace_one laidIn_row_lt tableIndex
  tableIndex_parts)
open VerifiableInference.Desc.K9L (BlockFacts blockFacts)
open VerifiableInference.Desc.K9 (Ahead rowBitsOf placeBitsOf)

/-- **The sum over the blocks of an array that is ahead is the reader's entry at the plan's seat and
the layout's place.** -/
theorem cellA_is_entry (codes : Codes) (h : Ahead) (rd : ℕ × ℕ → MsgQ)
    (hok : laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf codes h.shape .main) = true)
    {r c : ℕ} {rp : ℕ × ℕ} (hrp : laidAt h.A r c = some rp) :
    cellA codes h rd r c = rd h.seat false rp.1 rp.2 := by
  have hok' := hok
  unfold laidMatrixOk at hok'
  obtain ⟨hok1, -⟩ := Eq.mp (Bool.and_eq_true _ _) hok'
  obtain ⟨hall, hno⟩ := Eq.mp (Bool.and_eq_true _ _) hok1
  have hBF : ∀ b ∈ h.A.blocks,
      BlockFacts b (rowBitsOf h.shape .main) (placeBitsOf codes h.shape .main) := by
    intro b hb
    have h1 := List.all_eq_true.1 hall b hb
    obtain ⟨h2, -⟩ := Eq.mp (Bool.and_eq_true _ _) h1
    obtain ⟨h3, -⟩ := Eq.mp (Bool.and_eq_true _ _) h2
    exact blockFacts b _ _ h3
  have hlp : laidPlace h.A.blocks r c = some rp := (laidPlace_one h.A r c).trans hrp
  have hlt : rp.1 < 2 ^ rowBitsOf h.shape .main := by
    have h0 := hlp
    unfold laidPlace at h0
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h0
    exact laidIn_row_lt b _ _ (hBF b (List.mem_of_find?_eq_some hb)) r c
      (List.find?_some (p := fun b => laidHolds b r c) hb)
  unfold cellA
  rw [blocks_sum _ _ (fun J => rd h.seat false (J % 2 ^ rowBitsOf h.shape .main)
    (J / 2 ^ rowBitsOf h.shape .main)) r c h.A.blocks hBF hno, hlp]
  show rd h.seat false (tableIndex (rowBitsOf h.shape .main) rp % 2 ^ rowBitsOf h.shape .main)
    (tableIndex (rowBitsOf h.shape .main) rp / 2 ^ rowBitsOf h.shape .main) = _
  rw [(tableIndex_parts _ rp hlt).1, (tableIndex_parts _ rp hlt).2]

section
variable {P Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (m : ℕ)

/-- **The law's table of cells, at an array that is ahead, is the witness's table's entry at the
plan's seat and the layout's place.** For every witness. -/
theorem cellsAhead_is_entry (z : P) (s : S) {q : K9.Part} (hp : K9.segAt? s = some q) {t : ℕ}
    {x : ℕ × String} (hx : q.L.arrayOf[t]? = some x) {h : Ahead}
    (hA : K9.aheadIn (N.sent m) (N.group m) q (x.1, x.2) = some h)
    (hok : laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf q.d.st.codes h.shape .main) =
      true)
    (w : Wit Cells Tok MsgT) {r c : ℕ} {rp : ℕ × ℕ} (hrp : laidAt h.A r c = some rp) :
    cellsAhead cs arr ms N m (z, s) w t r c = seatTab cs arr ms w h.seat false rp.1 rp.2 := by
  show (match K9.segAt? s with
    | some p =>
      (worldOwn p [] (dataQA (N.sent m) (N.group m) p (seatTab cs arr ms w))).entry t r c
    | none => 0) = _
  rw [hp]
  show (match q.L.arrayOf[t]? with
    | some b => (dataQA (N.sent m) (N.group m) q (seatTab cs arr ms w)).cell b.1 b.2 r c
    | none => 0) = _
  rw [hx]
  show (match K9.aheadIn (N.sent m) (N.group m) q (x.1, x.2) with
    | some h => cellA q.d.st.codes h (seatTab cs arr ms w) r c
    | none => (dataQ (N.group m) q (seatTab cs arr ms w)).cell x.1 x.2 r c) = _
  rw [hA]
  exact cellA_is_entry _ h _ hok hrp

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.cellA_is_entry
#print axioms ProofFile.Honest.K8.cellsAhead_is_entry
