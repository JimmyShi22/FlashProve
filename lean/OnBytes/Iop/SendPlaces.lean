-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Iop/SendPlaces.lean: the five numbers of a cube, the pad and the number of free entries of
OnBytes/Iop/Send.lean are those of Fmt/Places.lean.

Fmt/Places.lean restates the format page's rules of places as functions on natural numbers.
OnBytes/Iop/Send.lean has the same rules in the verifier program's own text. Here each of the
program's functions named below is proved equal to ours, for every shape and all codes.

Main definition: Send.padByPlaces (the pad of Fmt/Places.lean as a list of the program's records).
Main theorems: ceilLog2_eq_logUp; Send.freeMaskEntries_eq_freeCount; Send.cube_mainRowBits,
Send.cube_mainBits, Send.cube_maskRowBits, Send.cube_maskBits, Send.cube_bits (against logUp,
tableBits, cubeBits); Send.pad_eq_padByPlaces (Send.pad gives nothing where the pad does not fit its
row, and else the entries padEntry of the row padRow, each with the number entryNo, by answer and
within an answer by entry).

What is not claimed. WHERE an entry stands on the cube (Fmt.Places.cubeNo) is tied to nothing here
or elsewhere: the program has no number for it: it weighs the entries by Send.front and Tensor.eq.
Nothing on Send.form, Send.admit or Send.verify. On the ledger that hands the free entries out:
OnBytes/Iop/LedgerPlaces.lean. cube_bits has the codes' logEll and pad_eq_padByPlaces their ell:
that ell is 2 ^ logEll is Codes.lengthsOk's matter, not used here. The program does not import this
file.
-/
import OnBytes.Iop.Send
import Fmt.Places

namespace OnBytes
open Fmt.Places

theorem ceilLog2_eq_logUp (n : Nat) : ceilLog2 n = logUp n := rfl

namespace Send

theorem freeMaskEntries_eq_freeCount (m e s : Nat) : freeMaskEntries m e s = freeCount m e s := by
  unfold freeMaskEntries freeCount
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]

theorem cube_mainRowBits (codes : Codes) (s : OracleShape) :
    (cube codes s).mainRowBits = logUp s.mainRows := by
  by_cases hM : s.mainRows = 0 <;> simp [cube, hM, ceilLog2_eq_logUp, Nat.pos_iff_ne_zero, logUp]

theorem cube_maskRowBits (codes : Codes) (s : OracleShape) :
    (cube codes s).maskRowBits = logUp s.maskRows := by
  by_cases hZ : s.maskRows = 0 <;> simp [cube, hZ, ceilLog2_eq_logUp, Nat.pos_iff_ne_zero, logUp]

theorem cube_mainBits (codes : Codes) (s : OracleShape) :
    (cube codes s).mainBits = tableBits s.mainRows (codes.base.getD s.code default).logEll := by
  by_cases hM : s.mainRows = 0 <;>
    simp [cube, tableBits, hM, ceilLog2_eq_logUp, Nat.pos_iff_ne_zero]

theorem cube_maskBits (codes : Codes) (s : OracleShape) :
    (cube codes s).maskBits = tableBits s.maskRows (codes.mask.getD s.maskCode default).logEll := by
  by_cases hZ : s.maskRows = 0 <;>
    simp [cube, tableBits, hZ, ceilLog2_eq_logUp, Nat.pos_iff_ne_zero]

theorem cube_bits (codes : Codes) (s : OracleShape) :
    (cube codes s).bits =
      cubeBits s.mainRows (codes.base.getD s.code default).logEll
        s.maskRows (codes.mask.getD s.maskCode default).logEll := by
  by_cases hM : s.mainRows = 0 <;> by_cases hZ : s.maskRows = 0 <;>
    simp [cube, cubeBits, tableBits, hM, hZ, ceilLog2_eq_logUp, Nat.pos_iff_ne_zero]

/-- The pad of Fmt/Places.lean, as a list of the program's records. -/
def padByPlaces (codes : Codes) (s : OracleShape) : Option (List PadPlace) :=
  let inMask := padInMask s.maskRows
  let rows := if inMask then s.maskRows else s.mainRows
  let len :=
    if inMask then (codes.mask.getD s.maskCode default).ell
    else (codes.base.getD s.code default).ell
  let each := padEach inMask (s.mainDeg == 3)
  if len < each * s.answers then none
  else
    some ((List.range s.answers).flatMap fun i =>
      (List.range each).map fun t =>
        { part := if inMask then .mask else .main,
          index := entryNo rows (padRow s.mainRows s.maskRows) (padEntry len s.answers each i t),
          answer := i, basis := thetaE t })

theorem pad_eq_padByPlaces (codes : Codes) (s : OracleShape) :
    pad codes s = padByPlaces codes s := by
  by_cases hZ : s.maskRows = 0
  · by_cases hM : s.mainRows = 0 <;>
      simp [pad, padByPlaces, cube, padInMask, padRow, padEach, entryNo, padEntry, hZ, hM,
        ceilLog2_eq_logUp, Nat.pos_iff_ne_zero, Nat.mul_comm, logUp]
  · simp [pad, padByPlaces, cube, padInMask, padRow, padEach, entryNo, padEntry, hZ,
      ceilLog2_eq_logUp, Nat.pos_iff_ne_zero, Nat.mul_comm]

end Send
end OnBytes
