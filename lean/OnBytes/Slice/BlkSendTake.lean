-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkSendTake.lean: the program's sample row reads no more of a seed's point than the
message's cube has coordinates.

One sending draws one point for all its messages, as long as the largest cube among them
(`Send.verify`, OnBytes/Iop/Send.lean). `Send.form` takes of it the first coordinates alone. So the
row at a seed is the row at the seed cut to any length from the cube's number of coordinates on.
Laws that ask "the seed's point has as many coordinates as the cube has bits"
(Johnson/Pack/FormPortZF.lean) thereby serve a longer point too. Near kin, in Johnson/Desc/K1/Law/:
`Msg.form_congr` (Joined2.lean) says the like of that folder's own form of a sample row, read in the
field; `ReadsOne`, `coef_port_main`, `coef_port_mask` (Port4.lean) hold that form against the
library's sample row at a point that may be longer than the cube; `form_eq` (FormEq.lean) ties that
form to `Send.form`, under premises on the codes' lengths and the shape. Here it is the program's
row itself, with no premise but the length, over two files on the program's sending alone.
Statements and proofs.
Main names:
  `cube_mainBits_le`, `cube_maskBits_le`: a table has at most the cube's coordinates.
  `front_take`: the factor in front of a table's equality vector, at a cut point.
  `form_take`: `Send.form` at the seed whose point is cut to n coordinates, n at least the cube's
    number: the same row.
  `readP_take`: the first n coordinates of a point cut to n, read: those of the point.
Limits: nothing on a point that is shorter than the cube. Nothing on soundness.

-/
import OnBytes.Slice.BlkSend
import OnBytes.Slice.ProgMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice
open OnBytes

/-- The main table has at most the cube's coordinates. -/
theorem cube_mainBits_le (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).mainBits ≤ (Send.cube codes s).bits := by
  rw [cube_bits_eq]
  split
  · exact le_trans (le_max_left _ _) (Nat.le_succ _)
  · exact Nat.le_add_right _ _

/-- The mask table has at most the cube's coordinates. -/
theorem cube_maskBits_le (codes : Codes) (s : OracleShape) :
    (Send.cube codes s).maskBits ≤ (Send.cube codes s).bits := by
  rw [cube_bits_eq]
  split
  · exact le_trans (le_max_right _ _) (Nat.le_succ _)
  · exact Nat.le_add_left _ _

/-- The factor in front of a table's equality vector reads the first coordinates alone. -/
theorem front_take (codes : Codes) (s : OracleShape) (z : List E) (n : ℕ)
    (hn : (Send.cube codes s).bits ≤ n) (tb : ℕ) (mask : Bool) :
    Send.front (z.take n) (Send.cube codes s) tb mask =
      Send.front z (Send.cube codes s) tb mask := by
  unfold Send.front
  by_cases hb : ((Send.cube codes s).hasMain && (Send.cube codes s).hasMask) = true
  · have h1 : (Send.cube codes s).bits - 1 < n := by
      have := cube_bits_both codes s hb
      omega
    have e1 : (z.take n).getD ((Send.cube codes s).bits - 1) zeroE =
        z.getD ((Send.cube codes s).bits - 1) zeroE := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h1]
    have e2 : (z.take n).take ((Send.cube codes s).bits - 1) =
        z.take ((Send.cube codes s).bits - 1) := by
      rw [List.take_take, Nat.min_eq_left h1.le]
    simp only [e1, e2]
  · simp only [hb, Bool.not_false, if_true]

/-- **The sample row at a cut seed is the sample row.** -/
theorem form_take (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (a n : ℕ)
    (hn : (Send.cube codes s).bits ≤ n) :
    Send.form codes s o { seed with z := seed.z.take n } a = Send.form codes s o seed a := by
  have e1 : (seed.z.take n).take (Send.cube codes s).mainBits =
      seed.z.take (Send.cube codes s).mainBits := by
    rw [List.take_take, Nat.min_eq_left (le_trans (cube_mainBits_le codes s) hn)]
  have e2 : (seed.z.take n).take (Send.cube codes s).maskBits =
      seed.z.take (Send.cube codes s).maskBits := by
    rw [List.take_take, Nat.min_eq_left (le_trans (cube_maskBits_le codes s) hn)]
  unfold Send.form
  simp only [e1, e2, front_take codes s seed.z n hn]

/-- The first n coordinates of a point cut to n. -/
theorem readP_take (n : ℕ) (l : List E) : readP n (l.take n) = readP n l :=
  funext fun i => readL_take n l i.val i.isLt

end OnBytes.Slice

#print axioms OnBytes.Slice.cube_mainBits_le
#print axioms OnBytes.Slice.cube_maskBits_le
#print axioms OnBytes.Slice.front_take
#print axioms OnBytes.Slice.form_take
#print axioms OnBytes.Slice.readP_take
