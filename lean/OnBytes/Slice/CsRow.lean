-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsRow.lean: the rows of the generator of the three folded rows.

A fold hands on three rows: one under the code C and two under the mask code Z repeated to the
positions of C (`Sg.cMid`). The library's code switch speaks of the row of the generator for a
coordinate of the long symbol at a position (`Cb.LdCode.row`): the weight that each entry of the
messages and of the tails has in that coordinate. This file gives these weights in closed form. An
entry has a weight only in the coordinate of its own row, and there it is a power of the position's
point.

Main definition: `midRow`. Main theorem: `row_mid`.
Not claimed. Nothing on a protocol.
-/
import OnBytes.Slice.CsData
import OnBytes.Slice.SimCs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- The weight of an entry of the old full message in a coordinate of the long symbol at the
position x: each of the three folded rows has its own message and tail. -/
def midRow (s : Sg) (x : ℕ) : s.cMid.Aa → CsK s → GE
  | .inl _, .inl (.inl j) => wM s.C x j.val
  | .inl _, .inr (.inl q) => wT s.C x q.val
  | .inr (.inl _), .inl (.inr (.inl j)) => wM s.Z (Fmt.M1.cp s.Z x) j.val
  | .inr (.inl _), .inr (.inr (.inl q)) => wT s.Z (Fmt.M1.cp s.Z x) q.val
  | .inr (.inr _), .inl (.inr (.inr j)) => wM s.Z (Fmt.M1.cp s.Z x) j.val
  | .inr (.inr _), .inr (.inr (.inr q)) => wT s.Z (Fmt.M1.cp s.Z x) q.val
  | _, _ => 0

/-- The generator's weight of an entry of the message, at a position of a group. -/
private theorem gen_m (C : Fmt.M1.Code) {a : ℕ} (x : Fin (2 ^ a)) (j : Fin C.l) :
    genOf C (posIn C x) (Fin.natAdd C.r j) = wM C (Fmt.M1.cp C x.val) j.val := by
  simp only [genOf, ptOf, wM, posIn, Fmt.M1.cp, Fmt.M1.Code.n, j.isLt, if_true, Fin.val_natAdd]

/-- The generator's weight of an entry of the tail, at a position of a group. -/
private theorem gen_t (C : Fmt.M1.Code) {a : ℕ} (x : Fin (2 ^ a)) (q : Fin C.r) :
    genOf C (posIn C x) (Fin.castAdd C.l q) = wT C (Fmt.M1.cp C x.val) q.val := by
  simp only [genOf, ptOf, wT, posIn, Fmt.M1.cp, Fmt.M1.Code.n, q.isLt, if_true, Fin.val_castAdd]

/-- A position of the code itself is read at that position. -/
private theorem cp_self (C : Fmt.M1.Code) (x : Fin (2 ^ C.a)) : Fmt.M1.cp C x.val = x.val :=
  Nat.mod_eq_of_lt x.isLt

/-- The library's row of the generator of the three folded rows. -/
theorem row_mid (s : Sg) (x : s.Ps) (α : s.cMid.Aa) (k : CsK s) :
    s.cMid.row x α k = midRow s x.val α k := by
  rcases α with ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rcases k with (j | j | j) | (q | q | q) <;>
    simp [LdCode.row, midRow, Pi.single_apply, gen_m, gen_t, cp_self]

end OnBytes.Slice

#print axioms OnBytes.Slice.row_mid
