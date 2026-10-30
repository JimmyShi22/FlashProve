-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LangTest.lean: two stored tables for the language of the link.

The language `Sz.Lang` (OnBytes/Slice/LinkAt.lean) holds a pair of stored tables if the first table
does not decode, or if the second decodes to the same rows' messages. A statement on that language
would say nothing if no table decoded, or if all tables decoded to the same messages. This file
writes two tables for that question, and does not prove that they decode.

The two tables. In `Sz.zeroTab` every word is 0. In `Sz.oneTab` the row with the number 0 is the
code word of the message with first entry 1 and all other entries 0, with the tail 0. Every other
word is 0.




Main definitions: `Sz.zeroTab`, `Sz.oneTab`.
Lemmas on numbers and lists: `rowNo_false`, `getD_copies`.





Not claimed. That either table decodes, or that a pair of tables lies outside the language.
Nothing on tables that are not tables of code words. Nothing on protocols.
No theorem of this library is stated for `Sz.Lang`.
-/
import Cb.Ld.LdFoldEqProofs
import OnBytes.Slice.LinkAt
import OnBytes.Slice.CodeFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Blocks

namespace Sz
variable (S : Sz)

/-- The stored table in which every word is 0. -/
def zeroTab : S.Pos → Run.PQ.SgX := fun x => (x.val, List.replicate (2 ^ S.P.v) 0)

/-- The stored table whose row number 0 is the code word of the message with first entry 1 and all
other entries 0, with the tail 0, and whose other words are 0. That code word has the value z^r at
the point z, where r is the number of the tail's entries. -/
def oneTab : S.Pos → Run.PQ.SgX :=
  fun x => (x.val, ofF (ptOf S.P.T.a x ^ S.P.T.r) :: List.replicate (2 ^ S.P.v - 1) 0)

/-- The vertex with all digits 0 has the number 0. -/
theorem rowNo_false (v : ℕ) : rowNo (fun _ : Fin v => false) = 0 := by
  simp [rowNo]

end Sz

/-- A list of copies of d, read at any place with the default d, gives d. -/
theorem getD_copies {α : Type} (d : α) : ∀ n i : ℕ, (List.replicate n d).getD i d = d
  | 0, _ => by simp
  | _ + 1, 0 => by simp [List.replicate_succ]
  | n + 1, i + 1 => by
    rw [List.replicate_succ, List.getD_cons_succ]
    exact getD_copies d n i

end OnBytes.Slice

