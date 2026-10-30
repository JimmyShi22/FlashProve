-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Honest.lean: stored tables that the format's own encoder makes, and their polynomials.


The language of the link (`Sz.Lang`, OnBytes/Slice/LinkAt.lean) holds a pair of stored tables if the
first table does not decode, or if the second decodes to the same rows' messages. No soundness
statement for that language can show that the decoder's code is the code in which tables are
written: with another code honest tables would not decode, every pair of them would lie in the
language by its first clause, and the statement would say nothing on them. This file takes the
format's own function for a symbol of a code word (`symF` in Fmt/M1Codes.lean) and shows that a
table made with it is the table of code words of polynomials whose message parts are the messages.
That such a table decodes is not shown here. No theorem of this library is stated for `Sz.Lang`.

Main definitions.
 `honestTab S msg tl`   the stored table whose row number b is the format's code word of the
                        message msg b with the random tail tl b. The tests of Fmt/M3Link.lean make
                        a stored column in the same way.
 `honestMsgs S msg`     the rows' messages, read in the field.
Main theorems.
 `view_honestPolys`   the message parts of the rows' polynomials (`honestPolys`) are the messages.
 `honestTab_getD`     a word of the table, at the row of a vertex.
 `tab_honestTab`      the table is the table of code words of these polynomials, under the
                      library's generator matrix.




A list that is shorter than the code asks counts as filled with 0, a longer one as cut, as in
`symF`. So nothing is asked of the lists' lengths.

Not claimed. That the programs write their tables with this function: no file of whole tables is
compared here. Nothing on tables that are not tables of code words. Nothing on protocols.
-/
import OnBytes.Slice.LangTest
import OnBytes.Slice.LinkAt
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import OnBytes.Slice.SimBasic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Blocks

/-- The stored table whose row number b is the format's code word of the message msg b with the
tail tl b. -/
def honestTab (S : Sz) (msg tl : ℕ → List UInt64) : S.Pos → Run.PQ.SgX :=
  fun x => (x.val, (List.range (2 ^ S.P.v)).map fun b => Fmt.M1.symF S.P.T x.val (msg b) (tl b))

/-- The rows' messages, read in the field: entry j of the row at the vertex r. -/
def honestMsgs (S : Sz) (msg : ℕ → List UInt64) : S.ix.Row × S.En → GE :=
  fun n => algebraMap GF GE (toF ((msg (Sz.rowNo n.1)).getD n.2.val 0))

/-- The coefficients of the rows' polynomials: the tail's entries, then the message's. -/
def honestPolys (S : Sz) (msg tl : ℕ → List UInt64) : S.ix.Row → S.Co → GE :=
  fun r k => algebraMap GF GE
    (if k.val < S.P.T.r then toF ((tl (Sz.rowNo r)).getD k.val 0)
      else toF ((msg (Sz.rowNo r)).getD (k.val - S.P.T.r) 0))

/-- The message parts of these polynomials are the messages. -/
theorem view_honestPolys (S : Sz) (msg tl : ℕ → List UInt64) :
    S.ix.view (honestPolys S msg tl) = honestMsgs S msg := by
  funext n
  show algebraMap GF GE
    (if S.P.T.r + n.2.val < S.P.T.r then toF ((tl (Sz.rowNo n.1)).getD (S.P.T.r + n.2.val) 0)
      else toF ((msg (Sz.rowNo n.1)).getD (S.P.T.r + n.2.val - S.P.T.r) 0)) = _
  rw [if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
  rfl

/-- A word of the table, at the row of a vertex. -/
theorem honestTab_getD (S : Sz) (msg tl : ℕ → List UInt64) (x : S.Pos) (r : S.ix.Row) :
    (honestTab S msg tl x).2.getD (Sz.rowNo r) 0 =
      Fmt.M1.symF S.P.T x.val (msg (Sz.rowNo r)) (tl (Sz.rowNo r)) := by
  have hr : Sz.rowNo r < 2 ^ S.P.v := rowNo_lt r
  have hl : Sz.rowNo r < ((List.range (2 ^ S.P.v)).map fun b =>
      Fmt.M1.symF S.P.T x.val (msg b) (tl b)).length := by
    rw [List.length_map, List.length_range]
    exact hr
  show ((List.range (2 ^ S.P.v)).map fun b =>
    Fmt.M1.symF S.P.T x.val (msg b) (tl b)).getD (Sz.rowNo r) 0 = _
  rw [List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range]

/-- The table is the table of code words of these polynomials, under the library's generator
matrix. -/
theorem tab_honestTab (S : Sz) (msg tl : ℕ → List UInt64) (r : S.ix.Row) (x : S.Pos) :
    S.lk.tab (honestTab S msg tl) r x = S.ix.G.mulVec (honestPolys S msg tl r) x := by
  show algebraMap GF GE (toF ((honestTab S msg tl x).2.getD (Sz.rowNo r) 0)) =
    ∑ k : Fin (S.P.T.r + S.P.T.l), genOf S.P.T x k * honestPolys S msg tl r k
  rw [honestTab_getD, toF_symF, map_add, map_sum, map_sum, Fin.sum_univ_add, Finset.sum_range,
    Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    show _ = algebraMap GF GE (ptOf S.P.T.a x ^ q.val) * algebraMap GF GE
      (if q.val < S.P.T.r then toF ((tl (Sz.rowNo r)).getD q.val 0)
        else toF ((msg (Sz.rowNo r)).getD (q.val - S.P.T.r) 0))
    rw [if_pos q.isLt, map_mul]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    show _ = algebraMap GF GE (ptOf S.P.T.a x ^ (S.P.T.r + j.val)) * algebraMap GF GE
      (if S.P.T.r + j.val < S.P.T.r then toF ((tl (Sz.rowNo r)).getD (S.P.T.r + j.val) 0)
        else toF ((msg (Sz.rowNo r)).getD (S.P.T.r + j.val - S.P.T.r) 0))
    rw [if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, map_mul]
    rfl



end OnBytes.Slice

