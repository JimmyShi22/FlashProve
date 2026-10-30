-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatWord.lean: the code switch: WHAT THE SWITCH's TEXT READS OF A
KEPT MEMBER's OWN TREE IS WHAT THE TABLE OF JOINTS' READER OF A SEAT READS THERE.

The text cuts a leaf's column by the book's tree's shape (OnBytes/Iop/Ground.lean's columnOf,
through K2Hears/LongCols.lean's colOne). The table's reader cuts it by what the description tells of
the tree (Johnson/Desc/Msg.lean's wordOf; Johnson/Desc/Sound/MsgSig.lean's rowAt).
  getD_drop_take, up_rowAt, readE_col_main  tools
  KeptSeat     WHAT TIES A KEPT MESSAGE OF THE SWITCH's FRONT TO A SEAT (tree, tenant) OF THE TABLE:
               the book has the message at a tree and at the seat's tenant · the front's statement
               has its shape · a position below the number of leaves is read as it is · the oracles'
               reading at the tree's key is Strs.col at the seat's tree · the description tells the
               tree and the tenant · EVERY LEAF's COLUMN HAS THE TREE's WORDS · the two skips in
               front of the tenant's main words are one · the tenant's main words are the shape's
               main rows, one word or three a row
  keptSym_seat  THE STATEMENT: K2Hands/KeptLong.lean's keptSym, read in the field, is the table's
               reader's row symbol, read in the field
LIMITS. KeptSeat IS A PREMISE: no clause of it is shown at a real value. Ten clauses are on public
numbers (the book, the statement's shapes, the description). TWO READ THE ORACLES: «the reading at
the key is Strs.col» (K2Hears/OrcStrs.lean's orcY has it where the tree is the first at hand with
that key) and «every leaf's column has the tree's words» (the table's «shown» at the seat). WITHOUT
THE LAST THE TWO READINGS PART: the table's reader returns nothing at a leaf of another length, the
text reads it with zeros behind its end. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.KeptLong
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Strs FileDescription wordOf)
open VerifiableInference.Desc.Sound (rowAt)
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

theorem getD_drop_take (col : List UInt64) (s n k : ℕ) (hk : k < n) :
    ((col.drop s).take n).getD k 0 = col.getD (s + k) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk, List.getElem?_drop]

theorem up_rowAt (bb : Bool) (ws : List UInt64) (b : ℕ) :
    upRow bb (rowAt bb ws b) =
      if bb then algebraMap Cb.Gl.F Cb.Gl.E (toF (ws.getD b 0))
      else toE (ws.getD (3 * b) 0, ws.getD (3 * b + 1) 0, ws.getD (3 * b + 2) 0) := by
  cases bb <;> rfl

theorem readE_col_main (xo : OnBytes.Oracle) (ms zs : ℕ) (c : Array F) (b : ℕ)
    (hb : b < xo.shape.mainRows) :
    readE ((Blk.columnOf xo ms zs c).main.getD b zeroE) =
      if xo.shape.mainDeg == 1 then algebraMap Cb.Gl.F Cb.Gl.E (toF (c.getD (ms + b) 0))
      else toE (c.getD (ms + 3 * b) 0, c.getD (ms + 3 * b + 1) 0, c.getD (ms + 3 * b + 2) 0) := by
  have e : (Blk.columnOf xo ms zs c).main.getD b zeroE =
      if xo.shape.mainDeg == 1 then OnBytes.ofF (c.getD (ms + b) 0)
      else E.mk3 (c.getD (ms + 3 * b) 0) (c.getD (ms + 3 * b + 1) 0)
        (c.getD (ms + 3 * b + 2) 0) := by
    simp [Blk.columnOf, Array.getD_eq_getD_getElem?, hb]
  rw [e]
  split
  · exact readE_ofF _
  · rfl

/-- **What ties a kept message of the switch's front to a seat of the table**: all on public numbers
but the two clauses on the oracles (orcIs, whole). -/
structure KeptSeat {Xi : Type} (G : FileDescription Xi) (p : K2.P2) (t : VerifiableInference.Desc.First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ)
    (sh : OracleShape) (seat : ℕ × ℕ) (leaves : ℕ) : Prop where
  at' : ∃ (B : TreeBook) (tp : ℕ) (tr : Tree) (xo : OnBytes.Oracle)
      (o : VerifiableInference.Desc.Oracle) (n : VerifiableInference.Desc.SymbolComponent),
    K2.bookAt (K2.par9 p).firstTree fx.st t.book t.roots (switchNotices fx.T fx.others) = some B ∧
    B.place[old]? = some (tp, seat.2) ∧ B.trees[tp]? = some tr ∧
    (K2.skelOf fx).oracles[old]? = some xo ∧ xo.shape = sh ∧
    (∀ x, x < leaves → (if tr.shape.logN == p.logN then x else x % 2 ^ tr.shape.logN) = x) ∧
    (∀ x, x < leaves → orc (tr.number - (K2.par9 p).firstTree) x = Y.col seat.1 x) ∧
    G.oracleAt seat.1 = some o ∧ o.tenants[seat.2]? = some n ∧
    (∀ x, x < leaves → (Y.col seat.1 x).length = o.words) ∧
    (tr.shape.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = o.mainSkip seat.2 ∧
    n.main = if sh.mainDeg == 1 then sh.mainRows else 3 * sh.mainRows

/-- **The two readings of a kept member's main symbol are one.** -/
theorem keptSym_seat {Xi : Type} {G : FileDescription Xi} {p : K2.P2}
    {t : VerifiableInference.Desc.First.S} {fx : _root_.Tw.K2.Front} {orc : ℕ → ℕ → List UInt64}
    {Y : Strs} {old : ℕ} {sh : OracleShape} {seat : ℕ × ℕ} {leaves : ℕ}
    (K : KeptSeat G p t fx orc Y old sh seat leaves) (b x : ℕ) (hb : b < sh.mainRows)
    (hx : x < leaves) :
    readE (keptSym p t fx orc old b x) =
      upRow (sh.mainDeg == 1) (rowAt (sh.mainDeg == 1)
        (((wordOf G Y seat.1 seat.2 x).map (·.main)).getD []) b) := by
  obtain ⟨B, tp, tr, xo, o, n, hB, hpl, htr, hxo, rfl, hpos, horc, hG, htn, hlen, hskip, hn⟩ :=
    K.at'
  have hw : ((wordOf G Y seat.1 seat.2 x).map (·.main)).getD [] =
      ((Y.col seat.1 x).drop (o.mainSkip seat.2)).take n.main := by
    unfold wordOf VerifiableInference.Desc.Oracle.cut
    simp [hG, htn, hlen x hx]
  have hk : keptSym p t fx orc old b x =
      (Blk.columnOf xo (o.mainSkip seat.2)
        (tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 seat.2).foldl (· + ·) 0)
        (Y.col seat.1 x).toArray).main.getD b zeroE := by
    unfold keptSym K2.colOne
    simp only [hB, Option.bind_some, hpl, htr, hxo, Option.map_some, Option.getD_some, hpos x hx,
      horc x hx, hskip]
  rw [hk, readE_col_main xo _ _ _ b hb, up_rowAt, hw]
  by_cases hd : (xo.shape.mainDeg == 1) = true
  · rw [if_pos hd] at hn
    rw [if_pos hd, if_pos hd, getD_drop_take _ _ _ _ (by omega)]
    simp
  · rw [if_neg hd] at hn
    rw [if_neg hd, if_neg hd, getD_drop_take _ _ _ _ (by omega), getD_drop_take _ _ _ _ (by omega),
      getD_drop_take _ _ _ _ (by omega)]
    simp [Nat.add_assoc]

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptSym_seat
