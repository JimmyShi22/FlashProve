-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MaskSeatWord.lean: WHAT THE CODE SWITCH's TEXT READS OF A MEMBER's MASK
ROWS IN ITS TREE IS WHAT THE TABLE OF JOINTS' READER OF A SEAT READS THERE:
`keptSym_seat` (Johnson/Top/H0/K2Caller/SeatWord.lean), which speaks of the main symbols, carried to
the mask symbols, step for step. A definition, a structure, theorems. It changes no other file.

  `readE_col_mask`: a column's mask symbol b, read in the field: the three words behind the mask's
    skip.
  `maskSym p s x orc o b q`: mask symbol b of the message o's column at the position q, off the
    oracles (after `keptSym`, K2Hands/KeptLong.lean).
  `MaskSeat`: what ties a message of the switch's front to a seat (tree, tenant) of the table, for
    its mask rows: `KeptSeat` with three clauses turned: the leaf that is read at the
    position x is `at' x` · the two skips in front of the tenant's MASK words are one · the
    tenant's mask words are three a mask row.
  `maskSym_seat`: **MaskSeat · b < sh.maskRows · x < positions ⊢ readE (maskSym p t fx orc old b x)
    = rowAt false ‹the seat's tenant's mask words at the leaf at' x› b.**
Limits. `MaskSeat` IS A PREMISE: no clause of it is shown at a value. As with `KeptSeat`: without
«every leaf's column has the tree's words» the two readings part. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.SeatWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (rowAt)
open VerifiableInference.Desc.First (K2.P2)
open VerifiableInference.Desc.First.K2Caller (getD_drop_take)
open _root_.Tw.K2 (switchNotices)

theorem readE_col_mask (xo : OnBytes.Oracle) (ms zs : ℕ) (c : Array F) (b : ℕ)
    (hb : b < xo.shape.maskRows) :
    readE ((Blk.columnOf xo ms zs c).mask.getD b zeroE) =
      toE (c.getD (zs + 3 * b) 0, c.getD (zs + 3 * b + 1) 0, c.getD (zs + 3 * b + 2) 0) := by
  have e : (Blk.columnOf xo ms zs c).mask.getD b zeroE =
      E.mk3 (c.getD (zs + 3 * b) 0) (c.getD (zs + 3 * b + 1) 0) (c.getD (zs + 3 * b + 2) 0) := by
    simp [Blk.columnOf, Array.getD_eq_getD_getElem?, hb]
  rw [e]
  rfl

/-- Mask symbol number b of the message o's column at the position q, off the oracles. -/
def maskSym (p : First.K2.P2) (s : First.S) (x : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (o b q : ℕ) : OnBytes.E :=
  (((First.K2.bookAt (First.K2.par9 p).firstTree x.st s.book s.roots
      (switchNotices x.T x.others)).bind fun B =>
      (B.place[o]?).bind fun pl =>
        First.K2.colOne (First.K2.skelOf x) B (First.K2.par9 p).firstTree p.logN orc o pl q).map
    fun c => c.mask.getD b zeroE).getD zeroE

/-- **What ties a message of the switch's front to a seat of the table, for its mask rows.** -/
structure MaskSeat {Xi : Type} (G : FileDescription Xi) (p : First.K2.P2) (t : First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) (Y : Strs) (old : ℕ)
    (sh : OracleShape) (seat : ℕ × ℕ) (positions : ℕ) (at' : ℕ → ℕ) : Prop where
  is : ∃ (B : TreeBook) (tp : ℕ) (tr : Tree) (xo : OnBytes.Oracle)
      (o : VerifiableInference.Desc.Oracle) (n : VerifiableInference.Desc.SymbolComponent),
    First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
      (switchNotices fx.T fx.others) = some B ∧
    B.place[old]? = some (tp, seat.2) ∧ B.trees[tp]? = some tr ∧
    (First.K2.skelOf fx).oracles[old]? = some xo ∧ xo.shape = sh ∧
    (∀ x, x < positions →
      (if tr.shape.logN == p.logN then x else x % 2 ^ tr.shape.logN) = at' x) ∧
    (∀ x, x < positions →
      orc (tr.number - (First.K2.par9 p).firstTree) (at' x) = Y.col seat.1 (at' x)) ∧
    G.oracleAt seat.1 = some o ∧ o.tenants[seat.2]? = some n ∧
    (∀ x, x < positions → (Y.col seat.1 (at' x)).length = o.words) ∧
    tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
      o.maskSkip seat.2 ∧
    n.mask = 3 * sh.maskRows

/-- **The two readings of a member's mask symbol are one.** -/
theorem maskSym_seat {Xi : Type} {G : FileDescription Xi} {p : First.K2.P2} {t : First.S}
    {fx : _root_.Tw.K2.Front} {orc : ℕ → ℕ → List UInt64} {Y : Strs} {old : ℕ} {sh : OracleShape}
    {seat : ℕ × ℕ} {positions : ℕ} {at' : ℕ → ℕ}
    (K : MaskSeat G p t fx orc Y old sh seat positions at') (b x : ℕ) (hb : b < sh.maskRows)
    (hx : x < positions) :
    readE (maskSym p t fx orc old b x) =
      rowAt false (((wordOf G Y seat.1 seat.2 (at' x)).map (·.mask)).getD []) b := by
  obtain ⟨B, tp, tr, xo, o, n, hB, hpl, htr, hxo, rfl, hpos, horc, hG, htn, hlen, hskip, hn⟩ :=
    K.is
  have hw : ((wordOf G Y seat.1 seat.2 (at' x)).map (·.mask)).getD [] =
      ((Y.col seat.1 (at' x)).drop (o.maskSkip seat.2)).take n.mask := by
    unfold wordOf VerifiableInference.Desc.Oracle.cut
    simp [hG, htn, hlen x hx]
  have hk : maskSym p t fx orc old b x =
      (Blk.columnOf xo ((tr.shape.mainSymbols.extract 0 seat.2).foldl (· + ·) 0)
        (o.maskSkip seat.2) (Y.col seat.1 (at' x)).toArray).mask.getD b zeroE := by
    unfold maskSym First.K2.colOne
    simp only [hB, Option.bind_some, hpl, htr, hxo, Option.map_some, Option.getD_some, hpos x hx,
      horc x hx, hskip]
  rw [hk, readE_col_mask xo _ _ _ b hb, hw]
  show _ = toE _
  rw [getD_drop_take _ _ _ _ (by omega), getD_drop_take _ _ _ _ (by omega),
    getD_drop_take _ _ _ _ (by omega)]
  simp [Nat.add_assoc]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.readE_col_mask
#print axioms VerifiableInference.Desc.LinkJoin.maskSym_seat
