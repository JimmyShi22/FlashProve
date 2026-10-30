-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OpenWordFront.lean: AT EVERY POSITION AT WHICH THE CODE
SWITCH's FRONT READS THE CARRIED ROWS (`K2.longFront`): WHAT IT READS AT THE MAIN ROW AND AT THE TWO
MASK ROWS IS, IN THE FIELD, THE TYPED FOLD OF THE TABLE's OWN WORDS, ARRANGED; AND TWO TERMS FOR THE
FRESH MASK's WORD THAT MAKE IT SO. The join of OpenWordAt · ColsShowOf · FrontCols. Definitions, a
structure, theorems. It changes no other file.

The term `mWAt`, by the
table of joints' reader, has a premise (`MaskSeat` at rows.fresh): «every leaf's column has
the tree's words». By report, not shown here: the fresh mask of the closing's fold is no item
of the table: no promise gives that clause. So the word is a LETTER z with one clause (hz), and
that clause has two payers.
  `mWAt G Y seatF aF`, `mWAt_fresh`: that term, and hz at it from `MaskSeat`.
  `mWRaw Y tree skip aF`: **THE FRESH MASK's WORD OFF THE RAW COLUMNS**: at the native position x
    and the row b of the cube of h variables: the three words of the column of the tree `tree` at
    the leaf x modulo 2 ^ aF that stand behind skip + 3 * rowNo b; zeros behind the column's end:
    as the switch's text reads them. `FreshSeat`: what ties rows.fresh to that tree: the book · the
    front's statement · the reading by key · the skip: NO CLAUSE ON THE COLUMNS' LENGTHS.
    `mWRaw_fresh`: hz at it.
  `open_word_front`: **at R := (rowsPort cs l mem s e oM oZ hM hZ).keep kp · W := R.G.word (wordsOf
    G cs l seat Y) · any z: R.Good · LaysFit R rows.layout ix · the first mask rows are R.oZ · two
    masks · h + g challenges · the layout's exponents · the layout's member number ix a is the
    message no a · KeptSeat and MaskSeat at every member · hz : z q (b, ()) = readE (maskSym …
    rows.fresh (rowNo b) q) · longFront p t fx orc q = some seg ⊢ foldedAt R.Sh.par (readP (h + g)
    rows.gamma) (R.Sh.rho.wd W) z holds at the main row readE seg[0], at the carried mask readE
    seg[maskRow 0], at the fresh mask readE seg[maskRow 1].**
Limits. LaysFit · KeptSeat · MaskSeat · FreshSeat are premises, shown at no value. The kept rows are
not joined here. That longFront answers at q is a premise. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.ColsShowOf
import Johnson.Desc.First.Link.Law.FrontCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (rowAt wordsOf)
open VerifiableInference.Desc.First.K2Caller (KeptSeat)
open VerifiableInference.Desc.First.Close (foldedAt)

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **THE FRESH MASK's WORD.** -/
noncomputable def mWAt {Xi : Type} (G : FileDescription Xi) (Y : Strs) (seatF : ℕ × ℕ) (aF : ℕ) :
    (RP).Sh.par.Cw.Word :=
  fun (x : Fin (2 ^ s.C.a)) sy =>
    rowAt false (((wordOf G Y seatF.1 seatF.2 (x.val % 2 ^ aF)).map (·.mask)).getD [])
      (Sz.rowNo sy.1)

/-- The first payer of the clause on the fresh mask's word: through the table's reader. -/
theorem mWAt_fresh {Xi : Type} (G : FileDescription Xi) (Y : Strs) (p : First.K2.P2) (t : First.S)
    (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64) {shF : OracleShape} {seatF : ℕ × ℕ}
    {aF : ℕ}
    (MF : MaskSeat G p t fx orc Y fx.f.rows.fresh shF seatF (2 ^ s.C.a) fun x => x % 2 ^ aF)
    (hF : shF.maskRows = 2 ^ s.h) (q : Fin (2 ^ s.C.a)) (b : Fin s.h → Bool) :
    mWAt cs l mem s e oM oZ hM hZ kp G Y seatF aF q (b, ()) =
      readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val) := by
  rw [maskSym_seat MF (Sz.rowNo b) q.val (by rw [hF]; exact rowNo_lt b) q.isLt]
  rfl

/-- **THE FRESH MASK's WORD, OFF THE RAW COLUMNS**: the three words behind the skip, zeros behind
the column's end: as the code switch's text reads them. -/
noncomputable def mWRaw (Y : Strs) (tree skip aF : ℕ) : (RP).Sh.par.Cw.Word :=
  fun (x : Fin (2 ^ s.C.a)) sy =>
    toE ((Y.col tree (x.val % 2 ^ aF)).getD (skip + 3 * Sz.rowNo sy.1) 0,
      (Y.col tree (x.val % 2 ^ aF)).getD (skip + 3 * Sz.rowNo sy.1 + 1) 0,
      (Y.col tree (x.val % 2 ^ aF)).getD (skip + 3 * Sz.rowNo sy.1 + 2) 0)

/-- What ties the fresh mask's message to a tree of the strings: on the book, the front's statement
and the oracles' reading by key. NO CLAUSE ON THE COLUMNS' LENGTHS. -/
structure FreshSeat (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) (Y : Strs) (tree skip aF rowsF positions : ℕ) : Prop where
  is : ∃ (B : TreeBook) (tp tn : ℕ) (tr : Tree) (xo : OnBytes.Oracle),
    First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
      (_root_.Tw.K2.switchNotices fx.T fx.others) = some B ∧
    B.place[fx.f.rows.fresh]? = some (tp, tn) ∧ B.trees[tp]? = some tr ∧
    (First.K2.skelOf fx).oracles[fx.f.rows.fresh]? = some xo ∧ xo.shape.maskRows = rowsF ∧
    (∀ x, x < positions →
      (if tr.shape.logN == p.logN then x else x % 2 ^ tr.shape.logN) = x % 2 ^ aF) ∧
    (∀ x, x < positions →
      orc (tr.number - (First.K2.par9 p).firstTree) (x % 2 ^ aF) = Y.col tree (x % 2 ^ aF)) ∧
    tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 tn).foldl (· + ·) 0 = skip

/-- The second payer: off the raw columns. -/
theorem mWRaw_fresh (Y : Strs) (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front)
    (orc : ℕ → ℕ → List UInt64) {tree skip aF : ℕ}
    (FS : FreshSeat p t fx orc Y tree skip aF (2 ^ s.h) (2 ^ s.C.a)) (q : Fin (2 ^ s.C.a))
    (b : Fin s.h → Bool) :
    mWRaw cs l mem s e oM oZ hM hZ kp Y tree skip aF q (b, ()) =
      readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val) := by
  obtain ⟨B, tp, tn, tr, xo, hB, hpl, htr, hxo, hsh, hpos, horc, hskip⟩ := FS.is
  have hk : maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val =
      (Blk.columnOf xo ((tr.shape.mainSymbols.extract 0 tn).foldl (· + ·) 0) skip
        (Y.col tree (q.val % 2 ^ aF)).toArray).mask.getD (Sz.rowNo b) zeroE := by
    unfold maskSym First.K2.colOne
    simp only [hB, Option.bind_some, hpl, htr, hxo, Option.map_some, Option.getD_some,
      hpos q.val q.isLt, horc q.val q.isLt, hskip]
  rw [hk, readE_col_mask xo _ _ _ (Sz.rowNo b) (by rw [hsh]; exact rowNo_lt b)]
  show toE _ = toE _
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rfl

/-- **WHAT THE FRONT READS IS THE TYPED FOLD.** -/
theorem open_word_front {Xi : Type} (G : FileDescription Xi) (seat : Fin l.length → ℕ × ℕ) (Y : Strs)
    (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (no : {i // mem i} → ℕ) (ix : {i // mem i} → ℕ) (hg : (RP).Good)
    (Ft : LaysFit RP fx.f.rows.layout ix)
    (hf : ∀ a, (RP).nZ a ≠ 0 → fx.f.rows.layout.maskFirst.getD (ix a) none = some ((RP).oZ a))
    (hm : fx.f.rows.masks = 2) (hγ : fx.f.rows.gamma.length = s.h + s.g)
    (hk : fx.f.rows.layout.k = s.h + s.g) (hh : fx.f.rows.layout.h = s.h)
    (hno : ∀ a, fx.f.rows.layout.members[ix a]? = some (no a))
    (KS : ∀ a : {i // mem i}, (l.get a.1).1.mainRows ≠ 0 →
      KeptSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1) (2 ^ (cMain cs (l.get a.1).1).a))
    (MS : ∀ a : {i // mem i}, MaskSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1)
      (2 ^ s.C.a) fun x => x % 2 ^ aOf cs (l.get a.1).1)
    (z : (RP).Sh.par.Cw.Word)
    (hz : ∀ (q : Fin (2 ^ s.C.a)) (b : Fin s.h → Bool),
      z q (b, ()) = readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val))
    (q : Fin (2 ^ s.C.a)) {seg : Array E}
    (h : First.K2.longFront p t fx orc q.val = some seg) :
    foldedAt (RP).Sh.par (readP (s.h + s.g) fx.f.rows.gamma)
        ((RP).Sh.rho.wd ((RP).G.word (wordsOf G cs l seat Y))) z (.inl q) (none, ()) =
        readE (seg.getD 0 zeroE) ∧
      foldedAt (RP).Sh.par (readP (s.h + s.g) fx.f.rows.gamma)
        ((RP).Sh.rho.wd ((RP).G.word (wordsOf G cs l seat Y))) z (.inr (.inl q)) () =
        readE (seg.getD (fx.f.rows.maskRow 0) zeroE) ∧
      foldedAt (RP).Sh.par (readP (s.h + s.g) fx.f.rows.gamma)
        ((RP).Sh.rho.wd ((RP).G.word (wordsOf G cs l seat Y))) z (.inr (.inr q)) () =
        readE (seg.getD (fx.f.rows.maskRow 1) zeroE) := by
  obtain ⟨B, places, hB, hP, hr⟩ := front_inv h
  have hso : singleRowsOracles fx.f.rows =
      fx.f.rows.layout.members.push fx.f.rows.fresh := by
    unfold singleRowsOracles
    simp [hm]
  have hsz : (singleRowsOracles fx.f.rows).size = fx.f.rows.layout.members.size + 1 := by
    rw [hso, Array.size_push]
  have Cs := colsShow_of cs l mem s e oM oZ hM hZ kp G seat Y p t fx orc no ix
    (frontCols p fx orc B places q.val) 0 q (fun a c hc => by
      have hlt := Ft.lt a
      have hw : ix a < (singleRowsOracles fx.f.rows).size := by omega
      obtain ⟨c1, c2, c3, c4⟩ := front_col hB hP hw hc
      have eo : (singleRowsOracles fx.f.rows)[ix a] = no a := by
        have h1 := hno a
        rw [Array.getElem?_eq_getElem hlt] at h1
        simp only [hso]
        rw [Array.getElem_push_lt hlt]
        exact Option.some.inj h1
      rw [eo] at c1 c2 c3 c4
      obtain ⟨_, _, _, xo, _, _, _, _, _, hxo, hsh, _⟩ := (MS a).is
      have eg : (First.K2.skelOf fx).oracles.getD (no a) default = xo := by
        rw [Array.getD_eq_getD_getElem?, hxo]
        rfl
      rw [eg, hsh] at c3 c4
      exact ⟨c3, c4, c1, c2⟩) KS MS
  refine open_word_at RP hg Ft hf hm hγ hk hh _ _ Cs (fun c hc b => ?_) hr
  have hw : fx.f.rows.layout.members.size < (singleRowsOracles fx.f.rows).size := by omega
  obtain ⟨_, c2, _, _⟩ := front_col hB hP hw hc
  have eo : (singleRowsOracles fx.f.rows)[fx.f.rows.layout.members.size] = fx.f.rows.fresh := by
    simp only [hso]
    exact Array.getElem_push_eq
  rw [eo] at c2
  have e1 : readV c.mask (Sz.rowNo b) =
      readE (maskSym p t fx orc fx.f.rows.fresh (Sz.rowNo b) q.val) :=
    congrArg readE (c2 (Sz.rowNo b))
  rw [e1]
  exact hz q b

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mWAt_fresh
#print axioms VerifiableInference.Desc.LinkJoin.mWRaw_fresh
#print axioms VerifiableInference.Desc.LinkJoin.open_word_front
