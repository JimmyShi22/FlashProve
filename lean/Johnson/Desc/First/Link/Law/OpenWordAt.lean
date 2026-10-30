-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OpenWordAt.lean: AT ONE POSITION: WHAT THE TEXT LAYS AS THE CARRIED
SINGLE ROWS' SYMBOLS (`rowsAt`, Johnson/Desc/Own/Symbols.lean) IS, READ IN THE FIELD, THE TYPED FOLD
OF THE ARRANGED WORDS (`foldedAt`, Johnson/Desc/First/Close/Law/Carry.lean): the main row and the
two mask rows. The join of LongText · MainTable · MaskTable · WordJoin. A theorem. It changes no
other file.

  `ColsShow R ix opened i W p q`: the members' columns at position number i are what `view` shows of
    the word W at the native positions p (main) and q (mask): as many symbols as the typed member
    has rows, each reading as the row's symbol.
  `open_word_at`: **R.Good · LaysFit · the first mask rows are the typed corners · the carried rows
    s have two masks, h + g challenges, the layout's exponents k = h + g and h · ColsShow · the
    fresh mask's word z holds at (b, x) the fresh column's mask symbol number rowNo b · a yes of
    rowsAt with seg ⊢ the typed folded word's main row at p is readE seg[0]; its carried mask at q
    is readE seg[maskRow 0]; its fresh mask at q' is readE seg[maskRow 1].**
Limits. The kept rows are another file's (`longFront_kept`, Johnson/Top/H0/K2Hands/KeptLong.lean)
with `kept_symbol` (WordJoin.lean): not joined here. `LaysFit`, `ColsShow` and the premise on z are
not paid here. ONE position: nothing on «every position». Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.MaskTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Top.H
open VerifiableInference.Desc.Own (Tables layMembers rowsAt)
open VerifiableInference.Desc.First.Close (foldedAt)

/-- The members' columns are what `view` shows. -/
structure ColsShow {S : Sig GE} (R : RowsK S) (ix : R.G.A → ℕ) (opened : Array (Array Column))
    (i : ℕ) (W : R.G.C.Word) (p : R.Sh.Cb.NP) (x : R.Sh.Cb.NS p) (q : R.Sh.Zb.NP)
    (x' : R.Sh.Zb.NS q) : Prop where
  nM : ∀ a c, colAt opened i (ix a) = some c → c.main.size = R.nM a
  nZ : ∀ a c, colAt opened i (ix a) = some c → c.mask.size = R.nZ a
  main : ∀ a c (j : Fin (R.nM a)), colAt opened i (ix a) = some c →
    readV c.main j.val = R.Sh.view.wd W ⟨a, .inl p⟩ (j, x)
  mask : ∀ a c (j : Fin (R.nZ a)), colAt opened i (ix a) = some c →
    readV c.mask j.val = R.Sh.view.wd W ⟨a, .inr q⟩ (j, x')

/-- **THE TEXT's SYMBOLS AT ONE POSITION ARE THE TYPED FOLDED WORD's.** -/
theorem open_word_at {S : Sig GE} (R : RowsK S) (hg : R.Good) {s : SingleRows} {ix : R.G.A → ℕ}
    (Ft : LaysFit R s.layout ix)
    (hf : ∀ a, R.nZ a ≠ 0 → s.layout.maskFirst.getD (ix a) none = some (R.oZ a))
    (hm : s.masks = 2) (hγ : s.gamma.length = R.s.h + R.s.g) (hk : s.layout.k = R.s.h + R.s.g)
    (hh : s.layout.h = R.s.h) {opened : Array (Array Column)} {i : ℕ} (W : R.G.C.Word)
    (z : R.Sh.par.Cw.Word) {p : R.Sh.Cb.NP} {x : R.Sh.Cb.NS p} {q : R.Sh.Zb.NP}
    {x' : R.Sh.Zb.NS q} (Cs : ColsShow R ix opened i W p x q x') {q' : R.Sh.par.Zw.NP}
    {x'' : R.Sh.par.Zw.NS q'}
    (hz : ∀ c, colAt opened i s.layout.members.size = some c →
      ∀ b : Fin R.s.h → Bool, z q' (b, x'') = readV c.mask (Sz.rowNo b))
    {seg : Array E} (h : rowsAt s opened #[] i = some seg) :
    foldedAt R.Sh.par (readP (R.s.h + R.s.g) s.gamma) (R.Sh.rho.wd W) z (.inl p) (none, x) =
        readE (seg.getD 0 zeroE) ∧
      foldedAt R.Sh.par (readP (R.s.h + R.s.g) s.gamma) (R.Sh.rho.wd W) z (.inr (.inl q)) x' =
        readE (seg.getD (s.maskRow 0) zeroE) ∧
      foldedAt R.Sh.par (readP (R.s.h + R.s.g) s.gamma) (R.Sh.rho.wd W) z (.inr (.inr q')) x'' =
        readE (seg.getD (s.maskRow 1) zeroE) := by
  obtain ⟨t, fresh, hl, z1, z2, z3, hfr, z4, rfl⟩ := rowsAt_inv hm h
  obtain ⟨a1, a0⟩ := main_table R hg Ft hl (fun r => R.Sh.view.wd W ⟨r.1, .inl p⟩ (r.2, x)) Cs.nM
    Cs.main
  obtain ⟨b1, b0⟩ := mask_table R hg Ft hf hl (fun r => R.Sh.view.wd W ⟨r.1, .inr q⟩ (r.2, x'))
    Cs.nZ Cs.mask
  refine ⟨?_, ?_, ?_⟩
  · rw [seg_main]
    exact main_symbol R W z s.gamma hγ (by rw [z1, hk]) p x a1 a0
  · have e : s.maskRow 0 = 1 + t.kept.size + 0 := by rw [z3]; rfl
    rw [e, seg_mask, hh]
    exact mask_symbol R W z s.gamma hγ (by rw [z2, hh]) q x' b1 b0
  · have e : s.maskRow 1 = 1 + t.kept.size + 1 := by rw [z3]; rfl
    rw [e, seg_fresh, hh]
    exact fresh_symbol R z s.gamma hγ (by rw [z4, hh]) _ q' x'' (hz fresh hfr)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.open_word_at
