-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseOpen.lean: the columns that the program's base case reads are the columns of the
last tree as it was sent.

The base case of the program (the Lean verifier in OnBytes/) reads the opened columns of two oracle
messages, the last stage's and the masking oracle, by one call of `Blk.readOpened`. Both are parts
of one tree. Each has one main row over the extension field and one mask row, so a leaf's column has
twelve words: the last stage's main symbol, the masking oracle's, the last stage's mask symbol, the
masking oracle's. The format (the verifier of the library's folder Fmt/) reads the same twelve words
as four symbols (OnBytes/Slice/LastJoint.lean: `lastQ`, `lastColW`, `lastMk`). This file joins the
two readings, from the law on a reading of the parts of one tree (OnBytes/Slice/BlkOpenN.lean:
`readParts`).

Main definitions: `LastBook` (what is public about the last tree).
Main theorems.
 `baseTie_of_view`   the condition `BaseTie` of OnBytes/Slice/BaseYields.lean is met by the word and
                     the masking word of the last tree.
 `lastRows_read`     the symbols of the last stage's two single rows are the first main symbol and
                     the first mask symbol of its oracle message.
 `ioppLast_view`     the last case of the program's proximity test, run on the view of the written
                     rounds: if it runs through and no named test fails, the library's decision
                     holds at the last tree's word and masking word.
What is asked, as hypotheses with names. `hb`: the public facts `LastBook`. `hview`: the view's
opened columns under the tree's key are the written oracle's. `hL`, `hk`, `hmf`, `hzf`: the last
group has one member, not kept, whose rows are the first of both tables. In addition, the hypotheses
of OnBytes/Slice/BaseLast.lean on the claim and on the program's forms.
Not claimed. That these hypotheses hold.
-/
import OnBytes.Slice.BlkOpenN
import OnBytes.Slice.BaseLast
import OnBytes.Slice.LastJoint
import OnBytes.Iop.SymbolLaws

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## The twelve words of a column of the last tree -/

/-- A list of twelve members, written out. -/
theorem twelve_of_length {α : Type} (l : List α) (h : l.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : α,
      l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨b, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h; omega)

/-- The four symbols of a column of twelve words. -/
theorem lastQ_of_words (d : PQ.RD) (o : (wRound d).Orc) (x : ℕ)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : UInt64)
    (h : colW d o x = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) :
    lastQ d o x = some ((a0, a1, a2), (a3, a4, a5), (a6, a7, a8), (a9, a10, a11)) := by
  unfold lastQ
  rw [h]
  rfl

/-- The first main symbol and the first mask symbol that the program cuts out of a column, for an
oracle message of one main row over the extension field and one mask row. -/
theorem columnOf_first (x : Oracle) (m z : ℕ) (w : Array F) (h1 : x.shape.mainRows = 1)
    (h3 : x.shape.mainDeg = 3) (h2 : x.shape.maskRows = 1) :
    (Blk.columnOf x m z w).main.getD 0 zeroE =
        E.mk3 (w.getD (m + 3 * 0) 0) (w.getD (m + 3 * 0 + 1) 0) (w.getD (m + 3 * 0 + 2) 0) ∧
      (Blk.columnOf x m z w).mask.getD 0 zeroE =
        E.mk3 (w.getD (z + 3 * 0) 0) (w.getD (z + 3 * 0 + 1) 0) (w.getD (z + 3 * 0 + 2) 0) := by
  unfold Blk.columnOf
  rw [h1, h2, h3]
  constructor <;> simp [Array.getD_eq_getD_getElem?, E.mk3]

/-! ## The symbols that the base case reads are those of the last tree's word and masking word -/

/-- What is public about the last tree when the base case reads it. The oracle message o of the
last stage and the masking oracle star are the two parts of tree t. Each has one main row over the
extension field and one mask row, so a leaf's column has twelve words. -/
structure LastBook (a : Ctx) (o star t : ℕ) (tree : Tree) (xo xs : Oracle) (logN : ℕ) : Prop where
  po : a.book.place[o]? = some (t, 0)
  ps : a.book.place[star]? = some (t, 1)
  tr : a.book.trees[t]? = some tree
  log : tree.shape.logN = logN
  main : tree.shape.mainSymbols = #[3, 3]
  mask : tree.shape.maskSymbols = #[3, 3]
  ox : a.st.oracles[o]? = some xo
  sx : a.st.oracles[star]? = some xs
  o1 : xo.shape.mainRows = 1
  o3 : xo.shape.mainDeg = 3
  o2 : xo.shape.maskRows = 1
  s1 : xs.shape.mainRows = 1
  s3 : xs.shape.mainDeg = 3
  s2 : xs.shape.maskRows = 1

/-- The symbols that the program's base case reads are those of the word and the masking word of
the last tree (OnBytes/Slice/LastJoint.lean). dS is the written round that sent the tree and oS
its oracle. hview: the view's opened columns under the tree's key are the oracle's. hy: the symbols
of the two single rows are the first main symbol and the first mask symbol of the last stage's
oracle message. -/
theorem baseTie_of_view (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (dS : PQ.RD)
    (oS : (wRound dS).Orc) (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (o star t : ℕ) (tree : Tree) (xo xs : Oracle) (pos : Positions) (a c' : Ctx)
    (opened : Array (Array Column)) (y : Array E) (stars : Array Column) (hda : a.ch.dry = false)
    (hrd : (Blk.readOpened #[o, star] pos).Yields a opened c')
    (hb : LastBook a o star t tree xo xs pos.logN)
    (hview : ∀ e ∈ a.ch.opened, e.1 = tree.number - a.ch.firstTree → e.2.2 = colW dS oS e.2.1)
    (hstars : opened.back? = some stars)
    (hy : ∀ i, i < pos.all.size →
      y.getD (i * 2 + 0) zeroE = ((opened.getD 0 #[]).getD i {}).main.getD 0 zeroE ∧
      y.getD (i * 2 + 1) zeroE = ((opened.getD 0 #[]).getD i {}).mask.getD 0 zeroE) :
    BaseTie s (wordIn s (lastColW dS oS)) (wordMk s (lastMk dS oS)) pos y stars := by
  obtain ⟨cs, hcs, hop, _, _, hsz, hsym⟩ := readParts #[o, star] t pos a c' opened hda hrd tree
    (Nat.zero_lt_succ 1) (fun p hp => by
      have hp2 : p < 2 := hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp2 with h1 | rfl
      · obtain rfl : p = 0 := Nat.lt_one_iff.1 h1
        exact hb.po
      · exact hb.ps) hb.tr hb.log
  have hsz2 : opened.size = 2 := hsz
  have hso : ∀ i, i < pos.all.size → (opened.getD 0 #[]).getD i {} =
      Blk.columnOf xo (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) :=
    hsym 0 (Nat.zero_lt_succ 1) xo hb.ox
  have hst1 : opened.getD 1 #[] = stars := by
    rw [Array.back?_eq_getElem?, hsz2] at hstars
    rw [Array.getD_eq_getD_getElem?, hstars]
    rfl
  have hss : ∀ i, i < pos.all.size → stars.getD i {} =
      Blk.columnOf xs (mainSkip tree 1) (maskSkip tree 1) (cs.getD i #[]) := by
    rw [← hst1]
    exact hsym 1 (Nat.lt_succ_self 1) xs hb.sx
  have hmem : ∀ i, i < pos.all.size →
      (tree.number - a.ch.firstTree, pos.all.getD i 0, (cs.getD i #[]).toList) ∈ a.ch.opened :=
    fun i hi => by
      rw [hop]
      exact List.mem_append_left _ (viewColumns_at _ _ _ hcs i hi)
  have hk : s.h + s.g = 0 := by omega
  -- where the symbols begin in a column
  have k0 : mainSkip tree 0 = 0 := by
    unfold mainSkip
    rw [hb.main]
    rfl
  have k1 : mainSkip tree 1 = 3 := by
    unfold mainSkip
    rw [hb.main]
    rfl
  have k2 : maskSkip tree 0 = 6 := by
    unfold maskSkip TreeShape.mainWidth
    rw [hb.main, hb.mask]
    rfl
  have k3 : maskSkip tree 1 = 9 := by
    unfold maskSkip TreeShape.mainWidth
    rw [hb.main, hb.mask]
    rfl
  intro i hi hx
  -- the column's twelve words
  have hw : (cs.getD i #[]).toList = colW dS oS (pos.all.getD i 0) := hview _ (hmem i hi) rfl
  have hlen : (colW dS oS (pos.all.getD i 0)).length = 12 := by
    unfold colW
    rw [dif_pos (by rw [hN]; exact hx), List.length_ofFn, hW]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hl⟩ := twelve_of_length _ hlen
  obtain ⟨T1, T2, T3, T4⟩ := lastQ_tie dS oS _ _ (lastQ_of_words dS oS _ _ _ _ _ _ _ _ _ _ _ _ _ hl)
  have hwA : cs.getD i #[] = #[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
    rw [← Array.toArray_toList (xs := cs.getD i #[]), hw, hl]
  obtain ⟨y0, y1⟩ := hy i hi
  obtain ⟨p0, p1⟩ := columnOf_first xo (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) hb.o1
    hb.o3 hb.o2
  obtain ⟨p2, p3⟩ := columnOf_first xs (mainSkip tree 1) (maskSkip tree 1) (cs.getD i #[]) hb.s1
    hb.s3 hb.s2
  rw [k0, k2, hwA] at p0 p1
  rw [k1, k3, hwA] at p2 p3
  rw [hso i hi] at y0 y1
  refine ⟨?_, ?_, ?_, ?_⟩
  · show readE (y.getD (i * 2 + 0) zeroE) =
      vec (lastColW dS oS (pos.all.getD i 0)).main (Sz.rowNo _)
    rw [y0, k0, k2, hwA, p0, rowNo_zero hk]
    unfold vec
    rw [T1]
    rfl
  · show readE (y.getD (i * 2 + 1) zeroE) =
      vec (lastColW dS oS (pos.all.getD i 0)).mask (Sz.rowNo _)
    rw [y1, k0, k2, hwA, p1, rowNo_zero h0]
    unfold vec
    rw [T3]
    rfl
  · show readE ((stars.getD i {}).main.getD 0 zeroE) = toE (lastMk dS oS (pos.all.getD i 0)).1
    rw [hss i hi, k1, k3, hwA, p2, T2]
    rfl
  · show readE ((stars.getD i {}).mask.getD 0 zeroE) = toE (lastMk dS oS (pos.all.getD i 0)).2
    rw [hss i hi, k1, k3, hwA, p3, T4]
    rfl

/-- A column put at row 0 of an empty table: the table's first entry is the column's. -/
theorem putAt_first (col : Array E) : putAt (some 0) col (fun _ => zeroE) 0 = col.getD 0 zeroE := by
  show (if 0 ≤ 0 ∧ 0 < 0 + col.size then col.getD (0 - 0) zeroE else zeroE) = _
  by_cases h : 0 ≤ 0 ∧ 0 < 0 + col.size
  · rw [if_pos h]
  · rw [if_neg h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

/-- The symbols of the last stage's two single rows are the first main symbol and the first mask
symbol of the stage's oracle message, position by position. The message is the group's one member,
not kept, and its rows are the first of both tables. -/
theorem lastRows_read (cur : Params.IoppStage) (L : GroupLayout) (row : GroupRow) (R : SingleRows)
    (hR : ioppLastRows cur L row = some R) (hsz : L.members.size = 1)
    (hk : L.kept.getD 0 false = false) (hmf : L.mainFirst.getD 0 none = some 0)
    (hzf : L.maskFirst.getD 0 none = some 0) (opened : Array (Array Column)) (y : Array E) (n : ℕ)
    (h : singleRowsSymbols R opened n = some y) (i : ℕ) (hi : i < n) :
    y.getD (i * 2 + 0) zeroE = ((opened.getD 0 #[]).getD i {}).main.getD 0 zeroE ∧
      y.getD (i * 2 + 1) zeroE = ((opened.getD 0 #[]).getD i {}).mask.getD 0 zeroE := by
  have eR := ioppLastRows_inv cur L row R hR
  subst eR
  obtain ⟨_, _, _, hall⟩ := singleRowsSymbols_inv _ opened n y (show (1 : ℕ) ≤ 2 by decide) h
  obtain ⟨t, ht, _, h0, _, h1, _⟩ := hall i hi
  obtain ⟨_, _, _, m1, m2⟩ := tablesAt_inv _ opened i t ht fun w hw => by
    have hw1 : w < 1 := by rw [← hsz]; exact hw
    obtain rfl : w = 0 := Nat.lt_one_iff.1 hw1
    exact hk
  have e1 : t.1.getD 0 zeroE = (colB opened 0 i).main.getD 0 zeroE := by
    have q := m1 0
    have q' : t.1.getD 0 zeroE = (List.range L.members.size).foldl
        (fun base w => putAt (L.mainFirst.getD w none) (colB opened w i).main base)
        (fun _ => zeroE) 0 := q
    rw [hsz] at q'
    rw [q']
    show putAt (L.mainFirst.getD 0 none) (colB opened 0 i).main (fun _ => zeroE) 0 = _
    rw [hmf, putAt_first]
  have e2 : t.2.1.getD 0 zeroE = (colB opened 0 i).mask.getD 0 zeroE := by
    have q := m2 0
    have q' : t.2.1.getD 0 zeroE = (List.range L.members.size).foldl
        (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base)
        (fun _ => zeroE) 0 := q
    rw [hsz] at q'
    rw [q']
    show putAt (L.maskFirst.getD 0 none) (colB opened 0 i).mask (fun _ => zeroE) 0 = _
    rw [hzf, putAt_first]
  have h1' : y.getD (i * 2 + 1) zeroE = (foldLow t.2.1 (List.take L.h [])).getD 0 zeroE :=
    h1 (Nat.le_refl 1)
  rw [List.take_nil] at h1'
  exact ⟨h0.trans e1, h1'.trans e2⟩

/-- Marking an oracle message as spent keeps every oracle message's shape. -/
theorem shape_after_spend (star o : ℕ) (c c1 : Ctx) (x : Oracle)
    (h : (Blk.spendAsMask star).Yields c () c1) (hx : c.st.oracles[o]? = some x) :
    ∃ x', c1.st.oracles[o]? = some x' ∧ x'.shape = x.shape := by
  rw [Blk.spendAsMask_inv star c c1 h]
  show ∃ x', (c.st.oracles.modify star _)[o]? = some x' ∧ _
  rw [Array.getElem?_modify, hx]
  split
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- The last case of the program's proximity test on the view of the written rounds, with the
word and the masking word of the last tree. If it runs through and no named test fails, the
library's decision holds at the values of the two written rounds. -/
theorem ioppLast_view (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hza : s.Z.a ≤ s.C.a)
    (ha : s.C.a ≤ 32) (answers : ℕ) (ride : Bool) (cur : Params.IoppStage) (row : GroupRow)
    (L : GroupLayout) (o star : ℕ) (hL : L.members = #[o]) (dS dL dB : PQ.RD)
    (oS : (wRound dS).Orc) (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (mL : (wRound dL).Msg) (cL : (wRound dL).Chal) (mB : (wRound dB).Msg) (cB : (wRound dB).Chal)
    (rest : List Fmt.RoundView) (c c' : Ctx) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (h : (ioppStagesVerify answers ride cur [] row L (some star)).Yields c () c')
    (hf : c'.failed = none) {nB : ℕ} (hB : SendsDraws dB nB 0 s.t s.C.a) (cd : Code)
    (hcd : c.st.codes.base[cur.code]? = some cd) (hC : codeOf cd = s.C)
    (hZ : codeOf (c.st.codes.mask.getD cur.maskCode default) = s.Z)
    (x : GE × (s.cIn.J → GE)) (hx1 : x.1 = readE row.target)
    (hxc : ∀ j : Fin s.C.l, x.2 (.inl (fun _ => false, j)) = readE (row.c.entry (2 * j.val)))
    (hxd : ∀ j : Fin s.Z.l, x.2 (.inr (fun _ => false, j)) = readV row.d j.val)
    (hfix : FixLaw row.c [zeroE])
    (t : ℕ) (tree : Tree) (xo xs : Oracle) (hb : LastBook c o star t tree xo xs cd.logN)
    (hview : ∀ e ∈ c.ch.opened, e.1 = tree.number - c.ch.firstTree → e.2.2 = colW dS oS e.2.1)
    (hk : L.kept.getD 0 false = false) (hmf : L.mainFirst.getD 0 none = some 0)
    (hzf : L.maskFirst.getD 0 none = some 0) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1
      (s.cIn.T (wordIn s (lastColW dS oS))) (s.cIn.T (wordMk s (lastMk dS oS)))
      (lst (sentW dL mL) 0) (gOne _ (valsOf dL cL)) (shownW s (sentW dB mB))
      (gPos s.C.a s.t _ (valsOf dB cB)) := by
  refine ioppLast_sem s h0 g0 ha (hza.trans ha) answers ride cur row L star dL dB mL cL mB
    cB rest c c' hd hp h hf hB cd hcd hC hZ x _ _ hx1 hxc hxd hfix ?_
  intro R c1 a opened y stars hR hrd hda hop hbk hft hsp hst hy hstars
  have eR := ioppLastRows_inv cur L row R hR
  have hids : (singleRowsOracles R).push star = #[o, star] := by
    rw [eR]
    show (L.members).push star = _
    rw [hL]
    rfl
  rw [hids] at hrd
  obtain ⟨xo', q1, q2⟩ := shape_after_spend star o c c1 xo hsp hb.ox
  obtain ⟨xs', q3, q4⟩ := shape_after_spend star star c c1 xs hsp hb.sx
  refine baseTie_of_view s h0 g0 dS oS hW hN o star t tree xo' xs' _ a c' opened y stars hda hrd
    ⟨by rw [hbk]; exact hb.po, by rw [hbk]; exact hb.ps, by rw [hbk]; exact hb.tr, hb.log, hb.main,
      hb.mask, by rw [hst]; exact q1, by rw [hst]; exact q3, by rw [q2]; exact hb.o1,
      by rw [q2]; exact hb.o3, by rw [q2]; exact hb.o2, by rw [q4]; exact hb.s1,
      by rw [q4]; exact hb.s3, by rw [q4]; exact hb.s2⟩
    (by rw [hop, hft]; exact hview) hstars
    (lastRows_read cur L row R hR (by rw [hL]; rfl) hk hmf hzf opened y _ hy)

end OnBytes.Slice

#print axioms OnBytes.Slice.lastRows_read
#print axioms OnBytes.Slice.ioppLast_view
#print axioms OnBytes.Slice.baseTie_of_view
#print axioms OnBytes.Slice.twelve_of_length
#print axioms OnBytes.Slice.lastQ_of_words
#print axioms OnBytes.Slice.columnOf_first
#print axioms OnBytes.Slice.putAt_first
#print axioms OnBytes.Slice.shape_after_spend
