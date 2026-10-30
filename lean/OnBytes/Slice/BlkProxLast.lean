-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxLast.lean: the base case's reading takes the last tree's segment of the columns
that are left to be read.

OnBytes/Slice/BaseOpen.lean ties the symbols that the program's base case reads to the last written
tree, if all opened columns that are left under the tree's key are the tree's. This file asks less:
what is left begins with the tree's segment at the base case's positions
(OnBytes/Slice/BlkProxSeg.lean). Nothing is asked of what comes after it, and that is what the run
leaves.

Main theorems.
  baseTie_of_seg   the symbols read are those of the word and the masking word of the last tree.
  lastTie_seg      the same for the last case of the program's proximity test.
  ioppLast_left    if the last case runs through, the rounds and the columns behind the base case's
                   are left, whether a named test has failed or not.
  ioppLast_seg     if the last case runs through and no named test fails, the library's decision
                   holds.

Not claimed. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxKeeps
import OnBytes.Slice.BlkProxSeg

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run

/-- The symbols that the program's base case reads are those of the word and the masking word of
the last tree, and what comes after the tree's segment is left. dS, mS: the written round that sent
the tree, and its message. hy: the symbols of the two single rows are the first main symbol and the
first mask symbol of the last stage's oracle message. -/
theorem baseTie_of_seg (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (dS : PQ.RD)
    (mS : (wRound dS).Msg) (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (o star t : ℕ) (tree : Tree) (xo xs : Oracle) (pos : Positions) (a c' : Ctx)
    (opened : Array (Array Column)) (y : Array E) (stars : Array Column) (hda : a.ch.dry = false)
    (hrd : (Blk.readOpened #[o, star] pos).Yields a opened c')
    (hb : LastBook a o star t tree xo xs pos.logN) (R : Cols)
    (hop : a.ch.opened =
      segOf (tree.number - a.ch.firstTree) pos.all.toList (treeCol dS mS) ++ R)
    (hin : ∀ x ∈ pos.all.toList, (treeCol dS mS x).isSome = true)
    (hstars : opened.back? = some stars)
    (hy : ∀ i, i < pos.all.size →
      y.getD (i * 2 + 0) zeroE = ((opened.getD 0 #[]).getD i {}).main.getD 0 zeroE ∧
      y.getD (i * 2 + 1) zeroE = ((opened.getD 0 #[]).getD i {}).mask.getD 0 zeroE) :
    BaseTie s (wordIn s (lastColW dS mS.1)) (wordMk s (lastMk dS mS.1)) pos y stars ∧
      c'.ch.opened = R := by
  obtain ⟨cs, hcs, hop', _, _, hsz, hsym⟩ := readParts #[o, star] t pos a c' opened hda hrd tree
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
  obtain ⟨eR, hval⟩ := seg_cut _ pos.all cs (treeCol dS mS) _ R _ hcs hop' hop hin
  refine ⟨?_, eR⟩
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
  have hw : (cs.getD i #[]).toList = colW dS mS.1 (pos.all.getD i 0) :=
    treeCol_some _ _ _ _ (hval i hi)
  have hlen : (colW dS mS.1 (pos.all.getD i 0)).length = 12 := by
    unfold colW
    rw [dif_pos (by rw [hN]; exact hx), List.length_ofFn, hW]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hl⟩ := twelve_of_length _ hlen
  obtain ⟨T1, T2, T3, T4⟩ :=
    lastQ_tie dS mS.1 _ _ (lastQ_of_words dS mS.1 _ _ _ _ _ _ _ _ _ _ _ _ _ hl)
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
      vec (lastColW dS mS.1 (pos.all.getD i 0)).main (Sz.rowNo _)
    rw [y0, k0, k2, hwA, p0, rowNo_zero hk]
    unfold vec
    rw [T1]
    rfl
  · show readE (y.getD (i * 2 + 1) zeroE) =
      vec (lastColW dS mS.1 (pos.all.getD i 0)).mask (Sz.rowNo _)
    rw [y1, k0, k2, hwA, p1, rowNo_zero h0]
    unfold vec
    rw [T3]
    rfl
  · show readE ((stars.getD i {}).main.getD 0 zeroE) = toE (lastMk dS mS.1 (pos.all.getD i 0)).1
    rw [hss i hi, k1, k3, hwA, p2, T2]
    rfl
  · show readE ((stars.getD i {}).mask.getD 0 zeroE) = toE (lastMk dS mS.1 (pos.all.getD i 0)).2
    rw [hss i hi, k1, k3, hwA, p3, T4]
    rfl

/-- The reading of the last case of the program's proximity test. c: the context before the case;
a: the context in which the columns are read; c': the context that the case leaves. -/
theorem lastTie_seg (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (cur : Params.IoppStage)
    (row : GroupRow) (L : GroupLayout) (o star : ℕ) (hL : L.members = #[o]) (dS : PQ.RD)
    (mS : (wRound dS).Msg) (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (c c' : Ctx) (t : ℕ) (tree : Tree) (xo xs : Oracle) (pos : Positions)
    (hb : LastBook c o star t tree xo xs pos.logN) (Rr : Cols)
    (hop : c.ch.opened =
      segOf (tree.number - c.ch.firstTree) pos.all.toList (treeCol dS mS) ++ Rr)
    (hin : ∀ x ∈ pos.all.toList, (treeCol dS mS x).isSome = true)
    (hk : L.kept.getD 0 false = false) (hmf : L.mainFirst.getD 0 none = some 0)
    (hzf : L.maskFirst.getD 0 none = some 0) (R : SingleRows) (c1 a : Ctx)
    (opened : Array (Array Column)) (y : Array E) (stars : Array Column)
    (hR : ioppLastRows cur L row = some R)
    (hrd : (Blk.readOpened ((singleRowsOracles R).push star) pos).Yields a opened c')
    (hda : a.ch.dry = false) (hopa : a.ch.opened = c.ch.opened) (hbk : a.book = c.book)
    (hft : a.ch.firstTree = c.ch.firstTree) (hsp : (Blk.spendAsMask star).Yields c () c1)
    (hst : a.st = c1.st) (hy : singleRowsSymbols R opened pos.all.size = some y)
    (hstars : opened.back? = some stars) :
    BaseTie s (wordIn s (lastColW dS mS.1)) (wordMk s (lastMk dS mS.1)) pos y stars ∧
      c'.ch.opened = Rr := by
  have eR := ioppLastRows_inv cur L row R hR
  have hids : (singleRowsOracles R).push star = #[o, star] := by
    rw [eR]
    show (L.members).push star = _
    rw [hL]
    rfl
  rw [hids] at hrd
  obtain ⟨xo', q1, q2⟩ := shape_after_spend star o c c1 xo hsp hb.ox
  obtain ⟨xs', q3, q4⟩ := shape_after_spend star star c c1 xs hsp hb.sx
  exact baseTie_of_seg s h0 g0 dS mS hW hN o star t tree xo' xs' _ a c' opened y stars hda hrd
    ⟨by rw [hbk]; exact hb.po, by rw [hbk]; exact hb.ps, by rw [hbk]; exact hb.tr, hb.log, hb.main,
      hb.mask, by rw [hst]; exact q1, by rw [hst]; exact q3, by rw [q2]; exact hb.o1,
      by rw [q2]; exact hb.o3, by rw [q2]; exact hb.o2, by rw [q4]; exact hb.s1,
      by rw [q4]; exact hb.s3, by rw [q4]; exact hb.s2⟩ Rr
    (by rw [hopa, hft]; exact hop) hin hstars
    (lastRows_read cur L row R hR (by rw [hL]; rfl) hk hmf hzf opened y _ hy)

/-- A reading of the two parts of one tree takes the tree's segment and leaves the rest. -/
theorem lastLeft_seg (o star t : ℕ) (tree : Tree) (pos : Positions) (a a' : Ctx)
    (opened : Array (Array Column)) (hda : a.ch.dry = false)
    (hrd : (Blk.readOpened #[o, star] pos).Yields a opened a')
    (hpo : a.book.place[o]? = some (t, 0)) (hps : a.book.place[star]? = some (t, 1))
    (htr : a.book.trees[t]? = some tree) (hlog : tree.shape.logN = pos.logN)
    (f : ℕ → Option (List UInt64)) (R : Cols)
    (hop : a.ch.opened = segOf (tree.number - a.ch.firstTree) pos.all.toList f ++ R)
    (hin : ∀ x ∈ pos.all.toList, (f x).isSome = true) : a'.ch.opened = R := by
  obtain ⟨cs, hcs, hop', _⟩ := readParts #[o, star] t pos a a' opened hda hrd tree
    (Nat.zero_lt_succ 1) (fun p hp => by
      have hp2 : p < 2 := hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp2 with h1 | rfl
      · obtain rfl : p = 0 := Nat.lt_one_iff.1 h1
        exact hpo
      · exact hps) htr hlog
  exact (seg_cut _ pos.all cs f _ R _ hcs hop' hop hin).1

/-- What the last case of the program's proximity test leaves, whether a named test has failed
or not: the rounds and the columns behind the base case's; no root was received. -/
theorem ioppLast_left (s : Sg) (answers : ℕ) (ride : Bool) (cur : Params.IoppStage)
    (row : GroupRow) (L : GroupLayout) (o star : ℕ) (hL : L.members = #[o]) (dS dL dB : PQ.RD)
    (mS : (wRound dS).Msg) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (mL : (wRound dL).Msg) (cL : (wRound dL).Chal) (mB : (wRound dB).Msg) (cB : (wRound dB).Chal)
    (rest : List Fmt.RoundView) (c c' : Ctx) (hd : c.ch.dry = false)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dL, dB] (mL, cL, mB, cB, ()) ++ rest)
    (h : (ioppStagesVerify answers ride cur [] row L (some star)).Yields c () c')
    {nB : ℕ} (hB : SendsDraws dB nB 0 s.t s.C.a) (cd : Code)
    (hcd : c.st.codes.base[cur.code]? = some cd) (hC : codeOf cd = s.C)
    (t : ℕ) (tree : Tree) (xo xs : Oracle) (hb : LastBook c o star t tree xo xs cd.logN)
    (Rr : Cols)
    (hop : c.ch.opened = segOf (tree.number - c.ch.firstTree)
      (listAt s.C.a dB mB cB).all.toList (treeCol dS mS) ++ Rr) :
    c'.ch.pending = rest ∧ c'.ch.opened = Rr ∧ c'.ch.roots = c.ch.roots := by
  have hlog : cd.logN = s.C.a := congrArg (·.a) hC
  obtain ⟨R, hR, hrun⟩ := ioppStages_last_inv answers ride cur row L (some star) c c' h
  have eR := ioppLastRows_inv cur L row R hR
  obtain ⟨E, code, c1, a, a', d, opened, b1, _, b3, b4, b5, b6, b7, b8, _, b10⟩ :=
    baseVerify_cut (n0 := 0) (g0 := 0) (sp := fun _ => True) R star 0 c c' hd (Or.inl trivial) hrun
  refine ⟨by rw [E.pending, hp]; rfl, ?_, E.still rfl⟩
  have ecode : code = cd := by
    rw [eR] at b1
    exact Option.some.inj (b1.symm.trans hcd)
  have hposs : d.poss = (rvOf dB mB cB).poss := by
    rw [hp] at b3
    rw [← Option.some.inj b3]
    rfl
  have hids : (singleRowsOracles R).push star = #[o, star] := by
    rw [eR]
    show (L.members).push star = _
    rw [hL]
    rfl
  rw [hids, ecode, hlog, hposs] at b4
  rw [b10]
  refine lastLeft_seg o star t tree (listAt s.C.a dB mB cB) a a' opened b5 b4
    (by rw [b7]; exact hb.po) (by rw [b7]; exact hb.ps) (by rw [b7]; exact hb.tr)
    (hb.log.trans hlog) (treeCol dS mS) Rr (by rw [b6, b8]; exact hop) fun x hx => ?_
  have hlt := hB.poss_lt mB cB x (mem_listAt _ _ _ _ x hx)
  unfold treeCol
  rw [if_pos (by rw [hN]; exact hlt)]
  rfl

/-- The last case of the program's proximity test on the view of the written rounds, with the
word and the masking word of the last tree. If it runs through and no named test fails, the
library's decision holds at the values of the two written rounds. -/
theorem ioppLast_seg (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hza : s.Z.a ≤ s.C.a)
    (ha : s.C.a ≤ 32) (answers : ℕ) (ride : Bool) (cur : Params.IoppStage) (row : GroupRow)
    (L : GroupLayout) (o star : ℕ) (hL : L.members = #[o]) (dS dL dB : PQ.RD)
    (mS : (wRound dS).Msg) (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
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
    (Rr : Cols)
    (hop : c.ch.opened = segOf (tree.number - c.ch.firstTree)
      (listAt s.C.a dB mB cB).all.toList (treeCol dS mS) ++ Rr)
    (hk : L.kept.getD 0 false = false) (hmf : L.mainFirst.getD 0 none = some 0)
    (hzf : L.maskFirst.getD 0 none = some 0) :
    LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) x) x.1
      (s.cIn.T (wordIn s (lastColW dS mS.1))) (s.cIn.T (wordMk s (lastMk dS mS.1)))
      (lst (sentW dL mL) 0) (gOne _ (valsOf dL cL)) (shownW s (sentW dB mB))
      (gPos s.C.a s.t _ (valsOf dB cB)) := by
  have hlog : cd.logN = s.C.a := congrArg (·.a) hC
  have hpos : Positions.ofDraws cd.logN (rvOf dB mB cB).poss = listAt s.C.a dB mB cB := by
    rw [hlog]
    rfl
  have hin : ∀ x ∈ (listAt s.C.a dB mB cB).all.toList, (treeCol dS mS x).isSome = true := by
    intro x hx
    have hlt := hB.poss_lt mB cB x (mem_listAt _ _ _ _ x hx)
    unfold treeCol
    rw [if_pos (by rw [hN]; exact hlt)]
    rfl
  have tie := fun R c1 a opened y stars hR hrd hda hopa hbk hft hsp hst hy hstars =>
    lastTie_seg s h0 g0 cur row L o star hL dS mS hW hN c c' t tree xo xs
      (Positions.ofDraws cd.logN (rvOf dB mB cB).poss) hb Rr (by rw [hpos]; exact hop)
      (by rw [hpos]; exact hin) hk hmf hzf R c1 a opened y stars hR hrd hda hopa hbk hft hsp hst hy
      hstars
  exact ioppLast_sem s h0 g0 ha (hza.trans ha) answers ride cur row L star dL dB mL cL mB
    cB rest c c' hd hp h hf hB cd hcd hC hZ x _ _ hx1 hxc hxd hfix
    fun R c1 a opened y stars hR hrd hda hopa hbk hft hsp hst hy hstars =>
      (tie R c1 a opened y stars hR hrd hda hopa hbk hft hsp hst hy hstars).1

end OnBytes.Slice.ProxRun
