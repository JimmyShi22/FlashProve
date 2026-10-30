-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkJoin.lean: the program's link and the written link, joined.

OnBytes/Slice/BlkLink.lean shows that the rows of the program's link are the rows `rowsX` at a
statement x of the library's verifier, under two records of hypotheses: `XTie` ties x to what the
program has drawn and received, and `LinkRows` says what the program's rows are. This file meets
both records where the program runs on the view of a written transcript and x is the statement
after the five written rounds (OnBytes/Slice/CorePeel.lean: `st4`).

The hypotheses that are left speak of values alone, so that they do not depend on how a run of the
program's blocks is described: the program's values, as triples of words, are those that the
format's decision reads of the written rounds (`rvOf`); the rows were made by the program's own
calls; the column that was opened at a listed position is the column that the table's string holds
there.

Main definition: `LinkSizes`, the public sizes of the two sides against each other.
Main theorems.
 `st4_fold0`, `st4_fold1`  the folds that the library's verifier holds after the five rounds.
 `xTie_st4`     the record `XTie` at that statement.
 `linkRows_of`  the record `LinkRows`, from the calls that made the rows.
 `folds_of`, `taken_at`   the fold in a draw's row is the fold of the column that the string holds;
                a column found by its position in a list of opened columns.
 `head_rows`    the two joined: targets and coefficients of the program's rows are `tgX` and `cfX`
                at the statement after the five written rounds.

Not claimed. That a run of the program's link yields these hypotheses. Nothing on the round in which
the rows are combined.
-/
import OnBytes.Slice.BlkLink

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## The folds that the library's verifier holds -/

/-- Membership in a union, whatever the test of equality with which the union is formed. -/
private theorem mem_union_of {α : Type} (inst : DecidableEq α) {s t : Finset α} {a : α} :
    a ∈ @Union.union _ (@Finset.instUnion α inst) s t ↔ a ∈ s ∨ a ∈ t := Finset.mem_union

/-- Membership in an image, whatever the test of equality with which the image is formed. -/
private theorem mem_image_of {α β : Type} (inst : DecidableEq β) {f : α → β} {s : Finset α}
    {b : β} : b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

section
variable (S : Sz) (d1 d2 d3 d4 d5 : PQ.RD) (y : S.lk.E0.Str) (c1 : (wRound d1).Chal)
  (m2 : (wRound d2).Msg) (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c4 : (wRound d4).Chal)
  (c5 : (wRound d5).Chal)

/-- After the five rounds the library's verifier holds, for each draw in the first table, the fold
of the symbol that is at the drawn location. -/
theorem st4_fold0 (i : Fin S.P.nu0) :
    (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1.1.2.1.2 i =
      S.lk.foldSym₀ (gVec S.P.v _ (valsOf d1 c1))
        (some (.inl (.inl (y.1 ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).1 i))))) := by
  show S.lk.foldSym₀ _ (ExtSpec.ans _ _ _ _) = _
  have hm : (Sum.inl (Sum.inl ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).1 i)) :
      S.lk.E2.Pos) ∈ S.lk.vLoc.rd (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)) :=
    (mem_union_of _).2 (Or.inl ((mem_image_of _).2 ⟨i, Finset.mem_univ _, rfl⟩))
  unfold ExtSpec.ans
  rw [if_pos hm]
  rfl

/-- The same for the draws in the copy. -/
theorem st4_fold1 (i : Fin S.P.nuj) :
    (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1.1.2.2.2 i =
      S.lk.foldSym₁ (gVec S.P.v _ (valsOf d1 c1))
        (some (.inl (.inr (y.2 ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).2 i))))) := by
  show S.lk.foldSym₁ _ (ExtSpec.ans _ _ _ _) = _
  have hm : (Sum.inl (Sum.inr ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).2 i)) :
      S.lk.E2.Pos) ∈ S.lk.vLoc.rd (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)) :=
    (mem_union_of _).2 (Or.inr ((mem_image_of _).2 ⟨i, Finset.mem_univ _, rfl⟩))
  unfold ExtSpec.ans
  rw [if_pos hm]
  rfl

end

/-- An entry of an array of words is the entry of its list. -/
private theorem getD_words (col : Array F) (b : ℕ) : col.getD b 0 = col.toList.getD b 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- The program's fold of a column, with the point given as the format reads it. -/
theorem readE_foldeqSymbol_lst (gamma : List E) (els : List Fmt.M1.E) (v : ℕ)
    (hg : gamma.map E.triple = els) (hl : els.length = v) (col : Array F) :
    readE (foldeqSymbol (foldeqWeights gamma) col) =
      ∑ b ∈ Finset.range (2 ^ v), eqW v (lst els) b *
        algebraMap GF GE (toF (col.toList.getD b 0)) := by
  have hlen : gamma.length = v := by
    rw [← hl, ← hg, List.length_map]
  have hr : readL gamma = lst els := funext fun t => by rw [readL_eq_lst, hg]
  rw [readE_foldeqSymbol, hlen, hr]
  exact Finset.sum_congr rfl fun b _ => by rw [getD_words]

/-! ## The tie of the statement after the five rounds -/

/-- The statement that the library's verifier holds after the five written rounds is tied to what
the program has drawn and received, if the program's values are those that the format's decision
reads of the written rounds, and its folds are made of the columns that the two strings hold at the
drawn locations. -/
theorem xTie_st4 (S : Sz) (d1 d2 d3 d4 d5 dA : PQ.RD) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (y : S.lk.E0.Str)
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
    (gamma phi z : List E) (beta y0 y1 : E) (D0 D1 : List ℕ) (f0 f1 : ℕ → E)
    (hgamma : gamma.map E.triple = (rvOf d1 m1 c1).els)
    (hz : z.map E.triple = (rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP))
    (hbeta : beta.triple = (rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE)
    (hy0 : y0.triple = (rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE)
    (hy1 : y1.triple = (rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE)
    (hD0 : ∀ i, i < S.P.nu0 → D0.getD i 0 = (rvOf d4 m4 c4).poss.getD i 0)
    (hD1 : ∀ i, i < S.P.nuj → D1.getD i 0 = (rvOf d4 m4 c4).poss.getD (S.P.nu0 + i) 0)
    (hphi : phi.map E.triple = (rvOf d5 m5 c5).els)
    (hf0 : ∀ (i : ℕ) (x : S.Pos), i < S.P.nu0 → x.val = D0.getD i 0 → ∃ col : Array F,
      f0 i = foldeqSymbol (foldeqWeights gamma) col ∧ col.toList = (y.1 x).2)
    (hf1 : ∀ (i : ℕ) (x : S.Pos), i < S.P.nuj → x.val = D1.getD i 0 → ∃ col : Array F,
      f1 i = foldeqSymbol (foldeqWeights gamma) col ∧ col.toList = (y.2 x).2) :
    XTie S (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 phi z beta y0 y1 D0 D1 f0 f1 := by
  have hpos : ∀ n,
      (possV _ (valsOf d4 c4)).getD n 0 % 2 ^ S.P.T.a = (rvOf d4 m4 c4).poss.getD n 0 := by
    intro n
    rw [rvOf_poss, Nat.mod_eq_of_lt (getD_lt S.P.T.a _ hd.r4.allPos _ n)]
  have hne0 : lst (rvOf d2 m2 c2).els (S.P.aR + S.P.aP) ≠ 0 := by
    have h0 := elemsV_nz _ (S.P.aR + S.P.aP) hd.nz (valsOf d2 c2)
    rwa [← rvOf_els d2 m2 c2, ← toE_zeroE, List.getD_map] at h0
  have hl0 : ∀ i : Fin S.P.nu0,
      ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).1 i).val = D0.getD i.val 0 := fun i => by
    rw [hD0 i.val i.isLt]
    exact hpos i.val
  have hl1 : ∀ i : Fin S.P.nuj,
      ((gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)).2 i).val = D1.getD i.val 0 := fun i => by
    rw [hD1 i.val i.isLt]
    exact hpos (S.P.nu0 + i.val)
  have hv : (rvOf d1 m1 c1).els.length = S.P.v := hd.r1.els_length m1 c1
  refine ⟨?_, fun _ => ⟨unitOf (lst (rvOf d2 m2 c2).els (S.P.aR + S.P.aP)), ?_, ?_⟩, ?_, ?_, hl0,
    hl1, fun i => ?_, fun i => ?_⟩
  · show gVec S.P.aPhi _ (valsOf d5 c5) = _
    rw [readP_eq_ptL, hphi]
    exact gVec_rvOf d5 m5 c5 _
  · show gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2) = _
    rw [gSeed_rv d2 m2 c2, readP_eq_ptL, hz]
    rfl
  · rw [unitOf_val hne0, readE_def, hbeta]
    rfl
  · show (ansOf d3 m3).getD 0 0 = _
    rw [← rvOf_sent d3 m3 c3, ← toE_zeroE, List.getD_map, readE_def, hy0]
  · show (ansOf d3 m3).getD 1 0 = _
    rw [← rvOf_sent d3 m3 c3, ← toE_zeroE, List.getD_map, readE_def, hy1]
  · obtain ⟨col, e1, e2⟩ := hf0 i.val _ i.isLt (hl0 i)
    rw [st4_fold0, gVec_rvOf d1 m1 c1, e1, readE_foldeqSymbol_lst gamma _ S.P.v hgamma hv, e2]
    exact foldSym₀_closed S (lst (rvOf d1 m1 c1).els) _
  · obtain ⟨col, e1, e2⟩ := hf1 i.val _ i.isLt (hl1 i)
    rw [st4_fold1, gVec_rvOf d1 m1 c1, e1, readE_foldeqSymbol_lst gamma _ S.P.v hgamma hv, e2]
    exact foldSym₁_closed S (lst (rvOf d1 m1 c1).els) _

/-! ## The rows, from what a run of the program's link yields -/

/-- The public sizes of the program's link against the sizes of the written link. -/
structure LinkSizes (S : Sz) (Λ : Params.LinkShape) (codes : Codes) : Prop where
  /-- How a folded row is arranged in its oracle message. -/
  lay : vectorLay codes (Λ.side false 1).u Λ.rowsHigh = S.layU
  /-- The number of entries of the two folded rows that are compared. -/
  cut : Λ.cut = S.P.cut
  /-- The number of draws in the first table. -/
  n0 : Λ.columnsFirst = S.P.nu0
  /-- The number of draws in the copy. -/
  n1 : Λ.columnsFurther = S.P.nuj
  /-- The number of rows of a folded row's oracle message. -/
  rows : Λ.rows = S.P.R
  /-- The length of a message under the code of these rows. -/
  ell : (codes.base.getD Λ.code default).ell = S.P.C.l
  /-- The number of coordinates of the point at which a table's rows are folded. -/
  v : Λ.table.v = S.P.v
  /-- A stored table has 2 to this power positions. -/
  logN : Λ.table.code.logN = S.P.T.a
  /-- The number of coordinates of a sample's point. -/
  bits : (Send.cube codes (Λ.side false 1).u).bits = S.P.aR + S.P.aP

/-- The rows of the program's link, from the calls that made them. o0: the number of the first
folded row's oracle message; the second's is the next. z, beta: the seed. d0, d1: the two tables'
draws. list, columns: the listed positions and the opened columns of each table. The fold of a
draw's column is read off the draw's row, whose target it is. -/
theorem linkRows_of (S : Sz) (Λ : Params.LinkShape) (codes : Codes) (hS : LinkSizes S Λ codes)
    (hl2 : S.P.C.l = 2 ^ S.P.aP) (o0 : ℕ) (gamma phi z : List E) (beta y0 y1 : E)
    (d0 d1 : List ℕ) (rE row0 row1 : Row) (rows0 rows1 : List Row) (list0 list1 : Array ℕ)
    (columns0 columns1 : Array (Array F)) (hz : z.length = S.P.aR + S.P.aP)
    (hd0 : d0.length = S.P.nu0) (hd1 : d1.length = S.P.nuj)
    (heq : linkEqualityRow Λ phi ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩
      ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩ Λ.cut = some rE)
    (form0 : Send.form codes (Λ.side false 1).u o0 ⟨z, beta⟩ 0 = some row0)
    (form1 : Send.form codes (Λ.side false 1).u (o0 + 1) ⟨z, beta⟩ 0 = some row1)
    (cols0 : (d0.mapM fun x => do
      let i ← list0.idxOf? x
      foldeqColumnRow (Λ.side false 1) x (foldeqSymbol (foldeqWeights gamma) (← columns0[i]?))
        ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows0)
    (cols1 : (d1.mapM fun x => do
      let i ← list1.idxOf? x
      foldeqColumnRow (Λ.side true 1) x (foldeqSymbol (foldeqWeights gamma) (← columns1[i]?))
        ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows1) :
    LinkRows S Λ (Λ.side false 1) (Λ.side true 1) o0 (o0 + 1) phi z beta y0 y1 d0 d1
      (fun k => (rows0.getD k default).target) (fun k => (rows1.getD k default).target) rE
      { row0 with target := y0 } { row1 with target := y1 } rows0 rows1 := by
  rw [hS.lay] at heq cols0 cols1
  rw [hS.cut] at heq
  obtain ⟨l0, c0⟩ := colRows_getD _ _ _ _ _ _ _ cols0
  obtain ⟨l1, c1⟩ := colRows_getD _ _ _ _ _ _ _ cols1
  have hsmp : ∀ (o : ℕ) (row : Row), Send.form codes (Λ.side false 1).u o ⟨z, beta⟩ 0 = some row →
      ∀ β : GEˣ, β.val = readE beta → ∀ i, i < 2 ^ (S.P.aR + S.P.aP) →
        coefAt row o .main i = S.smpC (readP (S.P.aR + S.P.aP) z, β) i := fun o row h β hβ i hi =>
    coefAt_smpRow S codes _ o z beta row hS.rows rfl rfl rfl hS.ell hl2 hz h β hβ i hi
  refine ⟨heq, hsmp o0 row0 form0, hsmp (o0 + 1) row1 form1, fun i => ?_, fun i => ?_, rfl, rfl,
    l0.trans hd0, l1.trans hd1, fun k hk => ?_, fun k hk => ?_⟩
  · exact coefAt_form_other codes _ o0 _ 0 row0 form0 (o0 + 1) (Nat.succ_ne_self o0) .main i
  · exact coefAt_form_other codes _ (o0 + 1) _ 0 row1 form1 o0 (Nat.succ_ne_self o0).symm .main i
  · obtain ⟨i, col, -, -, h⟩ := c0 k (by rw [hd0]; exact hk)
    show foldeqColumnRow _ _ (rows0.getD k default).target _ = _
    rw [(colRow_target _ _ _ _ _ h).1]
    exact h
  · obtain ⟨i, col, -, -, h⟩ := c1 k (by rw [hd1]; exact hk)
    show foldeqColumnRow _ _ (rows1.getD k default).target _ = _
    rw [(colRow_target _ _ _ _ _ h).1]
    exact h

/-- The folds of the draws' columns. If the column that was opened at a listed position is the
column that a string w holds there, then the target of each draw's row is the program's fold of the
column that w holds at the draw. -/
theorem folds_of {n : ℕ} (w : Fin n → List UInt64) (Sf : Params.FoldeqShape) (eqGamma : Array E)
    (u : FoldedRow) (list : Array ℕ) (columns : Array (Array F)) (draws : List ℕ)
    (rows : List Row)
    (h : (draws.mapM fun x => do
      let i ← list.idxOf? x
      foldeqColumnRow Sf x (foldeqSymbol eqGamma (← columns[i]?)) u) = some rows)
    (hcol : ∀ (i : ℕ) (col : Array F) (x : Fin n), list.idxOf? x.val = some i →
      columns[i]? = some col → col.toList = w x)
    (k : ℕ) (x : Fin n) (hk : k < draws.length) (hx : x.val = draws.getD k 0) :
    ∃ col : Array F, (rows.getD k default).target = foldeqSymbol eqGamma col ∧
      col.toList = w x := by
  obtain ⟨i, col, h1, h2, h3⟩ := (colRows_getD _ _ _ _ _ _ _ h).2 k hk
  rw [← hx] at h1
  exact ⟨col, (colRow_target _ _ _ _ _ h3).1, hcol i col x h1 h2⟩

/-- A column that is in a list of opened columns, found by its position. L: the opened columns,
each with a key and a position; l: the listed positions. If the two lists go side by side, the
column at the place of the position x in l is an entry of L under the key and at x. -/
theorem taken_at (L : List (ℕ × ℕ × List UInt64)) (l : List ℕ) (key W : ℕ)
    (hlen : L.length = l.length)
    (hall : ((L.zip l).all fun y =>
      y.1.1 == key && y.1.2.1 == y.2 && y.1.2.2.length == W) = true)
    (x idx : ℕ) (col : Array F) (hi : l.toArray.idxOf? x = some idx)
    (hc : ((L.map fun y => y.2.2.toArray).toArray)[idx]? = some col) :
    ∃ o ∈ L, o.1 = key ∧ o.2.1 = x ∧ col.toList = o.2.2 := by
  rw [List.idxOf?_toArray] at hi
  obtain ⟨h1, h2, -⟩ := List.idxOf?_eq_some_iff.1 hi
  have hL : idx < L.length := hlen ▸ h1
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hL] at hc
  have hcol : (L[idx]).2.2.toArray = col := Option.some.inj hc
  have hz : (L[idx], l[idx]) ∈ L.zip l := by
    have h3 : idx < (L.zip l).length := by
      rw [List.length_zip]
      omega
    have h4 := List.getElem_mem h3
    rwa [List.getElem_zip] at h4
  have h5 := List.all_eq_true.1 hall _ hz
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  exact ⟨L[idx], List.getElem_mem hL, h5.1.1, h5.1.2.trans h2, by rw [← hcol]⟩

/-! ## The two sides joined -/

/-- The rows of the program's link, run on the view of a written transcript, are the rows of
`rowsX` at the statement after the five written rounds. What is asked: the sizes agree; the
program's values are those that the format's decision reads of the written rounds; the rows were
made by the program's calls; the column that was opened at a listed position is the column that the
table's string holds there. -/
theorem head_rows (S : Sz) (Λ : Params.LinkShape) (codes : Codes) (hS : LinkSizes S Λ codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (d1 d2 d3 d4 d5 dA : PQ.RD)
    (hd : BatDraws S d1 d2 d3 d4 d5 dA) (y : S.lk.E0.Str)
    (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
    (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
    (o0 : ℕ) (gamma phi z : List E) (beta y0 y1 : E) (D0 D1 : List ℕ) (rE row0 row1 : Row)
    (rows0 rows1 : List Row) (list0 list1 : Array ℕ) (columns0 columns1 : Array (Array F))
    (hgamma : gamma.map E.triple = (rvOf d1 m1 c1).els)
    (hz : z.map E.triple = (rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP))
    (hbeta : beta.triple = (rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE)
    (hy0 : y0.triple = (rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE)
    (hy1 : y1.triple = (rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE)
    (hl0 : D0.length = S.P.nu0) (hl1 : D1.length = S.P.nuj)
    (hD0 : ∀ i, i < S.P.nu0 → D0.getD i 0 = (rvOf d4 m4 c4).poss.getD i 0)
    (hD1 : ∀ i, i < S.P.nuj → D1.getD i 0 = (rvOf d4 m4 c4).poss.getD (S.P.nu0 + i) 0)
    (hphi : phi.map E.triple = (rvOf d5 m5 c5).els)
    (heq : linkEqualityRow Λ phi ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩
      ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩ Λ.cut = some rE)
    (form0 : Send.form codes (Λ.side false 1).u o0 ⟨z, beta⟩ 0 = some row0)
    (form1 : Send.form codes (Λ.side false 1).u (o0 + 1) ⟨z, beta⟩ 0 = some row1)
    (cols0 : (D0.mapM fun x => do
      let i ← list0.idxOf? x
      foldeqColumnRow (Λ.side false 1) x (foldeqSymbol (foldeqWeights gamma) (← columns0[i]?))
        ⟨o0, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows0)
    (cols1 : (D1.mapM fun x => do
      let i ← list1.idxOf? x
      foldeqColumnRow (Λ.side true 1) x (foldeqSymbol (foldeqWeights gamma) (← columns1[i]?))
        ⟨o0 + 1, vectorLay codes (Λ.side false 1).u Λ.rowsHigh⟩) = some rows1)
    (hcol0 : ∀ (i : ℕ) (col : Array F) (x : S.Pos), list0.idxOf? x.val = some i →
      columns0[i]? = some col → col.toList = (y.1 x).2)
    (hcol1 : ∀ (i : ℕ) (col : Array F) (x : S.Pos), list1.idxOf? x.val = some i →
      columns1[i]? = some col → col.toList = (y.2 x).2)
    (b : ℕ) (hb : b < S.nRows) :
    readE ((rE :: { row0 with target := y0 } :: { row1 with target := y1 } ::
        (rows0 ++ rows1)).getD b default).target =
        tgX S (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 b ∧
      ∀ (a : Bool) (r p : ℕ), r < 2 ^ S.P.aR → p < 2 ^ S.P.aP →
        coefAt ((rE :: { row0 with target := y0 } :: { row1 with target := y1 } ::
          (rows0 ++ rows1)).getD b default) (if a then o0 + 1 else o0) .main
          (r + 2 ^ S.P.aR * p) =
          cfX S (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 b a r p := by
  have hzl : z.length = S.P.aR + S.P.aP := by
    have h1 := congrArg List.length hz
    rw [List.length_map, List.length_take, hd.r2.els_length m2 c2] at h1
    omega
  have hR := linkRows_of S Λ codes hS hF.pow o0 gamma phi z beta y0 y1 D0 D1 rE row0 row1 rows0
    rows1 list0 list1 columns0 columns1 hzl hl0 hl1 heq form0 form1 cols0 cols1
  have hx := xTie_st4 S d1 d2 d3 d4 d5 dA hd y m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 gamma phi z beta y0 y1
    D0 D1 (fun k => (rows0.getD k default).target) (fun k => (rows1.getD k default).target) hgamma
    hz hbeta hy0 hy1 hD0 hD1 hphi
    (fun i x hi hx => folds_of (fun x => (y.1 x).2) _ _ _ _ _ _ _ cols0 hcol0 i x
      (by rw [hl0]; exact hi) hx)
    (fun i x hi hx => folds_of (fun x => (y.2 x).2) _ _ _ _ _ _ _ cols1 hcol1 i x
      (by rw [hl1]; exact hi) hx)
  exact rows_cfX S Λ _ _ o0 (o0 + 1) (Nat.succ_ne_self o0).symm _ phi z beta y0 y1 D0 D1 _ _ rE _ _
    rows0 rows1 hF hx hR b hb

end OnBytes.Slice

#print axioms OnBytes.Slice.st4_fold0
#print axioms OnBytes.Slice.st4_fold1
#print axioms OnBytes.Slice.readE_foldeqSymbol_lst
#print axioms OnBytes.Slice.xTie_st4
#print axioms OnBytes.Slice.linkRows_of
#print axioms OnBytes.Slice.folds_of
#print axioms OnBytes.Slice.taken_at
#print axioms OnBytes.Slice.head_rows
#print axioms OnBytes.Slice.mem_union_of
#print axioms OnBytes.Slice.mem_image_of
#print axioms OnBytes.Slice.getD_words
