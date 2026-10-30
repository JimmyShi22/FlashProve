-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxGp.lean: the first code switch of a proximity test on a group of sent messages
reads the group's word.

OnBytes/Slice/KeyGroup.lean makes one word on a stage's tables of the sent words of a group's
members (Gp.word): each member's rows at its places, a mask row of a shorter tree read periodically,
zeros elsewhere. This file shows that the program reads that word. The members and the fold's fresh
mask may lie in several trees, of this chain or of an earlier one; a tree may be shorter than the
range of the positions; main rows may be over the base field.

Main definitions.
  Lay.cm, Lay.cz   a member's symbols out of a written oracle's columns, by position and row.
  rdM, rdZ         the symbols of the group's two tables, by position and row's number.
  Part1            an oracle message has a shape and is a part of a tree with a shape and a number.
  GpData           what is public of a group on the program's side: the members' numbers, shapes,
                   trees, blocks of rows; the same of the fresh mask; the trees that are opened.
  GpData.Pub       the public facts that tie these data to the group.
  LayG, GpTie, GpFit   the layout's clauses; the ties before and after the first fold.
Main theorems.
  read_main3, read_main1, read_mask   a symbol that the program cuts out of a written column.
  wordOf_rd        the word of rdM and rdZ is the group's word.
  rdM_hit, rdM_miss, rdZ_hit, rdZ_miss   their values in a member's block, and outside all blocks.
  Part1.keeps      the clause lasts as long as book and statement keep what is public.

Not claimed. That a run of the program reaches the ties. The public facts, which are hypotheses.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxChain
import OnBytes.Slice.BlkProxMany
import OnBytes.Slice.BlkProxTables
import OnBytes.Slice.KeyPlaces

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run

/-! ## A written column's words, in the field -/

/-- A word of a written column. -/
theorem colW_getD (d : PQ.RD) (o : (wRound d).Orc) (x k : ℕ) :
    (colW d o x).getD k 0 = wordAt d o x k := by
  unfold colW wordAt
  by_cases hx : x < PQ.posN d.tree
  · rw [dif_pos hx, dif_pos hx]
    by_cases hk : k < PQ.colW d.tree
    · rw [dif_pos hk, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk),
        List.getElem_ofFn]
    · rw [dif_neg hk, List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
  · rw [dif_neg hx, dif_neg hx]
    rfl

/-- Three words of a written column, as an element of the extension field. -/
theorem sym3_colW (d : PQ.RD) (o : (wRound d).Orc) (x k : ℕ) :
    toE (sym3 (colW d o x) k) = symW d o x k := by
  unfold sym3 symW
  rw [colW_getD, colW_getD, colW_getD]

/-- A main symbol over the extension field that the program cuts out of a written column. -/
theorem read_main3 (x : Oracle) (m z : ℕ) (cw : Array OnBytes.F) (d : PQ.RD) (o : (wRound d).Orc)
    (x' : ℕ) (hcw : cw.toList = colW d o x') (b : ℕ) (hb : b < x.shape.mainRows)
    (h3 : x.shape.mainDeg = 3) :
    readV (Blk.columnOf x m z cw).main b = symW d o x' (m + 3 * b) := by
  rw [columnOf_main x m z cw b hb h3, hcw, sym3_colW]

/-- A mask symbol that the program cuts out of a written column. -/
theorem read_mask (x : Oracle) (m z : ℕ) (cw : Array OnBytes.F) (d : PQ.RD) (o : (wRound d).Orc)
    (x' : ℕ) (hcw : cw.toList = colW d o x') (b : ℕ) (hb : b < x.shape.maskRows) :
    readV (Blk.columnOf x m z cw).mask b = symW d o x' (z + 3 * b) := by
  rw [columnOf_mask x m z cw b hb, hcw, sym3_colW]

/-- A main symbol over the base field that the program cuts out of a written column. -/
theorem read_main1 (x : Oracle) (m z : ℕ) (cw : Array OnBytes.F) (d : PQ.RD) (o : (wRound d).Orc)
    (x' : ℕ) (hcw : cw.toList = colW d o x') (b : ℕ) (hb : b < x.shape.mainRows)
    (h1 : x.shape.mainDeg = 1) :
    readV (Blk.columnOf x m z cw).main b = symF d o x' (m + b) := by
  have e : (Blk.columnOf x m z cw).main.getD b zeroE = OnBytes.ofF (cw.getD (m + b) 0) := by
    unfold Blk.columnOf
    simp [Array.getD_eq_getD_getElem?, hb, h1]
  have e2 : cw.getD (m + b) 0 = wordAt d o x' (m + b) := by
    rw [← colW_getD, ← hcw, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]
  unfold readV symF
  rw [e, readE_ofF, e2]

/-! ## The group's two tables, by numbers -/

/-- The number of the vertex with the number j. -/
theorem rowNo_vtx (k j : ℕ) (hj : j < 2 ^ k) : Sz.rowNo (vtx k j) = j := by
  unfold vtx
  rw [rowNo_testBit, Nat.mod_eq_of_lt hj]

/-- The vertex with a vertex's number. -/
theorem vtx_rowNo (k : ℕ) (b : Fin k → Bool) : vtx k (Sz.rowNo b) = b :=
  funext fun t => testBit_rowNo b t

/-- A vertex is the one with the number j exactly if j is its number. -/
theorem vtx_eq_iff (k j : ℕ) (hj : j < 2 ^ k) (b : Fin k → Bool) :
    vtx k j = b ↔ j = Sz.rowNo b :=
  ⟨fun h => by rw [← h, rowNo_vtx k j hj], fun h => by rw [h, vtx_rowNo]⟩

/-- A member's main symbols out of a written oracle's columns: position, then row. -/
def _root_.OnBytes.Slice.Lay.cm (L : Lay) (d : PQ.RD) (o : (wRound d).Orc) (x i : ℕ) : GE :=
  if L.base then symF d o x (L.oM + i) else symW d o x (L.oM + 3 * i)

/-- A member's mask symbols out of a written oracle's columns: position, then row. -/
def _root_.OnBytes.Slice.Lay.cz (L : Lay) (d : PQ.RD) (o : (wRound d).Orc) (x i : ℕ) : GE :=
  symW d o x (L.oZ + 3 * i)

section
variable {s : Sg} (G : Gp s)

/-- The symbol of row number b of the group's main table at the position x. oM i: the first row of
member i. cm i: the member's main symbols. -/
def rdM (oM : G.ι → ℕ) (cm : G.ι → ℕ → ℕ → GE) (x b : ℕ) : GE :=
  ∑ n : G.RM, if oM n.1 + n.2.val = b then cm n.1 x n.2.val else 0

/-- The symbol of row number b of the group's mask table at the position x: a member's mask rows are
read at x modulo the length of the member's tree. -/
def rdZ (oZ : G.ι → ℕ) (cz : G.ι → ℕ → ℕ → GE) (x b : ℕ) : GE :=
  ∑ n : G.RZ, if oZ n.1 + n.2.val = b then cz n.1 (x % 2 ^ (G.mb n.1).a) n.2.val else 0

variable {G}

/-- The word of the two readers is the group's word. -/
theorem wordOf_rd {oM oZ : G.ι → ℕ} (hN : G.Numbered oM oZ) (cm cz : G.ι → ℕ → ℕ → GE) :
    wordOf s (rdM G oM cm) (rdZ G oZ cz) = G.word fun i => (G.mb i).word (cm i) (cz i) := by
  funext p
  rcases p with x | x
  · funext a
    refine Finset.sum_congr rfl fun n _ => ?_
    have hlt : oM n.1 + n.2.val < 2 ^ (s.h + s.g) :=
      lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hN.roomM n.1)
    rw [hN.pM]
    by_cases h : oM n.1 + n.2.val = Sz.rowNo a.1
    · rw [if_pos h, if_pos ((vtx_eq_iff _ _ hlt _).2 h)]
      rfl
    · rw [if_neg h, if_neg fun e => h ((vtx_eq_iff _ _ hlt _).1 e)]
  · funext a
    refine Finset.sum_congr rfl fun n _ => ?_
    have hlt : oZ n.1 + n.2.val < 2 ^ s.h :=
      lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hN.roomZ n.1)
    rw [hN.pZ]
    by_cases h : oZ n.1 + n.2.val = Sz.rowNo a.1
    · rw [if_pos h, if_pos ((vtx_eq_iff _ _ hlt _).2 h)]
      rfl
    · rw [if_neg h, if_neg fun e => h ((vtx_eq_iff _ _ hlt _).1 e)]

/-- In a member's block the main table has the member's symbol. -/
theorem rdM_hit {oM oZ : G.ι → ℕ} (hN : G.Numbered oM oZ) (cm : G.ι → ℕ → ℕ → GE) (x : ℕ)
    (i : G.ι) (r : ℕ) (hr : r < (G.mb i).nM) : rdM G oM cm x (oM i + r) = cm i x r := by
  unfold rdM
  rw [Finset.sum_eq_single (⟨i, ⟨r, hr⟩⟩ : G.RM)]
  · exact if_pos rfl
  · rintro ⟨i', r'⟩ _ hne
    refine if_neg fun e => hne ?_
    have e' : oM i' + r'.val = oM i + r := e
    have hr' := r'.isLt
    by_cases hi : i' = i
    · subst hi
      have : r' = ⟨r, hr⟩ := Fin.ext (Nat.add_left_cancel e')
      rw [this]
    · rcases hN.apartM i' i hi with h | h <;> omega
  · exact fun h => absurd (Finset.mem_univ _) h

/-- In a member's block the mask table has the member's symbol, at the position modulo the length of
the member's tree. -/
theorem rdZ_hit {oM oZ : G.ι → ℕ} (hN : G.Numbered oM oZ) (cz : G.ι → ℕ → ℕ → GE) (x : ℕ)
    (i : G.ι) (r : ℕ) (hr : r < (G.mb i).nZ) :
    rdZ G oZ cz x (oZ i + r) = cz i (x % 2 ^ (G.mb i).a) r := by
  unfold rdZ
  rw [Finset.sum_eq_single (⟨i, ⟨r, hr⟩⟩ : G.RZ)]
  · exact if_pos rfl
  · rintro ⟨i', r'⟩ _ hne
    refine if_neg fun e => hne ?_
    have e' : oZ i' + r'.val = oZ i + r := e
    have hr' := r'.isLt
    by_cases hi : i' = i
    · subst hi
      have : r' = ⟨r, hr⟩ := Fin.ext (Nat.add_left_cancel e')
      rw [this]
    · rcases hN.apartZ i' i hi with h | h <;> omega
  · exact fun h => absurd (Finset.mem_univ _) h

/-- Outside all members' rows the main table is 0. -/
theorem rdM_miss (oM : G.ι → ℕ) (cm : G.ι → ℕ → ℕ → GE) (x b : ℕ)
    (h : ∀ (i : G.ι) (r : ℕ), r < (G.mb i).nM → oM i + r ≠ b) : rdM G oM cm x b = 0 :=
  Finset.sum_eq_zero fun n _ => if_neg (h n.1 n.2.val n.2.isLt)

/-- Outside all members' rows the mask table is 0. -/
theorem rdZ_miss (oZ : G.ι → ℕ) (cz : G.ι → ℕ → ℕ → GE) (x b : ℕ)
    (h : ∀ (i : G.ι) (r : ℕ), r < (G.mb i).nZ → oZ i + r ≠ b) : rdZ G oZ cz x b = 0 :=
  Finset.sum_eq_zero fun n _ => if_neg (h n.1 n.2.val n.2.isLt)

end

/-! ## An oracle message as a part of a tree -/

/-- The oracle message o has the shape sh and is part p of the tree at the place t of the book,
which has the shape tsh and the number num. -/
structure Part1 (c : Ctx) (o : ℕ) (sh : OracleShape) (num : ℕ) (tsh : TreeShape) (t p : ℕ) :
    Prop where
  /-- the oracle message and its shape -/
  oracle : ∃ x, c.st.oracles[o]? = some x ∧ x.shape = sh
  /-- its place -/
  place : c.book.place[o]? = some (t, p)
  /-- the tree, its shape and its number -/
  tree : ∃ T, c.book.trees[t]? = some T ∧ T.shape = tsh ∧ T.number = num

/-- The clause lasts as long as the book and the statement keep what is public. -/
theorem Part1.keeps {c c' : Ctx} {o num t p : ℕ} {sh : OracleShape} {tsh : TreeShape}
    (h : Part1 c o sh num tsh t p) (hb : BookKeeps c.book c'.book) (hs : ShapesKeep c.st c'.st) :
    Part1 c' o sh num tsh t p := by
  obtain ⟨x, hx, ex⟩ := h.oracle
  obtain ⟨x', hx', ex'⟩ := hs o x hx
  obtain ⟨T, hT, e1, e2⟩ := h.tree
  obtain ⟨T', hT', f1, f2, _⟩ := hb.tree t T hT
  exact ⟨⟨x', hx', ex'.trans ex⟩, hb.place o _ h.place, T', hT', f1.trans e1, f2.trans e2⟩

/-- The word at which the main symbols of part p begin in a column of a tree of the shape tsh. -/
def skipM (tsh : TreeShape) (p : ℕ) : ℕ := (tsh.mainSymbols.extract 0 p).foldl (· + ·) 0

/-- The word at which the mask symbols of part p begin in a column of a tree of the shape tsh. -/
def skipZ (tsh : TreeShape) (p : ℕ) : ℕ :=
  tsh.mainWidth + (tsh.maskSymbols.extract 0 p).foldl (· + ·) 0

/-! ## What is public of a group on the program's side -/

/-- What is public of a group of sent messages on the program's side. Two parts can lie in one tree
(a member and the first fold's mask, if the mask rode with the member): then tp i = ft, and whoever
names written columns for the trees by their places must take one written round and one message for
both: d i = dF. No clause says so here; the theorems' hypotheses on the columns ask it. -/
structure GpData {s : Sg} (G : Gp s) where
  /-- the number of members -/
  n : ℕ
  /-- a member's place among the layout's members, and its oracle message's number and shape -/
  ix : G.ι → ℕ
  id : G.ι → ℕ
  sh : G.ι → OracleShape
  /-- a member's tree: its number, its shape, its place in the book; the member's place in it -/
  num : G.ι → ℕ
  tsh : G.ι → TreeShape
  tp : G.ι → ℕ
  part : G.ι → ℕ
  /-- the first rows of a member's blocks in the group's two tables -/
  oM : G.ι → ℕ
  oZ : G.ι → ℕ
  /-- where a member's symbols stand in a column, and the written round that sent its tree -/
  lay : G.ι → Lay
  d : G.ι → PQ.RD
  /-- the first fold's fresh mask: shape; tree's number, shape, place; part; the tree's depth; the
  first word of its symbols; the written round that sent its tree -/
  fsh : OracleShape
  fnum : ℕ
  ftsh : TreeShape
  ft : ℕ
  fpart : ℕ
  aF : ℕ
  oF : ℕ
  dF : PQ.RD
  /-- the places in the book of the trees that the first switch opens, increasing; the key and the
  depth of the tree at a place -/
  ts : List ℕ
  key : ℕ → ℕ
  log : ℕ → ℕ

namespace GpData
variable {s : Sg} {G : Gp s} (P : GpData G)

/-- The public facts that tie the data to the group. F: the number of the chain's first tree. -/
structure Pub (F : ℕ) : Prop where
  /-- the group's seats are by numbers, from the blocks' first rows on -/
  numbered : G.Numbered P.oM P.oZ
  /-- the members' places among the layout's members are the numbers below n, each once -/
  ixLt : ∀ i, P.ix i < P.n
  ixInj : ∀ i i', P.ix i = P.ix i' → i = i'
  ixSur : ∀ w, w < P.n → ∃ i, P.ix i = w
  /-- the members' shapes -/
  mainRows : ∀ i, (P.sh i).mainRows = (G.mb i).nM
  maskRows : ∀ i, (P.sh i).maskRows = (G.mb i).nZ
  deg : ∀ i, (P.sh i).mainDeg = if (P.lay i).base then 1 else 3
  /-- the members' trees -/
  depth : ∀ i, (P.tsh i).logN = (G.mb i).a
  skipM : ∀ i, skipM (P.tsh i) (P.part i) = (P.lay i).oM
  skipZ : ∀ i, skipZ (P.tsh i) (P.part i) = (P.lay i).oZ
  posN : ∀ i, PQ.posN (P.d i).tree = 2 ^ (G.mb i).a
  /-- the fresh mask -/
  fMain : P.fsh.mainRows = 0
  fMask : P.fsh.maskRows = 2 ^ s.h
  fDepth : P.ftsh.logN = P.aF
  fSkip : ProxRun.skipZ P.ftsh P.fpart = P.oF
  fPosN : PQ.posN P.dF.tree = 2 ^ P.aF
  /-- the trees that are opened -/
  incr : P.ts.Pairwise (· < ·)
  mem : ∀ t, t ∈ P.ts ↔ (∃ i, P.tp i = t) ∨ t = P.ft
  keyOf : ∀ i, P.key (P.tp i) = P.num i - F
  logOf : ∀ i, P.log (P.tp i) = (G.mb i).a
  fKey : P.key P.ft = P.fnum - F
  fLog : P.log P.ft = P.aF

/-- The layout's clauses: the members, none of them kept, and the first rows of their blocks. -/
structure LayG (L : GroupLayout) : Prop where
  size : L.members.size = P.n
  members : ∀ i, L.members[P.ix i]? = some (P.id i)
  kept : ∀ w, L.kept.getD w false = false
  mainFirst : ∀ i, 0 < (G.mb i).nM → L.mainFirst.getD (P.ix i) none = some (P.oM i)
  maskFirst : ∀ i, 0 < (G.mb i).nZ → L.maskFirst.getD (P.ix i) none = some (P.oZ i)

/-- The members and the fresh mask o are parts of their trees. -/
structure Parts (c : Ctx) (o : ℕ) : Prop where
  mem : ∀ i, Part1 c (P.id i) (P.sh i) (P.num i) (P.tsh i) (P.tp i) (P.part i)
  fresh : Part1 c o P.fsh P.fnum P.ftsh P.ft P.fpart

/-- The clauses last as long as the book and the statement keep what is public. -/
theorem Parts.keeps {P : GpData G} {c c' : Ctx} {o : ℕ} (h : P.Parts c o)
    (hb : BookKeeps c.book c'.book) (hs : ShapesKeep c.st c'.st) : P.Parts c' o :=
  ⟨fun i => (h.mem i).keeps hb hs, h.fresh.keeps hb hs⟩

/-- The tie before the first fold. o: the fresh mask. -/
structure GpTie (c : Ctx) (row : GroupRow) (L : GroupLayout) (o : ℕ) : Prop where
  /-- the row has no form on a kept member -/
  noKept : row.kept = #[]
  /-- the layout -/
  lay : P.LayG L
  /-- the members' and the mask's trees -/
  parts : P.Parts c o

/-- The tie after the first fold, before the switch to the stage s'. -/
structure GpFit (s' : Sg) (K : Codes) (nc nz : ℕ) (pt : Fin (s.h + s.g) → GE) (c : Ctx)
    (old : SingleRows) : Prop where
  /-- what a code switch asks of the three folded rows -/
  ok : FoldedFit s s' K nc nz old
  /-- the row variables of the main table -/
  k : old.layout.k = s.h + s.g
  /-- the row variables of the mask table -/
  h : old.layout.h = s.h
  /-- the point at which the rows were folded -/
  gamma : readP (s.h + s.g) old.gamma = pt
  /-- the layout -/
  lay : P.LayG old.layout
  /-- the members' and the mask's trees -/
  parts : P.Parts c old.fresh

end GpData

end OnBytes.Slice.ProxRun
