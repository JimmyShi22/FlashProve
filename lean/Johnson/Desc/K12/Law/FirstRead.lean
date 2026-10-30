-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstRead.lean: at the first stage of the proximity test (the kind K12), what
the plain reading of the first switch returns is, at each listed position, the symbol of the three
folded words of a group of several members in several trees.

It proves `firstReads : FirstReads`: ReadTie (Johnson/Desc/K12/Law/JointK.lean) for the group under
test. Statements and proofs.
Why the list is pinned to the draws, and why the columns go by order. At one of the four proximity
tests of the smaller stored proof the chain's first tree has the number 23 and the three trees that
the first switch opens have the numbers 1, 21 and 1. `keyed` (Johnson/Desc/K12/Join.lean) and
Tw.L9.openOne take number - firstTree in the natural numbers, so all three keys are 0. A key names
no tree; the order of the dealt columns does. readOld cuts them by the lengths of its own lists
under pos: with a free pos a long tree could be fed a short tree's column, and only the widths would
refuse it. So the list is pinned to the draws, and the premise on the columns goes segment by
segment.
What it says. G : Gp s and P : GpData G are the library's plain group and what is public of it
(OnBytes/Slice/KeyGroup.lean, OnBytes/Slice/BlkProxGp.lean). The dealt columns are the segments of
the trees P.ts, in the book's order, each at its own list under the draws, each column a value of g
t; g at a member's tree is the written oracle o j of the round P.d j, at the mask's tree oF of P.dF.
Then whatever a yes of readOld returns is, at each listed position of the stage's range, the symbol
of foldWords s y z at y = G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j) and z = frOf s P.aF
P.oF P.dF oF.
From which message each word is read. y is read row by row off the members' own messages: member j's
rows off the written oracle o j of the round P.d j that sent its tree (of this chain or of an
earlier one); a main row at the position itself; a mask row at the position modulo the length of its
own tree; zeros on the rows that no member has. The fresh mask z, a word without a sample, is read
off oF of P.dF, from word P.oF on, at the position modulo 2 ^ P.aF. Both are functions of o and oF
alone, letters that stand in front of the test's transcripts. Which messages these are, and that
they are fixed in front of the stage's first draw: Johnson/Desc/K12/Law/FirstSrc.lean over
Johnson/Desc/K12/Law/FixedLaw.lean.
How. The first lemmas are ports, on plain data, of the library's lemmas on runs, which are not
called: Blk.openTreesInto_inv and readOpened_inv (OnBytes/Iop/OpenLaws.lean), readMany_seg
(OnBytes/Slice/BlkProxMany.lean; its proof from its second line on is taken over with the names
turned). The assembly from GpData to the folded words (`gp_main`, `gp_mask`, `gp_symS`, `gpReads`)
is new: OnBytes/Slice/BlkProxGp.lean has the definitions and the pieces alone.
Main names:
  `openOne_seg`, `openAll_seg`, `readOld_seg`: what a yes of openOne, of the loop and of readOld
    says, in readOpened_inv's clauses.
  `readManyP`: the port of readMany_seg.
  `symS_at`: symS_of_tables asked only at the places of the list that hold x.
  `CutAt`: each one's symbols are cut out of the written column of its own tree.
  `gp_main`, `gp_mask`: the program's two tables are the group's (rdM, rdZ): a member's block, or
    zero.
  `gp_symS`: from the cuts to the folded words.
  `Part1P`, `PartsP`: the library's Part1 and GpData.Parts over a statement and a book.
  `gpReads`: the reading at a list pos.
  `FirstReads`, `firstReads`: the statement above.
  `GroupsAre`, `keyed_groups`, `firstReads_keyed`: the same at the columns as `keyed` lays them.
  `ownAt_ofDraws`: the first half of GroupsAre from Block.step's groupsOf, under one bound: every
    draw is below 2 ^ s.C.a.
Limits: No soundness is claimed, and nothing is said on hiding. The law of the proximity test is not
proved here.
Premises of ReadTie that the proof does not spend: row.kept = #[]; gamma.length = s.h + s.g.
A position stays a natural number from the list to colW's argument; x : s.Ps enters by x.val ∈
pos.all, and x.val < 2 ^ s.C.a is spent once (`placeIn_mod`). A word is read by the part as E.mk3 or
ofF and by the library as toE or toF (read_main3, read_main1, read_mask: without a bound).
The statement is about one fixed text (Tw.L9.readOld). A reading that says no to all meets it by its
form; one that said yes to all and returned any symbols would not meet it. That readOld says yes
under all the premises at once was shown on made-up data (three trees, all keys equal, two of one
width, one shorter than the range) in a file that is not in this library.
That P.Pub, P.LayG, PartsP and GroupsAre hold at a real record is not shown here:
Johnson/Desc/K12/Law/FirstOk.lean tests it by evaluation, Johnson/Desc/K12/Law/FirstOkLaw.lean turns
that test's yes into these propositions.
Of `verify-on-bytes` and the library it uses plain records, pure functions and lemmas on them; no
routine in a context is reached from a statement or a proof.
Lemmas called: columnsFit_eq, rebuild (OnBytes/Iop/OpenLaws.lean); listOfT_eq, eq_of_incr
(OnBytes/Chain/Draws.lean); Fmt.listOf_incr, Fmt.listOf_mem (Fmt/Rules6Laws.lean); array_mapM_inv
(OnBytes/Slice/BlkOpenN.lean); symbolsOf_at, flatMap_cut, ownList_eq, idxOf_some
(OnBytes/Slice/BlkProxMany.lean); seg_cut (OnBytes/Slice/BlkProxSeg.lean); indexOf_some
(OnBytes/Slice/BlkCsRead.lean); singleRowsSymbols_inv, tablesAt_inv (OnBytes/Iop/SymbolLaws.lean);
sym_main, sym_mask, sym_fresh (OnBytes/Slice/BlkCsSym.lean); foldWords_std
(OnBytes/Slice/BlkCuts.lean); wordIn_colOf, wordFr_colOf, vec_ofFn, mainAt_eq, maskAt_eq,
putAll_hit, putAll_miss (OnBytes/Slice/BlkProxTables.lean); wordOf_rd, rdM_hit, rdM_miss, rdZ_hit,
rdZ_miss, read_main1, read_main3, read_mask (OnBytes/Slice/BlkProxGp.lean); columnOf_size
(OnBytes/Slice/BlkColumns.lean); readE_zero (OnBytes/Slice/ProgField.lean); and projections of
GpData.Pub, GpData.LayG, Gp.Numbered, BookKeeps and Site.
Tw.L9.openOne tests the columns by the description's own colsStand (Johnson/Desc/Own/Shapes.lean);
openOne_seg goes back to Blk.columnsFit by colsStand_agrees (Johnson/Desc/Own/ShapesAgree.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.SwRead
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- What a yes of Tw.L9.openOne says, with the tree: it is in the book B0 and not longer than the
range (G8, G11); the dealt columns begin with its columns at its own list, under its key (G12);
these are pushed; what comes behind them is left. -/
theorem openOne_seg (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (B1 : TreeBook) (op : List Tw.L9.Col) (acc : Array (Nat × Array Nat × Array (Array F)))
    (out : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : Tw.L9.openOne S firstTree pos B0 t (B1, op, acc) = .ok out) :
    ∃ (tree : OnBytes.Tree) (cs : Array (Array F)), B0.trees[t]? = some tree ∧
      tree.shape.logN ≤ pos.logN ∧ cs.size = (Blk.ownList tree pos).size ∧
      op = viewColumns (tree.number - firstTree) (Blk.ownList tree pos) cs ++ out.2.1 ∧
      out.2.2 = acc.push (t, Blk.ownList tree pos, cs) := by
  unfold Tw.L9.openOne at h
  cases h1 : B1.trees[t]? with
  | none => simp [h1] at h
  | some tree1 =>
    cases h0 : B0.trees[t]? with
    | none => simp [h1, h0] at h
    | some tree =>
      simp only [h1, h0] at h
      split_ifs at h with a b c hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases h
      obtain ⟨hl, ha⟩ := hc
      rw [← Own.colsStand_agrees, columnsFit_eq] at ha
      have hr := rebuild (tree.number - firstTree) (tree.shape.mainWidth + tree.shape.maskWidth)
        (op.take (Blk.ownList tree pos).size) (Blk.ownList tree pos).toList (by simpa using hl) ha
      refine ⟨tree, _, rfl, by simpa using c, by simpa using hl, ?_, rfl⟩
      unfold viewColumns
      simp only
      rw [← hr, List.take_append_drop]

/-- The same of the loop over the trees' places ts. -/
theorem openAll_seg (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (ts : List Nat) (B1 : TreeBook) (op : List Tw.L9.Col)
      (acc : Array (Nat × Array Nat × Array (Array F)))
      (out : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))),
    ts.foldlM (fun s t => Tw.L9.openOne S firstTree pos B0 t s) (B1, op, acc) = .ok out →
    ∃ ext : List (Nat × Array Nat × Array (Array F)), out.2.2.toList = acc.toList ++ ext ∧
      op = (ext.flatMap fun y => viewColumns (Blk.treeKey B0 firstTree y.1) y.2.1 y.2.2) ++
        out.2.1 ∧
      ext.map (·.1) = ts ∧
      ∀ y ∈ ext, ∃ tree, B0.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = Blk.ownList tree pos ∧ y.2.2.size = y.2.1.size
  | [], B1, op, acc, out, h => by
    cases h
    exact ⟨[], by simp, by simp, rfl, by simp⟩
  | t :: ts, B1, op, acc, out, h => by
    rw [List.foldlM_cons] at h
    cases ho : Tw.L9.openOne S firstTree pos B0 t (B1, op, acc) with
    | error e =>
      rw [ho] at h
      cases h
    | ok mid =>
      rw [ho] at h
      obtain ⟨B2, op2, acc2⟩ := mid
      obtain ⟨tree, cs, k1, k2, k3, k4, k5⟩ := openOne_seg _ _ _ _ _ _ _ _ _ ho
      obtain ⟨ext, e1, e2, e3, e4⟩ := openAll_seg S firstTree pos B0 ts B2 op2 acc2 out h
      have k5' : acc2 = acc.push (t, Blk.ownList tree pos, cs) := k5
      have k4' : op = viewColumns (tree.number - firstTree) (Blk.ownList tree pos) cs ++ op2 := k4
      have hkey : Blk.treeKey B0 firstTree t = tree.number - firstTree := by
        unfold Blk.treeKey
        rw [k1]
        rfl
      refine ⟨(t, Blk.ownList tree pos, cs) :: ext, ?_, ?_, ?_, ?_⟩
      · rw [e1, k5']
        simp
      · rw [List.flatMap_cons, hkey, List.append_assoc, ← e2]
        exact k4'
      · rw [List.map_cons, e3]
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨tree, k1, k2, rfl, k3⟩
        · exact e4 y hy

/-- What a yes of Tw.L9.readOld says: the clauses of the library's Blk.readOpened_inv
(OnBytes/Iop/OpenLaws.lean:264), on plain data, and what singleRowsSymbols makes of the symbols. -/
theorem readOld_seg (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) :
    ∃ (places : Array (Nat × Nat)) (cols : List (Nat × Array Nat × Array (Array F)))
      (opened : Array (Array Column)),
      ((singleRowsOracles i.old).mapM fun o => i.book.place[o]?) = some places ∧
      i.opened =
        (cols.flatMap fun y => viewColumns (Blk.treeKey i.book i.firstTree y.1) y.2.1 y.2.2) ++
          left ∧
      cols.map (·.1) = Fmt.listOf (places.map (·.1)).toList ∧
      (∀ y ∈ cols, ∃ tree, i.book.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = Blk.ownList tree pos ∧ y.2.2.size = y.2.1.size) ∧
      (((singleRowsOracles i.old).zip places).mapM fun y =>
        Blk.symbolsOf i.st i.book pos cols y.1 y.2) = some opened ∧
      singleRowsSymbols i.old opened pos.all.size = some ys := by
  obtain ⟨places, cols, opened, h1, h3, h5, h6⟩ := readOld_inv i pos B left ys h
  obtain ⟨ext, e1, e2, e3, e4⟩ := openAll_seg _ _ _ _ _ _ _ _ _ h3
  have e1' : cols.toList = ext := by simpa using e1
  subst e1'
  exact ⟨places, cols.toList, opened, h1, e2, by rw [e3, listOfT_eq], e4, h5, h6⟩

/-- The port of readMany_seg (BlkProxMany.lean:122). ts: the places in the book of the trees of the
messages asked for (by hts: each once, increasing). If the dealt columns begin with the segments of
these trees in turn, each at its own list under pos, then R, which comes after them, is left; and
the symbols of message number w, which is o, part p of the tree at the place t, are cut at each
listed position from a value of g t. no key tells two trees apart here: the order does. -/
theorem readManyP (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys))
    (key log : Nat → Nat) (g : Nat → Nat → Option (List UInt64)) (R : Cols) (ts : List Nat)
    (hts : ∀ places, ((singleRowsOracles i.old).mapM fun o => i.book.place[o]?) = some places →
      Fmt.listOf (places.map (·.1)).toList = ts)
    (hbk : ∀ t ∈ ts, ∀ T, i.book.trees[t]? = some T →
      T.number - i.firstTree = key t ∧ T.shape.logN = log t)
    (hop : i.opened = expCols pos key log g ts ++ R)
    (hin : ∀ t ∈ ts, ∀ x ∈ (ownAt (log t) pos).toList, (g t x).isSome = true) :
    ∃ opened : Array (Array Column), singleRowsSymbols i.old opened pos.all.size = some ys ∧
    left = R ∧
    ∀ (w o t p : Nat) (T : OnBytes.Tree) (x : OnBytes.Oracle), (singleRowsOracles i.old)[w]? = some
        o →
      i.book.place[o]? = some (t, p) → i.book.trees[t]? = some T → i.st.oracles[o]? = some x →
      ∀ k, k < pos.all.size →
        ∃ cw : Array OnBytes.F,
          g t (placeIn T.shape.logN pos.logN (pos.all.getD k 0)) = some cw.toList ∧
          colB opened w k = Blk.columnOf x (OnBytes.Slice.mainSkip T p) (OnBytes.Slice.maskSkip T p)
              cw := by
  obtain ⟨places, cols, opened, h1, h2, h3, h4, h5, h6⟩ := readOld_seg i pos B left ys h
  generalize singleRowsOracles i.old = ids at *
  have ets := hts places h1
  have hmts : ∀ y ∈ cols, y.1 ∈ ts := fun y hy => by
    rw [← ets, ← h3]
    exact List.mem_map_of_mem hy
  -- Segment by segment
  have hexp : expCols pos key log g ts = cols.flatMap fun y =>
      segOf (key y.1) (ownAt (log y.1) pos).toList (g y.1) := by
    unfold expCols
    rw [← ets, ← h3, List.flatMap_map]
  rw [hexp] at hop
  obtain ⟨hseg, hR⟩ := flatMap_cut _ _ cols _ _ (fun y hy => by
    obtain ⟨T, k1, _, k3, k4⟩ := h4 y hy
    obtain ⟨_, b2⟩ := hbk y.1 (hmts y hy) T k1
    unfold viewColumns segOf
    rw [List.length_map, List.length_map, List.length_zip, Array.length_toList,
      Array.length_toList, Array.length_toList, k4, Nat.min_self, k3, ownList_eq, b2])
    (h2.symm.trans hop)
  refine ⟨opened, h6, hR, ?_⟩
  intro w o t p T x hw hpl hT hx k hk
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ h1
  obtain ⟨hwlt, hwo⟩ := Array.getElem?_eq_some_iff.1 hw
  have hwp : w < places.size := by rw [z1]; exact hwlt
  have hplace : places[w] = (t, p) := by
    have e := z2 w hwlt
    rw [hwo, hpl, Array.getElem?_eq_getElem hwp] at e
    exact (Option.some.inj e).symm
  -- The tree is among those opened
  have hmem : t ∈ cols.map (·.1) := by
    rw [h3, Fmt.listOf_mem]
    simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff]
    exact ⟨places[w], Array.getElem_mem hwp, by rw [hplace]⟩
  obtain ⟨m0, hm0, em0⟩ := List.mem_map.1 hmem
  obtain ⟨mine, hfind⟩ : ∃ mine, cols.find? (·.1 == t) = some mine := by
    cases hc : cols.find? (·.1 == t) with
    | some mine => exact ⟨mine, rfl⟩
    | none =>
      have := List.find?_eq_none.1 hc m0 hm0
      rw [em0] at this
      simp at this
  have hmine : mine ∈ cols := List.mem_of_find?_eq_some hfind
  have emine : mine.1 = t := by
    have := List.find?_some hfind
    simpa using this
  obtain ⟨T', k1, _, k3, k4⟩ := h4 mine hmine
  rw [emine, hT] at k1
  obtain rfl : T = T' := Option.some.inj k1
  -- The tree's columns are values of g t
  have hkey : Blk.treeKey i.book i.firstTree mine.1 = T.number - i.firstTree := by
    unfold Blk.treeKey
    rw [emine, hT]
    rfl
  have htm : t ∈ ts := emine ▸ hmts mine hmine
  obtain ⟨b1, b2⟩ := hbk t htm T hT
  have hs := hseg mine hmine
  rw [hkey, emine, ← b1, ← b2, ← ownList_eq, ← k3] at hs
  obtain ⟨_, hval⟩ := seg_cut (T.number - i.firstTree) mine.2.1 mine.2.2 (g t) _ [] [] k4
    (List.append_nil _).symm (by rw [List.append_nil]; exact hs)
    (by rw [k3, ownList_eq, b2]; exact hin t htm)
  -- The message's symbols
  obtain ⟨w1, w2⟩ := array_mapM_inv _ _ _ h5
  have hzs : (ids.zip places).size = ids.size := by rw [Array.size_zip, z1, Nat.min_self]
  have q1 := w2 w (by rw [hzs]; exact hwlt)
  have hop' : w < opened.size := by rw [w1, hzs]; exact hwlt
  rw [Array.getElem_zip, Array.getElem?_eq_getElem hop', hwo, hplace] at q1
  obtain ⟨here, c, e1, e2, e3⟩ :=
    symbolsOf_at i.st i.book pos cols o t p T x opened[w] mine hT hx hfind q1 k hk
  have eo : opened.getD w #[] = opened[w] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hop']
    rfl
  refine ⟨c, ?_, by unfold colB; rw [eo]; exact e3⟩
  obtain ⟨hlt2, _⟩ := Array.getElem?_eq_some_iff.1 e2
  have hlt1 : here < mine.2.1.size := by rw [← k4]; exact hlt2
  have hv := hval here hlt1
  have ecd : mine.2.2.getD here #[] = c := by
    rw [Array.getD_eq_getD_getElem?, e2]
    rfl
  rw [ecd] at hv
  -- The column's position
  have hposn : mine.2.1.getD here 0 = placeIn T.shape.logN pos.logN (pos.all.getD k 0) := by
    unfold placeIn
    by_cases hl : T.shape.logN = pos.logN
    · rw [if_pos hl]
      rw [if_pos (by rw [hl]; exact beq_self_eq_true _)] at e1
      obtain rfl : k = here := Option.some.inj e1
      rw [k3]
      unfold Blk.ownList
      rw [if_pos (by rw [hl]; exact beq_self_eq_true _)]
    · rw [if_neg hl]
      rw [if_neg (by simpa using hl)] at e1
      exact (idxOf_some _ _ _ e1).2
  rw [← hposn]
  exact hv

/-! ## The tables, at the one listed position that is asked for -/

/-- symS_of_tables (BlkProxTables.lean:151), asked only at the places of the list that hold x. (A
listed position outside the stage's range is no x : s.Ps, and nothing is said of it.) -/
theorem symS_at (s : Sg) (old : SingleRows) (pos : Positions) (opened : Array (Array Column))
    (y : Array E) (rm rz rf : ℕ → ℕ → GE)
    (hsym : singleRowsSymbols old opened pos.all.size = some y) (hm : old.masks = 2)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = false)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h) (x : s.Ps) (hx : x.val ∈ pos.all)
    (hmain : ∀ i, i < pos.all.size → pos.all.getD i 0 = x.val → ∀ b, b < 2 ^ (s.h + s.g) →
      OnBytes.Slice.readE (mainAt old.layout opened i b) = rm x.val b)
    (hmask : ∀ i, i < pos.all.size → pos.all.getD i 0 = x.val → ∀ b, b < 2 ^ s.h →
      OnBytes.Slice.readE (maskAt old.layout opened i b) = rz x.val b)
    (hfresh : ∀ i, i < pos.all.size → pos.all.getD i 0 = x.val → ∀ b, b < 2 ^ s.h →
      readV (colB opened old.layout.members.size i).mask b = rf x.val b)
    (α : s.cMid.Aa) :
    s.cMid.T (foldWords s (OnBytes.Slice.ProxRun.wordOf s rm rz) (freshOf s rf) (readP _ old.gamma))
        x α =
      symS s old pos y x.val α := by
  rw [← wordIn_colOf s rm rz rf, ← wordFr_colOf s rm rz rf, foldWords_std]
  obtain ⟨i, hi, hlt, hxi⟩ := indexOf_some pos x.val hx
  obtain ⟨hg, _, _, hall⟩ := singleRowsSymbols_inv old opened _ y (by omega) hsym
  obtain ⟨t, ht, _, y0, _, y1, y2⟩ := hall i hlt
  obtain ⟨z1, z2, _, e1, e2⟩ := tablesAt_inv old.layout opened i t ht hkept
  obtain ⟨zf, y2⟩ := y2 hm
  have hg' : old.gamma.length = s.h + s.g := hg.trans hk
  rw [hh] at y1 y2 zf z2
  rw [hk] at z1
  rcases α with _ | _ | _
  · rw [sym_main s (colOf s rm rz rf) old.gamma hg' x t.1 z1 fun b hb => by
      unfold readV
      rw [e1 b]
      exact (hmain i hlt hxi b hb).trans (OnBytes.Slice.ProxRun.vec_ofFn _ (rm _) b hb).symm]
    unfold symS readV
    rw [hi, Option.getD_some, y0]
  · rw [sym_mask s (colOf s rm rz rf) old.gamma hg' x t.2.1 z2 fun b hb => by
      unfold readV
      rw [e2 b]
      exact (hmask i hlt hxi b hb).trans (OnBytes.Slice.ProxRun.vec_ofFn _ (rz _) b hb).symm]
    unfold symS readV
    rw [hi, Option.getD_some, y1 (by omega)]
  · rw [sym_fresh s (colOf s rm rz rf) old.gamma hg' x _ zf fun b hb =>
      (hfresh i hlt hxi b hb).trans (OnBytes.Slice.ProxRun.vec_ofFn _ (rf _) b hb).symm]
    unfold symS readV
    rw [hi, Option.getD_some, y2]

/-- The position of a tree of depth a ≤ … that belongs to a position of the stage's range is the
position modulo the tree's length. -/
theorem placeIn_mod (a logN x : ℕ) (hx : x < 2 ^ logN) : placeIn a logN x = x % 2 ^ a := by
  unfold placeIn
  by_cases h : a = logN
  · rw [if_pos h, h, Nat.mod_eq_of_lt hx]
  · rw [if_neg h]

section
variable {s : Sg} {G : Gp s} (P : GpData G)

/-- What was read of the group's members and of the fresh mask at the place k of the list: each
one's symbols are cut, where its part begins, out of the written column of its own tree at the
position that belongs to the listed one. o j: the written oracle of the round P.d j, which sent
member j's tree. oF: that of P.dF, which sent the fresh mask's. -/
structure CutAt (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (pos : Positions)
    (opened : Array (Array Column)) (k : ℕ) : Prop where
  mem : ∀ j, ∃ (xo : OnBytes.Oracle) (cw : Array OnBytes.F), xo.shape = P.sh j ∧
    cw.toList = colW (P.d j) (o j) (placeIn (P.tsh j).logN pos.logN (pos.all.getD k 0)) ∧
    colB opened (P.ix j) k =
      Blk.columnOf xo (skipM (P.tsh j) (P.part j)) (skipZ (P.tsh j) (P.part j)) cw
  fresh : ∃ (xo : OnBytes.Oracle) (cw : Array OnBytes.F), xo.shape = P.fsh ∧
    cw.toList = colW P.dF oF (placeIn P.ftsh.logN pos.logN (pos.all.getD k 0)) ∧
    colB opened P.n k = Blk.columnOf xo (skipM P.ftsh P.fpart) (skipZ P.ftsh P.fpart) cw

variable {P}

/-- The program's main table at a listed position x of the stage's range is the group's. -/
theorem gp_main {F : ℕ} (hP : P.Pub F) {L : GroupLayout} (hL : P.LayG L)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (pos : Positions)
    (hlog : pos.logN = s.C.a) (opened : Array (Array Column)) (k : ℕ)
    (hc : CutAt P o oF pos opened k) (x : s.Ps) (hx : pos.all.getD k 0 = x.val) (b : ℕ) :
    OnBytes.Slice.readE (mainAt L opened k b) =
      rdM G P.oM (fun j => (P.lay j).cm (P.d j) (o j)) x.val b := by
  have hsz : ∀ j, (colB opened (P.ix j) k).main.size = (G.mb j).nM := fun j => by
    obtain ⟨xo, cw, e1, _, e3⟩ := hc.mem j
    rw [e3, (columnOf_size _ _ _ _).1, e1, hP.mainRows]
  rw [mainAt_eq, hL.size]
  by_cases hb : ∃ j r, r < (G.mb j).nM ∧ P.oM j + r = b
  · obtain ⟨j, r, hr, rfl⟩ := hb
    rw [rdM_hit hP.numbered _ _ j r hr,
      putAll_hit _ _ (P.ix j) (P.oM j) r (hL.mainFirst j (by omega)) (by rw [hsz]; exact hr) P.n
        (hP.ixLt j) fun w' hw' hne f' hf' => by
          obtain ⟨j', rfl⟩ := hP.ixSur w' hw'
          have hjj : j' ≠ j := fun e => hne (by rw [e])
          rw [hsz]
          by_cases h0 : 0 < (G.mb j').nM
          · have := (hL.mainFirst j' h0).symm.trans hf'
            obtain rfl : P.oM j' = f' := Option.some.inj this
            rcases hP.numbered.apartM j' j hjj with h | h <;> omega
          · omega]
    obtain ⟨xo, cw, e1, e2, e3⟩ := hc.mem j
    have hpl : placeIn (P.tsh j).logN pos.logN (pos.all.getD k 0) = x.val := by
      unfold placeIn
      rw [if_pos (by rw [hP.depth, (G.seat j).hM ⟨r, hr⟩, hlog]), hx]
    rw [hpl] at e2
    have hr' : r < xo.shape.mainRows := by rw [e1, hP.mainRows]; exact hr
    show readV (colB opened (P.ix j) k).main r = _
    rw [e3, hP.skipM]
    unfold Lay.cm
    by_cases hbase : (P.lay j).base = true
    · rw [if_pos hbase]
      exact read_main1 xo _ _ cw _ _ _ e2 r hr' (by rw [e1, hP.deg, if_pos hbase])
    · rw [if_neg hbase]
      exact read_main3 xo _ _ cw _ _ _ e2 r hr' (by rw [e1, hP.deg, if_neg hbase])
  · rw [rdM_miss _ _ _ _ fun j r hr e => hb ⟨j, r, hr, e⟩,
      putAll_miss _ _ _ _ fun w hw f hf => by
        obtain ⟨j, rfl⟩ := hP.ixSur w hw
        rw [hsz]
        by_cases h0 : 0 < (G.mb j).nM
        · have := (hL.mainFirst j h0).symm.trans hf
          obtain rfl : P.oM j = f := Option.some.inj this
          by_contra hcon
          exact hb ⟨j, b - P.oM j, by omega, by omega⟩
        · omega]
    exact readE_zero

/-- The program's mask table at a listed position x of the stage's range is the group's: a member's
mask rows are read at x modulo the length of the member's tree. -/
theorem gp_mask {F : ℕ} (hP : P.Pub F) {L : GroupLayout} (hL : P.LayG L)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (pos : Positions)
    (hlog : pos.logN = s.C.a) (opened : Array (Array Column)) (k : ℕ)
    (hc : CutAt P o oF pos opened k) (x : s.Ps) (hx : pos.all.getD k 0 = x.val) (b : ℕ) :
    OnBytes.Slice.readE (maskAt L opened k b) =
      rdZ G P.oZ (fun j => (P.lay j).cz (P.d j) (o j)) x.val b := by
  have hsz : ∀ j, (colB opened (P.ix j) k).mask.size = (G.mb j).nZ := fun j => by
    obtain ⟨xo, cw, e1, _, e3⟩ := hc.mem j
    rw [e3, (columnOf_size _ _ _ _).2, e1, hP.maskRows]
  rw [maskAt_eq, hL.size]
  by_cases hb : ∃ j r, r < (G.mb j).nZ ∧ P.oZ j + r = b
  · obtain ⟨j, r, hr, rfl⟩ := hb
    rw [rdZ_hit hP.numbered _ _ j r hr,
      putAll_hit _ _ (P.ix j) (P.oZ j) r (hL.maskFirst j (by omega)) (by rw [hsz]; exact hr) P.n
        (hP.ixLt j) fun w' hw' hne f' hf' => by
          obtain ⟨j', rfl⟩ := hP.ixSur w' hw'
          have hjj : j' ≠ j := fun e => hne (by rw [e])
          rw [hsz]
          by_cases h0 : 0 < (G.mb j').nZ
          · have := (hL.maskFirst j' h0).symm.trans hf'
            obtain rfl : P.oZ j' = f' := Option.some.inj this
            rcases hP.numbered.apartZ j' j hjj with h | h <;> omega
          · omega]
    obtain ⟨xo, cw, e1, e2, e3⟩ := hc.mem j
    rw [hx, placeIn_mod _ _ _ (by rw [hlog]; exact x.isLt), hP.depth] at e2
    have hr' : r < xo.shape.maskRows := by rw [e1, hP.maskRows]; exact hr
    show readV (colB opened (P.ix j) k).mask r = _
    rw [e3, hP.skipZ]
    exact read_mask xo _ _ cw _ _ _ e2 r hr'
  · rw [rdZ_miss _ _ _ _ fun j r hr e => hb ⟨j, r, hr, e⟩,
      putAll_miss _ _ _ _ fun w hw f hf => by
        obtain ⟨j, rfl⟩ := hP.ixSur w hw
        rw [hsz]
        by_cases h0 : 0 < (G.mb j).nZ
        · have := (hL.maskFirst j h0).symm.trans hf
          obtain rfl : P.oZ j = f := Option.some.inj this
          by_contra hcon
          exact hb ⟨j, b - P.oZ j, by omega, by omega⟩
        · omega]
    exact readE_zero

/-- From the cuts to the folded words. If at each place of the list that holds x the members' and
the mask's symbols are cut out of their own trees' written columns, the symbols read are those of
the three folded words of the group's word (each member's written word at its seat; a mask row of a
shorter tree read periodically; zeros elsewhere) and of the fresh mask's written word. -/
theorem gp_symS {F : ℕ} (hP : P.Pub F) (old : SingleRows) (hL : P.LayG old.layout)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (pos : Positions)
    (hlog : pos.logN = s.C.a) (opened : Array (Array Column)) (y : Array E)
    (hsym : singleRowsSymbols old opened pos.all.size = some y) (hm : old.masks = 2)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (hc : ∀ k, k < pos.all.size → CutAt P o oF pos opened k)
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (foldWords s (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
      (frOf s P.aF P.oF P.dF oF) (readP _ old.gamma)) x α = symS s old pos y x.val α := by
  have hw : (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j)) =
      OnBytes.Slice.ProxRun.wordOf s (rdM G P.oM fun j => (P.lay j).cm (P.d j) (o j))
        (rdZ G P.oZ fun j => (P.lay j).cz (P.d j) (o j)) :=
    (wordOf_rd hP.numbered _ _).symm
  have hf : frOf s P.aF P.oF P.dF oF =
      freshOf s fun x b => symW P.dF oF (x % 2 ^ P.aF) (P.oF + 3 * b) := rfl
  rw [hw, hf]
  refine symS_at s old pos opened y _ _ _ hsym hm (fun w _ => hL.kept w) hk hh x hx
    (fun k hk' hxk b _ => gp_main hP hL o oF pos hlog opened k (hc k hk') x hxk b)
    (fun k hk' hxk b _ => gp_mask hP hL o oF pos hlog opened k (hc k hk') x hxk b)
    (fun k hk' hxk b hb => ?_) α
  obtain ⟨xo, cw, e1, e2, e3⟩ := (hc k hk').fresh
  rw [hxk, placeIn_mod _ _ _ (by rw [hlog]; exact x.isLt), hP.fDepth] at e2
  rw [hL.size, e3, hP.fSkip]
  exact read_mask xo _ _ cw _ _ _ e2 b (by rw [e1, hP.fMask]; exact hb)

end

/-! ## The members' and the mask's places, on plain data -/

/-- The library's Part1 (BlkProxGp.lean:206) over a statement and a book: the oracle message o has
the shape sh and is part p of the tree at the place t of the book, which has the shape tsh and the
number num. -/
structure Part1P (st : Statement) (book : TreeBook) (o : ℕ) (sh : OracleShape) (num : ℕ)
    (tsh : TreeShape) (t p : ℕ) : Prop where
  oracle : ∃ x, st.oracles[o]? = some x ∧ x.shape = sh
  place : book.place[o]? = some (t, p)
  tree : ∃ T, book.trees[t]? = some T ∧ T.shape = tsh ∧ T.number = num

theorem Part1P.keeps {st st' : Statement} {book book' : TreeBook} {o num t p : ℕ}
    {sh : OracleShape} {tsh : TreeShape} (h : Part1P st book o sh num tsh t p)
    (hb : BookKeeps book book') (hs : ShapesKeep st st') : Part1P st' book' o sh num tsh t p := by
  obtain ⟨x, hx, ex⟩ := h.oracle
  obtain ⟨x', hx', ex'⟩ := hs o x hx
  obtain ⟨T, hT, e1, e2⟩ := h.tree
  obtain ⟨T', hT', f1, f2, _⟩ := hb.tree t T hT
  exact ⟨⟨x', hx', ex'.trans ex⟩, hb.place o _ h.place, T', hT', f1.trans e1, f2.trans e2⟩

/-- The library's GpData.Parts over a statement and a book: the members and the fresh mask o are
parts of their trees. -/
structure PartsP {s : Sg} {G : Gp s} (P : GpData G) (st : Statement) (book : TreeBook) (o : ℕ) :
    Prop where
  mem : ∀ j, Part1P st book (P.id j) (P.sh j) (P.num j) (P.tsh j) (P.tp j) (P.part j)
  fresh : Part1P st book o P.fsh P.fnum P.ftsh P.ft P.fpart

/-- The reading in front of the first switch, at a list pos. The dealt columns begin with the
segments of the group's trees in the book's order (P.ts), each at its own list under pos, each
column the written column of that tree (g). Then what a yes of readOld returns is, at each listed
position of the stage's range, the symbol of the three folded words of the group's word and the
fresh mask's word.
from which message each word is read: member j's word off the written oracle o j of the round P.d j
(which sent its tree; of this chain or an earlier one); the fresh mask's off oF of P.dF. Where two
of them share a tree (P.tp j = P.ft), the two premises on g force one written column for both. -/
theorem gpReads (firstTree : ℕ) (s : Sg) (G : Gp s) (P : GpData G) (cu : IoppStage)
    (L : GroupLayout) (st : Statement) (book : TreeBook) (id : ℕ)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc)
    (g : ℕ → ℕ → Option (List UInt64)) (R : Cols)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (hP : P.Pub firstTree) (hL : P.LayG L)
    (hparts : PartsP P st book id)
    (hgM : ∀ j x, g (P.tp j) x = some (colW (P.d j) (o j) x))
    (hgF : ∀ x, g P.ft x = some (colW P.dF oF x))
    (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col) (ys : Array E)
    (S : Statement) (row : GroupRow) (eps claim : E) (gamma : List E)
    (hB : BookKeeps book i.book) (hS : ShapesKeep st i.st) (hf : i.firstTree = firstTree)
    (ho : i.opened = expCols pos P.key P.log g P.ts ++ R)
    (hold : i.old = foldOutput S (ioppFoldShape cu L) row id eps gamma claim)
    (hlog : pos.logN = s.C.a) (hread : Tw.L9.readOld i pos = .ok (B, left, ys))
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (foldWords s (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
      (frOf s P.aF P.oF P.dF oF) (readP (s.h + s.g) gamma)) x α = symS s i.old pos ys x.val α := by
  have hM := fun j => (hparts.mem j).keeps hB hS
  have hF := hparts.fresh.keeps hB hS
  have hlay : i.old.layout = { L with k := cu.k, h := cu.h } := by rw [hold]; rfl
  have hm : i.old.masks = 2 := by rw [hold]; rfl
  have hgam : i.old.gamma = gamma := by rw [hold]; rfl
  have hL' : P.LayG i.old.layout := by
    rw [hlay]
    exact ⟨hL.size, hL.members, hL.kept, hL.mainFirst, hL.maskFirst⟩
  have hids : singleRowsOracles i.old = L.members.push id := by
    rw [hold]
    rfl
  have idM : ∀ j, (singleRowsOracles i.old)[P.ix j]? = some (P.id j) := fun j => by
    rw [hids, Array.getElem?_push, if_neg (by have := hP.ixLt j; rw [hL.size]; omega)]
    exact hL.members j
  have idF : (singleRowsOracles i.old)[P.n]? = some id := by
    rw [hids, ← hL.size, Array.getElem?_push_size]
  have hsize : (singleRowsOracles i.old).size = P.n + 1 := by
    rw [hids, Array.size_push, hL.size]
  obtain ⟨opened, hsym, _, hcut⟩ := readManyP i pos B left ys hread P.key P.log g R P.ts
    (fun places hpl => by
      obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ hpl
      refine eq_of_incr _ _ (Fmt.listOf_incr _) hP.incr fun z => ?_
      rw [Fmt.listOf_mem, hP.mem]
      simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Array.mem_iff_getElem.1 hq
        have hw' : w < (singleRowsOracles i.old).size := by rw [← z1]; exact hw
        have e := z2 w hw'
        rw [Array.getElem?_eq_getElem hw] at e
        by_cases hn : w < P.n
        · obtain ⟨j, rfl⟩ := hP.ixSur w hn
          have e1 := idM j
          rw [Array.getElem?_eq_getElem hw'] at e1
          rw [Option.some.inj e1, (hM j).place] at e
          rw [← Option.some.inj e]
          exact Or.inl ⟨j, rfl⟩
        · obtain rfl : w = P.n := by omega
          have e1 := idF
          rw [Array.getElem?_eq_getElem hw'] at e1
          rw [Option.some.inj e1, hF.place] at e
          rw [← Option.some.inj e]
          exact Or.inr rfl
      · rintro (⟨j, rfl⟩ | rfl)
        · have hw' : P.ix j < (singleRowsOracles i.old).size := by
            have := hP.ixLt j
            omega
          have hw : P.ix j < places.size := by rw [z1]; exact hw'
          have e := z2 _ hw'
          have e1 := idM j
          rw [Array.getElem?_eq_getElem hw'] at e1
          rw [Option.some.inj e1, (hM j).place, Array.getElem?_eq_getElem hw] at e
          exact ⟨_, Array.getElem_mem hw, by rw [← Option.some.inj e]⟩
        · have hw' : P.n < (singleRowsOracles i.old).size := by omega
          have hw : P.n < places.size := by rw [z1]; exact hw'
          have e := z2 _ hw'
          have e1 := idF
          rw [Array.getElem?_eq_getElem hw'] at e1
          rw [Option.some.inj e1, hF.place, Array.getElem?_eq_getElem hw] at e
          exact ⟨_, Array.getElem_mem hw, by rw [← Option.some.inj e]⟩)
    (fun t ht T hT => by
      rw [hf]
      rcases (hP.mem t).1 ht with ⟨j, rfl⟩ | rfl
      · obtain ⟨T', k1, k2, k3⟩ := (hM j).tree
        obtain rfl : T' = T := Option.some.inj (k1.symm.trans hT)
        exact ⟨by rw [k3, hP.keyOf], by rw [k2, hP.depth, hP.logOf]⟩
      · obtain ⟨T', k1, k2, k3⟩ := hF.tree
        obtain rfl : T' = T := Option.some.inj (k1.symm.trans hT)
        exact ⟨by rw [k3, hP.fKey], by rw [k2, hP.fDepth, hP.fLog]⟩)
    ho
    (fun t ht x _ => by
      rcases (hP.mem t).1 ht with ⟨j, rfl⟩ | rfl
      · rw [hgM]
        rfl
      · rw [hgF]
        rfl)
  rw [← hgam]
  refine gp_symS hP i.old hL' o oF pos hlog opened ys hsym hm (by rw [hlay]; exact hk)
    (by rw [hlay]; exact hh) (fun k hk' => ⟨fun j => ?_, ?_⟩) x hx α
  · obtain ⟨xo, q1, q2⟩ := (hM j).oracle
    obtain ⟨T, k1, k2, _⟩ := (hM j).tree
    obtain ⟨cw, c1, c2⟩ := hcut _ _ _ _ T xo (idM j) (hM j).place k1 q1 k hk'
    rw [hgM, k2] at c1
    refine ⟨xo, cw, q2, (Option.some.inj c1).symm, ?_⟩
    rw [c2, ← k2]
    rfl
  · obtain ⟨xo, q1, q2⟩ := hF.oracle
    obtain ⟨T, k1, k2, _⟩ := hF.tree
    obtain ⟨cw, c1, c2⟩ := hcut _ _ _ _ T xo idF hF.place k1 q1 k hk'
    rw [hgF, k2] at c1
    refine ⟨xo, cw, q2, (Option.some.inj c1).symm, ?_⟩
    rw [c2, ← k2]
    rfl

/-! ## (F) FirstReads -/

/-- (F) the tie in front of the first switch, for a group of several members in several trees. G, P:
the library's plain group and what is public of it on the program's side (KeyGroup.lean ·
BlkProxGp.lean). id: the first fold's fresh mask. o j, oF: the written oracles of the rounds P.d j,
P.dF that sent member j's tree and the mask's. g t: the written columns of the tree at the place t
of the book. the dealt columns go by order: the segments of the trees P.ts (the book's order), each
at its own list under the draws poss; R: what comes behind them. no key and no width tells two trees
apart. -/
def FirstReads : Prop :=
  ∀ (firstTree : ℕ) (s : Sg) (G : Gp s) (P : GpData G) (cu : IoppStage) (L : GroupLayout)
    (st : Statement) (book : TreeBook) (id : ℕ) (o : ∀ j, (wRound (P.d j)).Orc)
    (oF : (wRound P.dF).Orc) (g : ℕ → ℕ → Option (List UInt64)) (R : Cols) (poss : List ℕ),
    cu.k = s.h + s.g → cu.h = s.h → P.Pub firstTree → P.LayG L → PartsP P st book id →
    (∀ j x, g (P.tp j) x = some (colW (P.d j) (o j) x)) →
    (∀ x, g P.ft x = some (colW P.dF oF x)) →
    ReadTie firstTree s (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
      (frOf s P.aF P.oF P.dF oF) (ioppFoldShape cu L) st book id
      (expCols (Positions.ofDraws s.C.a poss) P.key P.log g P.ts ++ R) poss

/-- The reading at the first stage, as the head states it. -/
theorem firstReads : FirstReads := by
  intro firstTree s G P cu L st book id o oF g R poss hk hh hP hL hparts hgM hgF i pos B left ys S
    row eps claim gamma hB hS hf ho hold _ _ hpos hread x hx α
  subst hpos
  exact gpReads firstTree s G P cu L st book id o oF g R hk hh hP hL hparts hgM hgF i _ B left ys S
    row eps claim gamma hB hS hf ho hold rfl hread x hx α

/-- The groups that a part is dealt are the trees' ts, in turn: group by group the positions are the
tree's own list under pos, and each column is a value of g t. -/
def GroupsAre (pos : Positions) (log : ℕ → ℕ) (g : ℕ → ℕ → Option (List UInt64)) (ts : List ℕ)
    (gs : Gs) : Prop :=
  List.Forall₂ (fun t grp => grp.map (·.1) = (ownAt (log t) pos).toList ∧
    ∀ c ∈ grp, g t c.1 = some c.2) ts gs

/-- Such groups, with the keys laid on as Join.lean's keyed lays them, are the segments in turn. -/
theorem keyed_groups (pos : Positions) (key log : ℕ → ℕ) (g : ℕ → ℕ → Option (List UInt64)) :
    ∀ (ts : List ℕ) (gs : Gs), GroupsAre pos log g ts gs →
    (((ts.map key).zip gs).flatMap fun x => x.2.map fun c => (x.1, c.1, c.2)) =
      expCols pos key log g ts
  | [], [], _ => rfl
  | t :: ts, grp :: gs, h => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := List.forall₂_cons.1 h
    have ih := keyed_groups pos key log g ts gs h3
    unfold expCols at ih ⊢
    rw [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons, ih]
    congr 1
    unfold segOf
    rw [← h1, List.map_map]
    refine List.map_congr_left fun c hc => ?_
    show (key t, c.1, c.2) = (key t, c.1, (g t c.1).getD [])
    rw [h2 c hc]
    rfl

/-- (F) at the columns as Join.lean's keyed lays them: the declared trees' keys are the book's
trees', in turn, and the groups are theirs. -/
theorem firstReads_keyed (p : P12) (cut : List Fmt.DeclaredRound) (gs : Gs) (s : Sg) (G : Gp s)
    (P : GpData G) (cu : IoppStage) (L : GroupLayout) (st : Statement) (book : TreeBook) (id : ℕ)
    (o : ∀ j, (wRound (P.d j)).Orc) (oF : (wRound P.dF).Orc) (g : ℕ → ℕ → Option (List UInt64))
    (poss : List ℕ) (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (hP : P.Pub p.nums.firstTree)
    (hL : P.LayG L) (hparts : PartsP P st book id)
    (hgM : ∀ j x, g (P.tp j) x = some (colW (P.d j) (o j) x))
    (hgF : ∀ x, g P.ft x = some (colW P.dF oF x))
    (hkeys : (cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree) =
      P.ts.map P.key)
    (hgs : GroupsAre (Positions.ofDraws s.C.a poss) P.log g P.ts gs) :
    ReadTie p.nums.firstTree s (G.word fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (o j))
      (frOf s P.aF P.oF P.dF oF) (ioppFoldShape cu L) st book id (keyed p cut gs) poss := by
  have h := firstReads p.nums.firstTree s G P cu L st book id o oF g [] poss hk hh hP hL hparts hgM
    hgF
  rw [List.append_nil, ← keyed_groups _ _ _ _ _ _ hgs, ← hkeys] at h
  exact h

/-- GroupsAre's first half, from what Block.step's test "the columns" gives (Block.lean's groupsOf:
group t stands at Fmt.listOf (poss.map (· % 2 ^ a_t))): that list is the tree's own list under the
draws, where every draw lies in the range. (At a tree as long as the range the program's list is the
draws' own, unreduced: the bound is spent there, and nowhere else.) -/
theorem ownAt_ofDraws (a logT : ℕ) (poss : List ℕ) (h : ∀ x ∈ poss, x < 2 ^ a) :
    (ownAt logT (Positions.ofDraws a poss)).toList = Fmt.listOf (poss.map (· % 2 ^ logT)) := by
  unfold ownAt Positions.ofDraws
  by_cases e : logT = a
  · subst e
    rw [if_pos (beq_self_eq_true _), listOfT_eq]
    have hm : poss.map (· % 2 ^ logT) = poss :=
      (List.map_congr_left fun x hx => Nat.mod_eq_of_lt (h x hx)).trans (List.map_id' poss)
    rw [hm]
  · rw [if_neg (by simpa using e), listOfT_eq]
    simp

end H2K.Sw
