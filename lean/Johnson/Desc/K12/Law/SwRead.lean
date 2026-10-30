-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwRead.lean: what the plain reading of a code switch returns is, at each listed
position, the symbol of the stage's three folded words, where the stage's message and its fold's
mask are the two parts of one written tree.

It proves `seatReads : SeatReads` (stated in Johnson/Desc/K12/Law/SwDid.lean), a part of the law of
the proximity test (the kind K12) at a stage behind a switch. Statements and proofs.
What it says. The stage's oracle message o and its fold's mask id are parts 0 and 1 of one tree
(`SeatP`), and every column that the switch is dealt is the column of the written oracle orc of the
round d at the column's own position. Then whatever `Tw.L9.readOld` returns with a yes, at any book
and statement that keep the public part, is at each listed position the symbol of `foldWords s y z`,
at y = wordIn s (colSt s d orc) and z = wordFr s (colSt s d orc).
From which message each word is read. Both words are read off one message, the written oracle orc of
the one round d (in the chain: the first round of the switch that leads to this stage). The main
rows of y are the words 0 to 3 * 2^(h+g) - 1 of a column, its carried mask rows the next 3 * 2^h
words. The fresh mask z, a word without a sample, is the last 3 * 2^h words of the same column. So z
is fixed by the message of the round d, which stands in front of this stage's fold.
How. The proofs are ports, on plain data, of the library's `readParts`
(OnBytes/Slice/BlkOpenN.lean), `readSeat` (OnBytes/Slice/BlkCsRead.lean), `stage_cols` and
`stage_symS` (OnBytes/Slice/BlkCsReadS.lean). These speak of runs in a context and are not called.
Main names:
  `columnsFit_at`: what a yes of Blk.columnsFit says of column number k.
  `openOne_inv`: what a yes of Tw.L9.openOne says: the next columns fit the tree's own list, key and
    width, and they are what is pushed.
  `readOld_inv`: what a yes of Tw.L9.readOld says, line by line.
  `readPartsP`: the port of readParts: where the messages asked for are the parts of one tree of the
    list's range, the columns read are among the dealt ones, at the listed positions, of the tree's
    width, and each part's symbols are cut out of them.
  `seatReads`: the statement above.
Limits: No soundness is claimed, and nothing is said on hiding. The law of the proximity test is not
proved here.
That every tree which a part opens was sent before that part's first round is not shown here
(Johnson/Desc/K12/Law/FixedLaw.lean).
Premises of SeatReads and ReadTie that the proof does not spend: 1 ≤ s.h + s.g; the width PQ.colW
d.tree (the width comes from readOld's own test on the columns and the seat's tree: a column outside
the written tree's range is empty and is refused by that test); i.firstTree = firstTree and the
tree's number n (the premise on the columns speaks of every dealt column, whatever its key);
row.kept = #[]; gamma.length = s.h + s.g (singleRowsSymbols tests it); of pos = Positions.ofDraws
s.C.a poss only pos.logN = s.C.a (one tree is read here, so nothing hangs on how the dealt columns
are cut; at several trees it does: Johnson/Desc/K12/Law/FirstRead.lean).
No cast of a position stands here: a position is a natural number from the list pos.all to colW's
argument, and x : s.Ps enters by x.val ∈ pos.all alone. A word is read by the part as E.mk3 and by
the library as toE (`readE_sym3`, without a bound).
The statement is about one fixed text (Tw.L9.readOld); no member ranges. A reading that says no to
all meets it by its form. A reading that said yes to all and returned any symbols would not meet it:
the conclusion pins the symbols at every listed position. That readOld says yes under all the
premises at once was shown on made-up data in a file that is not in this library.
Of `verify-on-bytes` and the library it uses plain records, pure functions and lemmas on them; no
routine in a context is reached from a statement or a proof (of OnBytes.Ctx, Blk, Chan, Blk.Yields:
none; under the name OnBytes.Blk.*: columnsFit, ownList, symbolsOf, columnOf, pure functions on
data).
Lemmas called: array_mapM_inv, listOf_const, symbolsOf_inv (OnBytes/Slice/BlkOpenN.lean); listOfT_eq
(OnBytes/Chain/Draws.lean); stage_skips, putAt_zero (OnBytes/Slice/BlkCsReadS.lean); stageCol_some,
foldWords_std (OnBytes/Slice/BlkCuts.lean); stage_main, stage_mask, stage_fresh, columnOf_size
(OnBytes/Slice/BlkColumns.lean); symS_of_cols (OnBytes/Slice/BlkCsRead.lean).
Tw.L9.openOne and Tw.L9.readOld test and read by the description's own colsStand, symbolsAt and
rowsSymbols (Johnson/Desc/Own/). The statements here speak of the program's Blk.columnsFit,
Blk.symbolsOf and singleRowsSymbols; they are reached by the theorems of agreement colsStand_agrees
(Johnson/Desc/Own/ShapesAgree.lean), symbolsAt_eq and rowsSymbols_eq
(Johnson/Desc/Own/SymbolsAgree.lean), each an equation at all arguments.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.SwDid
import Johnson.Desc.Own.ShapesAgree
import Johnson.Desc.Own.SymbolsAgree
import OnBytes.Slice.BlkCsReadS

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- What a yes of Blk.columnsFit says of column number k, where the columns are as many as the
positions: it is at the list's position number k and has W words. -/
theorem columnsFit_at (key W : Nat) : ∀ (got : List Tw.L9.Col) (xs : List Nat),
    got.length = xs.length → Blk.columnsFit key W got xs = true →
    ∀ k, k < xs.length → ∃ c ∈ got, got[k]? = some c ∧ c.2.1 = xs.getD k 0 ∧ c.2.2.length = W
  | [], [], _, _ => fun k hk => absurd hk (Nat.not_lt_zero _)
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | g :: got, x :: xs, h, ha => by
    simp only [Blk.columnsFit, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨_, h2⟩, h3⟩, h4⟩ := ha
    intro k hk
    cases k with
    | zero => exact ⟨g, List.mem_cons_self, rfl, h2, h3⟩
    | succ k =>
      obtain ⟨c, c1, c2, c3, c4⟩ := columnsFit_at key W got xs (by simpa using h) h4 k
        (Nat.lt_of_succ_lt_succ hk)
      exact ⟨c, List.mem_cons_of_mem _ c1, c2, c3, c4⟩

/-- What a yes of Tw.L9.openOne says (its test G12): the next dealt columns are as many as the
tree's own list, fit it, and are what is pushed. tree0: the tree in the book B0. -/
theorem openOne_inv (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (B1 : TreeBook) (op : List Tw.L9.Col) (acc : Array (Nat × Array Nat × Array (Array F)))
    (out : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))) (tree0 : Tree)
    (h0 : B0.trees[t]? = some tree0)
    (h : Tw.L9.openOne S firstTree pos B0 t (B1, op, acc) = .ok out) :
    (op.take (Blk.ownList tree0 pos).size).length = (Blk.ownList tree0 pos).size ∧
    Blk.columnsFit (tree0.number - firstTree) (tree0.shape.mainWidth + tree0.shape.maskWidth)
      (op.take (Blk.ownList tree0 pos).size) (Blk.ownList tree0 pos).toList = true ∧
    out.2.2 = acc.push (t, Blk.ownList tree0 pos,
      ((op.take (Blk.ownList tree0 pos).size).map fun y => y.2.2.toArray).toArray) := by
  unfold Tw.L9.openOne at h
  cases h1 : B1.trees[t]? with
  | none => simp [h1] at h
  | some tree =>
    simp only [h1, h0] at h
    split_ifs at h with a b c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases h
    exact ⟨hc.1, (Own.colsStand_agrees _ _ _ _).trans hc.2, rfl⟩

/-- What a yes of Tw.L9.readOld says, line by line (its tests G13, G8-G12, G15, G16). -/
theorem readOld_inv (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) :
    ∃ (places : Array (Nat × Nat)) (cols : Array (Nat × Array Nat × Array (Array F)))
      (opened : Array (Array Column)),
      ((singleRowsOracles i.old).mapM fun o => i.book.place[o]?) = some places ∧
      (listOfT (places.map (·.1)).toList).foldlM
        (fun s t => Tw.L9.openOne i.st i.firstTree pos i.book t s) (i.book, i.opened, #[]) =
          .ok (B, left, cols) ∧
      (((singleRowsOracles i.old).zip places).mapM fun y =>
        Blk.symbolsOf i.st i.book pos cols.toList y.1 y.2) = some opened ∧
      singleRowsSymbols i.old opened pos.all.size = some ys := by
  unfold Tw.L9.readOld at h
  simp only at h
  split at h
  · cases h
  rename_i places hp
  split at h
  · cases h
  split at h
  · cases h
  rename_i B' left' cols hc
  split at h
  · cases h
  rename_i opened ho
  split at h
  · cases h
  rename_i y hy
  cases h
  simp only [Own.symbolsAt_eq] at ho
  rw [Own.rowsSymbols_eq] at hy
  exact ⟨places, cols, opened, hp, hc, ho, hy⟩

/-- The port of readParts. The messages asked for are the parts of one tree, in the parts' order,
and the tree is as long as the list's range. Then a yes of readOld read columns cs that are among
the dealt ones (i.opened), at the listed positions, of the tree's width; the symbols of part p are
cut out of them where part p begins; and ys is what singleRowsSymbols makes of these symbols. -/
theorem readPartsP (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (ids : Array Nat) (hids : singleRowsOracles i.old = ids) (t : Nat) (tree : Tree)
    (hne : 0 < ids.size)
    (hpl : ∀ p (h : p < ids.size), i.book.place[ids[p]]? = some (t, p))
    (htr : i.book.trees[t]? = some tree) (hlog : tree.shape.logN = pos.logN)
    (h : Tw.L9.readOld i pos = .ok (B, left, ys)) :
    ∃ (opened : Array (Array Column)) (cs : Array (Array F)), cs.size = pos.all.size ∧
      singleRowsSymbols i.old opened pos.all.size = some ys ∧
      (∀ k, k < pos.all.size → ∃ c ∈ i.opened, c.2.1 = pos.all.getD k 0 ∧
        c.2.2.length = tree.shape.mainWidth + tree.shape.maskWidth ∧
        cs.getD k #[] = c.2.2.toArray) ∧
      ∀ p (_ : p < ids.size) x, i.st.oracles[ids[p]]? = some x → ∀ k, k < pos.all.size →
        colB opened p k = Blk.columnOf x (OnBytes.Slice.mainSkip tree p) (OnBytes.Slice.maskSkip
            tree p) (cs.getD k #[]) := by
  obtain ⟨places, cols, opened, h1, h3, h5, h6⟩ := readOld_inv i pos B left ys h
  rw [hids] at h1 h5
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ h1
  have hplace : ∀ p (h : p < ids.size), places[p]? = some (t, p) := fun p h =>
    (z2 p h).symm.trans (hpl p h)
  have e3 : listOfT (places.map (·.1)).toList = [t] := by
    rw [listOfT_eq]
    refine listOf_const t _ ?_ ?_
    · intro he
      have hl := congrArg List.length he
      rw [Array.length_toList, Array.size_map, z1, List.length_nil] at hl
      omega
    · intro x hx
      simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨p, hp, rfl⟩ := Array.mem_iff_getElem.1 hq
      have := hplace p (by rw [← z1]; exact hp)
      rw [Array.getElem?_eq_getElem hp] at this
      rw [Option.some.inj this]
  rw [e3, List.foldlM_cons] at h3
  cases ho : Tw.L9.openOne i.st i.firstTree pos i.book t (i.book, i.opened, #[]) with
  | error e =>
    rw [ho] at h3
    cases h3
  | ok out =>
    rw [ho] at h3
    obtain rfl : out = (B, left, cols) := Except.ok.inj h3
    obtain ⟨a1, a2, a3⟩ := openOne_inv _ _ _ _ _ _ _ _ _ tree htr ho
    have hown : Blk.ownList tree pos = pos.all := by
      unfold Blk.ownList
      rw [hlog, if_pos (beq_self_eq_true _)]
    rw [hown] at a1 a2 a3
    have a3' : cols = #[(t, pos.all,
      ((i.opened.take pos.all.size).map fun y => y.2.2.toArray).toArray)] := a3
    subst a3'
    have hcs : (((i.opened.take pos.all.size).map fun y => y.2.2.toArray).toArray).size =
        pos.all.size := by
      rw [List.size_toArray, List.length_map]
      exact a1
    obtain ⟨w1, w2⟩ := array_mapM_inv _ _ _ h5
    have hzs : (ids.zip places).size = ids.size := by
      rw [Array.size_zip, z1, Nat.min_self]
    refine ⟨opened, _, hcs, h6, fun k hk => ?_, fun p hp x hx k hk => ?_⟩
    · obtain ⟨c, c1, c2, c3, c4⟩ := columnsFit_at _ _ _ _ (by rw [a1, Array.length_toList]) a2 k
        (by rw [Array.length_toList]; exact hk)
      refine ⟨c, List.mem_of_mem_take c1, ?_, c4, ?_⟩
      · rw [c3, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
      · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, c2]
        rfl
    · have hp' : p < places.size := by rw [z1]; exact hp
      have q1 := w2 p (by rw [hzs]; exact hp)
      rw [Array.getElem_zip] at q1
      have hpp : places[p] = (t, p) := by
        have := hplace p hp
        rw [Array.getElem?_eq_getElem hp'] at this
        exact Option.some.inj this
      have hop : p < opened.size := by rw [w1, hzs]; exact hp
      rw [Array.getElem?_eq_getElem hop] at q1
      have q2 : Blk.symbolsOf i.st i.book pos [(t, pos.all,
          ((i.opened.take pos.all.size).map fun y => y.2.2.toArray).toArray)] ids[p] (t, p) =
          some opened[p] := by
        rw [← hpp]
        exact q1
      have eo : opened.getD p #[] = opened[p] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hop]
        rfl
      unfold colB
      rw [eo]
      exact symbolsOf_inv _ _ _ _ _ _ _ _ _ _ _ htr hx hlog hcs q2 k hk

/-- (R). Both words are read off the written oracle orc of the one round d: y = wordIn s (colSt s d
orc) off part 0 of its tree (the stage's message o: main rows and carried mask rows), z = wordFr s
(colSt s d orc) off part 1 (the fold's fresh mask id). -/
theorem seatReads : SeatReads := by
  intro firstTree s cu L st book o id n d orc cols poss hk hh _ hL seat _ hcols i pos B left ys S
      row
    eps claim gamma hB hS _ ho hold _ _ hpos hread x hx α
  have hlogN : pos.logN = s.C.a := by rw [hpos]; rfl
  obtain ⟨t, tree0, t1, _, t3, t4, t5, t6⟩ := seat.tree
  obtain ⟨tree, u1, u2, _, _⟩ := hB.tree t tree0 t1
  rw [← u2] at t3 t4 t5
  have hlay : i.old.layout = { L with k := cu.k, h := cu.h } := by rw [hold]; rfl
  have hm : i.old.masks = 2 := by rw [hold]; rfl
  have hfr : i.old.fresh = id := by rw [hold]; rfl
  have hgam : i.old.gamma = gamma := by rw [hold]; rfl
  have hmem : i.old.layout.members = #[o] := by rw [hlay]; exact hL.members
  have hids : singleRowsOracles i.old = #[o, id] := by
    unfold singleRowsOracles
    rw [hm, hmem, hfr]
    rfl
  obtain ⟨opened, cs, hcs, hsym, hwords, hparts⟩ := readPartsP i pos B left ys #[o, id] hids t tree
    (Nat.zero_lt_succ 1)
    (fun p hp => by
      have := hB.place _ _ (t6 p hp)
      match p, hp, this with
      | 0, _, this => exact this
      | 1, _, this => exact this)
    u1 (t3.trans hlogN.symm) hread
  have sh0 : ∀ x0 : OnBytes.Oracle, x0.shape = (stageShapes s cu).getD 0 default →
      x0.shape.mainRows = 2 ^ (s.h + s.g) ∧ x0.shape.mainDeg = 3 ∧ x0.shape.maskRows = 2 ^ s.h :=
    fun x0 e => by rw [e]; exact ⟨rfl, rfl, rfl⟩
  have sh1 : ∀ x1 : OnBytes.Oracle, x1.shape = (stageShapes s cu).getD 1 default →
      x1.shape.maskRows = 2 ^ s.h := fun x1 e => by
    rw [e, ← hh]
    rfl
  obtain ⟨k0, z0, z1⟩ := stage_skips tree _ _ t4 t5 rfl rfl
  have z0' : OnBytes.Slice.maskSkip tree 0 = 3 * 2 ^ (s.h + s.g) := z0
  have z1' : OnBytes.Slice.maskSkip tree 1 = 3 * (2 ^ (s.h + s.g) + 2 ^ s.h) := z1
  have hwid : tree.shape.mainWidth + tree.shape.maskWidth =
      3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h) := by
    unfold TreeShape.mainWidth TreeShape.maskWidth
    rw [t4, t5]
    simp [foldMaskNotice, ioppFoldShape, switchTargetStage, hh]
    ring
  have hcut : ∀ k, k < pos.all.size → Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g))
      (cs.getD k #[]).toList = some (colSt s d orc (pos.all.getD k 0)) := fun k hk => by
    obtain ⟨c, c1, c2, c3, c4⟩ := hwords k hk
    rw [c4, ← c2]
    have c5 := hcols c (ho ▸ c1)
    obtain ⟨col, e⟩ := stageCol_some s.st (2 ^ (s.h + s.g)) c.2.2 (c3.trans hwid)
    have hc : colSt s d orc c.2.1 = col := by
      show (Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) (colW d orc c.2.1)).getD default = col
      rw [← c5, e]
      rfl
    rw [hc]
    exact e
  obtain ⟨y0, e0, s0⟩ := seat.shape 0 (Nat.zero_lt_succ 1)
  obtain ⟨y1, e1, s1⟩ := seat.shape 1 (Nat.lt_succ_self 1)
  obtain ⟨x0, f0, g0⟩ := hS _ _ e0
  obtain ⟨x1, f1, g1⟩ := hS _ _ e1
  obtain ⟨m1, m2, m3⟩ := sh0 x0 (g0.trans s0)
  have f3 := sh1 x1 (g1.trans s1)
  have c0 := hparts 0 (Nat.zero_lt_succ 1) x0 f0
  have c1 := hparts 1 (Nat.lt_succ_self 1) x1 f1
  have hsz : i.old.layout.members.size = 1 := by
    rw [hmem]
    rfl
  have hmf : i.old.layout.mainFirst.getD 0 none = some 0 := by
    rw [hlay]
    show L.mainFirst.getD 0 none = some 0
    rw [hL.mainFirst]
    rfl
  have hzf : i.old.layout.maskFirst.getD 0 none = some 0 := by
    rw [hlay]
    show L.maskFirst.getD 0 none = some 0
    rw [hL.maskFirst]
    rfl
  have hmainAt : ∀ k b, mainAt i.old.layout opened k b =
      putAt (some 0) (colB opened 0 k).main (fun _ => zeroE) b := fun k b => by
    unfold mainAt
    rw [hsz, ← hmf]
    rfl
  have hmaskAt : ∀ k b, maskAt i.old.layout opened k b =
      putAt (some 0) (colB opened 0 k).mask (fun _ => zeroE) b := fun k b => by
    unfold maskAt
    rw [hsz, ← hzf]
    rfl
  rw [foldWords_std, ← hgam]
  refine symS_of_cols s i.old pos opened ys (colSt s d orc) hsym hm (fun w hw => ?_)
    (by rw [hlay]; exact hk) (by rw [hlay]; exact hh) (fun k hk b hb => ?_) (fun k hk b hb => ?_)
    (fun k hk b hb => ?_) x hx α
  · rw [hsz] at hw
    rw [hlay]
    exact hL.kept w hw
  · have hb0 : b < x0.shape.mainRows := by rw [m1]; exact hb
    have h := stage_main x0 (OnBytes.Slice.mainSkip tree 0) (OnBytes.Slice.maskSkip tree 0) (cs.getD
        k #[]) s.st _ _
      (hcut k hk) 0 b hb0 m2 (by rw [k0]) (by rw [Nat.zero_add]; exact hb)
      (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmainAt, c0 k hk, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).1]; exact hb0)]
    exact h
  · have hb0 : b < x0.shape.maskRows := by rw [m3]; exact hb
    have h := stage_mask x0 (OnBytes.Slice.mainSkip tree 0) (OnBytes.Slice.maskSkip tree 0) (cs.getD
        k #[]) s.st _ _
      (hcut k hk) 0 b hb0 (by rw [z0', Nat.add_zero]) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmaskAt, c0 k hk, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).2]; exact hb0)]
    exact h
  · have hb1 : b < x1.shape.maskRows := by rw [f3]; exact hb
    have h := stage_fresh x1 (OnBytes.Slice.mainSkip tree 1) (OnBytes.Slice.maskSkip tree 1)
        (cs.getD k #[]) s.st _ _
      (hcut k hk) 0 b hb1 (by
        rw [z1', Nat.add_zero]
        rfl) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hsz, c1 k hk]
    exact h

end H2K.Sw
