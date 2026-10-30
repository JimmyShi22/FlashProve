-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxSeg.lean: the columns that the program reads are the next of those that are
left to be read.

A view lists its opened columns in the order in which a run reads them, each with its tree's key
and its position. OnBytes/Slice/BlkSeat.lean ties the columns that a block reads to written oracles
by the key: under a tree's key the view holds only that tree's columns. A key is a tree's number
less that of the chain's first tree, or 0 if the number is lower. In a chain that takes trees from
earlier chains several trees have the key 0, and one call can read three of them. And of the columns
that later blocks will read, a statement on one block knows nothing. So this file goes by the order:
what is left to be read begins with a segment, the columns of one tree at a list of positions, and
a reading takes that segment and leaves the rest.

Main definitions.
  segOf      the columns of one tree at a list of positions, as a view lists them: f gives the
             column's words at a position.
  RunOn      what every joint says of the run, but for the columns that are left.
  FoldedFit  what is public of the three folded rows before a switch. Unlike FoldedOk
             (OnBytes/Slice/BlkJointCsAt.lean) it lets the form have a written-out factor.
  SingleFit  the tie after a fold.
Main theorems.
  seg_cut          a reading that has taken a tree's columns has taken the segment.
  readSeat_seg     what is read of the oracle messages that are the parts of one tree.
  stage_symS_seg   the symbols read at a later stage are the long symbols of the three folded
                   words, and the rest is left.
  csRan_positions  the list of positions of a run of the switch, from the written round.
  hread_stage_seg  the same as stage_symS_seg, for a run of the switch.

Not claimed. Nothing on soundness. That a run of the program reaches these ties.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BaseOpen
import OnBytes.Slice.BlkCsReadAt
import OnBytes.Slice.BlkProxOrder

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run

/-- Opened columns as a view lists them: a tree's key, a position, the column's words. -/
abbrev Cols : Type := List (Nat × Nat × List UInt64)

/-- The columns of one tree at the positions xs, as a view lists them. f: the words of the column
at a position. -/
def segOf (key : Nat) (xs : List Nat) (f : Nat → Option (List UInt64)) : Cols :=
  xs.map fun x => (key, x, (f x).getD [])

/-- A reading that has taken a tree's columns has taken the segment. cs: the columns that were
taken at the positions xs. -/
theorem seg_cut (key : Nat) (xs : Array Nat) (cs : Array (Array OnBytes.F))
    (f : Nat → Option (List UInt64)) (l R R' : Cols) (hs : cs.size = xs.size)
    (h1 : l = viewColumns key xs cs ++ R') (h2 : l = segOf key xs.toList f ++ R)
    (hin : ∀ x ∈ xs.toList, (f x).isSome = true) :
    R' = R ∧ ∀ i, i < xs.size → f (xs.getD i 0) = some (cs.getD i #[]).toList := by
  have hlen : (viewColumns key xs cs).length = (segOf key xs.toList f).length := by
    unfold viewColumns segOf
    rw [List.length_map, List.length_map, List.length_zip, Array.length_toList,
      Array.length_toList, hs, Nat.min_self]
  obtain ⟨e1, e2⟩ := List.append_inj (h1.symm.trans h2) hlen
  refine ⟨e2, fun i hi => ?_⟩
  have hm := viewColumns_at key xs cs hs i hi
  rw [e1] at hm
  obtain ⟨x, hx, ex⟩ := List.mem_map.1 hm
  obtain ⟨_, e3⟩ := Prod.mk.inj ex
  obtain ⟨e4, e5⟩ := Prod.mk.inj e3
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hin x hx)
  rw [← e4, hw]
  rw [hw] at e5
  exact congrArg some e5

/-- What every joint says of the run, but for the columns that are left. It is no dry run. The
chain's first tree has the number F. The rounds that are not yet closed are rest. The statement's
codes are K. The number of roots received is roots. A sample has one answer. -/
structure RunOn (F : Nat) (K : Codes) (roots : Nat) (rest : List Fmt.RoundView) (answers : Nat)
    (c : Ctx) : Prop where
  /-- it is no dry run -/
  dry : c.ch.dry = false
  /-- the number of the chain's first tree -/
  first : c.ch.firstTree = F
  /-- the rounds that are not yet closed -/
  pending : c.ch.pending = rest
  /-- the statement's codes -/
  codes : c.st.codes = K
  /-- the number of roots received -/
  roots : c.ch.roots = roots
  /-- a sample has one answer -/
  answers : answers = 1

/-- Keeping a value changes nothing that a joint says of the run. -/
theorem RunOn.notes {F : Nat} {K : Codes} {roots : Nat} {rest : List Fmt.RoundView}
    {answers : Nat} {c c' : Ctx} (h : RunOn F K roots rest answers c)
    (hn : Blk.SameButNotes c c') : RunOn F K roots rest answers c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, h.answers⟩
  · rw [hn.ch]; exact h.dry
  · rw [hn.ch]; exact h.first
  · rw [hn.ch]; exact h.pending
  · rw [hn.st]; exact h.codes
  · rw [hn.ch]; exact h.roots

/-! ## What is read of one tree -/

/-- What is read of the oracle messages that are the parts of one tree, if what is left to be read
begins with the tree's segment at the listed positions. The tree's columns at these positions are
words cs, the values of f. Each message's symbols are cut out of these words. What comes after the
segment is left. -/
theorem readSeat_seg (ids : List ℕ) (pos : Positions) (a a' : Ctx)
    (opened : Array (Array Column)) (n : ℕ) (shapes : List OracleShape) (hd : a.ch.dry = false)
    (hrd : (Blk.readOpened ids.toArray pos).Yields a opened a') (hne : 0 < ids.length)
    (seat : Seat a ids n pos.logN shapes) (f : ℕ → Option (List UInt64)) (R : Cols)
    (hop : a.ch.opened = segOf (n - a.ch.firstTree) pos.all.toList f ++ R)
    (hin : ∀ x ∈ pos.all.toList, (f x).isSome = true) :
    ∃ (tree : Tree) (cs : Array (Array OnBytes.F)),
      tree.shape.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray ∧
      tree.shape.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray ∧
      cs.size = pos.all.size ∧
      (∀ i, i < pos.all.size → f (pos.all.getD i 0) = some (cs.getD i #[]).toList) ∧
      a'.ch.opened = R ∧
      ∀ p, p < ids.length → ∃ x : Oracle, x.shape = shapes.getD p default ∧
        ∀ i, i < pos.all.size →
          colB opened p i = Blk.columnOf x (mainSkip tree p) (maskSkip tree p) (cs.getD i #[]) := by
  obtain ⟨t, tree, h1, h2, h3, h4, h5, h6⟩ := seat.tree
  have hid : ∀ p (h : p < ids.toArray.size), ids.toArray[p] = ids.getD p 0 := fun p h => by
    rw [List.getElem_toArray, List.getD_eq_getElem _ _ (by simpa using h)]
  obtain ⟨cs, hs, hop', _, _, _, hcol⟩ := readParts ids.toArray t pos a a' opened hd hrd tree
    (by rw [List.size_toArray]; exact hne)
    (fun p h => by
      rw [hid p h]
      exact h6 p (by simpa using h)) h1 h3
  rw [h2] at hop'
  obtain ⟨e1, e2⟩ := seg_cut _ pos.all cs f _ R _ hs hop' hop hin
  refine ⟨tree, cs, h4, h5, hs, e2, e1, fun p hp => ?_⟩
  obtain ⟨x, hx, hsh⟩ := seat.shape p hp
  have hp' : p < ids.toArray.size := by rw [List.size_toArray]; exact hp
  exact ⟨x, hsh, fun i hi => hcol p hp' x (by rw [hid p hp']; exact hx) i hi⟩

/-- The program's main table, mask table and fresh column at a listed position have the entries of
the column that the format cuts from the same words, and what comes after the segment is left. f:
the written columns of the tree number n. col: what the format cuts from them. -/
theorem stage_cols_seg (s : Sg) (old : SingleRows) (pos : Positions)
    (a a' : Ctx) (opened : Array (Array Column)) (n o : ℕ) (sh sh' : OracleShape)
    (f : ℕ → Option (List UInt64)) (col : ℕ → Fmt.M1.Col) (hd : a.ch.dry = false)
    (hrd : (Blk.readOpened (singleRowsOracles old) pos).Yields a opened a')
    (hm : old.masks = 2) (hmem : old.layout.members = #[o])
    (hmf : old.layout.mainFirst.getD 0 none = some 0)
    (hzf : old.layout.maskFirst.getD 0 none = some 0)
    (seat : Seat a [o, old.fresh] n pos.logN [sh, sh'])
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h) (R : Cols)
    (hop : a.ch.opened = segOf (n - a.ch.firstTree) pos.all.toList f ++ R)
    (hin : ∀ x ∈ pos.all.toList, (f x).isSome = true)
    (hcut : ∀ x w, f x = some w → Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) w = some (col x)) :
    (∀ i, i < pos.all.size → ∀ b, b < 2 ^ (s.h + s.g) →
      readE (mainAt old.layout opened i b) = vec (col (pos.all.getD i 0)).main b) ∧
    (∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readE (maskAt old.layout opened i b) = vec (col (pos.all.getD i 0)).mask b) ∧
    (∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readV (colB opened old.layout.members.size i).mask b =
        vec (col (pos.all.getD i 0)).fresh b) ∧ a'.ch.opened = R := by
  have hids : singleRowsOracles old = [o, old.fresh].toArray := by
    unfold singleRowsOracles
    rw [hm, hmem]
    rfl
  rw [hids] at hrd
  obtain ⟨tree, cs, w1, w2, _, hwords, hleft, hparts⟩ :=
    readSeat_seg _ pos a a' opened n _ hd hrd (Nat.zero_lt_succ 1) seat f R hop hin
  obtain ⟨k0, z0, z1⟩ := stage_skips tree sh sh' w1 w2 m2 f1
  obtain ⟨x0, e0, c0⟩ := hparts 0 (Nat.zero_lt_succ 1)
  obtain ⟨x1, e1, c1⟩ := hparts 1 (Nat.lt_succ_self 1)
  have e0' : x0.shape = sh := e0
  have e1' : x1.shape = sh' := e1
  have hsz : old.layout.members.size = 1 := by
    rw [hmem]
    rfl
  have hmainAt : ∀ i b, mainAt old.layout opened i b =
      putAt (some 0) (colB opened 0 i).main (fun _ => zeroE) b := fun i b => by
    unfold mainAt
    rw [hsz, ← hmf]
    rfl
  have hmaskAt : ∀ i b, maskAt old.layout opened i b =
      putAt (some 0) (colB opened 0 i).mask (fun _ => zeroE) b := fun i b => by
    unfold maskAt
    rw [hsz, ← hzf]
    rfl
  refine ⟨fun i hi b hb => ?_, fun i hi b hb => ?_, fun i hi b hb => ?_, hleft⟩
  · have hw := hcut _ _ (hwords i hi)
    have hb0 : b < x0.shape.mainRows := by rw [e0', m1]; exact hb
    have h := stage_main x0 (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) s.st _ _ hw 0 b hb0
      (by rw [e0']; exact m2) (by rw [k0]) (by rw [Nat.zero_add]; exact hb)
      (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmainAt, c0 i hi, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).1]; exact hb0)]
    exact h
  · have hw := hcut _ _ (hwords i hi)
    have hb0 : b < x0.shape.maskRows := by rw [e0', m3]; exact hb
    have h := stage_mask x0 (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) s.st _ _ hw 0 b hb0
      (by rw [z0, m1, Nat.add_zero]) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmaskAt, c0 i hi, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).2]; exact hb0)]
    exact h
  · have hw := hcut _ _ (hwords i hi)
    have hb1 : b < x1.shape.maskRows := by rw [e1', f3]; exact hb
    have h := stage_fresh x1 (mainSkip tree 1) (maskSkip tree 1) (cs.getD i #[]) s.st _ _ hw 0 b hb1
      (by
        rw [z1, m1, m3, Nat.add_zero]
        rfl) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hsz, c1 i hi]
    exact h

/-- The symbols read by a run of the reading, at a later stage, are at each listed position the long
symbols of the three folded words at the point that the fold's challenges give, and what comes after
the segment is left. f, col and the hypotheses on them are those of stage_cols_seg. -/
theorem stage_symS_seg (s : Sg) (old : SingleRows) (pos : Positions)
    (a a' : Ctx) (y : Array E) (n o : ℕ) (sh sh' : OracleShape) (f : ℕ → Option (List UInt64))
    (col : ℕ → Fmt.M1.Col) (hd : a.ch.dry = false)
    (hread : (singleRowsRead old pos).Yields a y a')
    (hm : old.masks = 2) (hmem : old.layout.members = #[o])
    (hkept : old.layout.kept.getD 0 false = false)
    (hmf : old.layout.mainFirst.getD 0 none = some 0)
    (hzf : old.layout.maskFirst.getD 0 none = some 0)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (seat : Seat a [o, old.fresh] n pos.logN [sh, sh'])
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h) (R : Cols)
    (hop : a.ch.opened = segOf (n - a.ch.firstTree) pos.all.toList f ++ R)
    (hin : ∀ x ∈ pos.all.toList, (f x).isSome = true)
    (hcut : ∀ x w, f x = some w → Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) w = some (col x)) :
    (∀ (x : s.Ps), x.val ∈ pos.all → ∀ α : s.cMid.Aa,
      s.cMid.T (wordMid s col (readP _ old.gamma)) x α = symS s old pos y x.val α) ∧
      a'.ch.opened = R := by
  obtain ⟨opened, hrd, hsym⟩ := singleRowsRead_inv old pos y a a' hread
  obtain ⟨h1, h2, h3, h4⟩ := stage_cols_seg s old pos a a' opened n o sh sh' f col hd hrd hm hmem
    hmf hzf seat m1 m2 m3 f1 f3 R hop hin hcut
  refine ⟨fun x hx α =>
    symS_of_cols s old pos opened y col hsym hm (fun w hw => ?_) hk hh h1 h2 h3 x hx α, h4⟩
  have hw0 : w = 0 := by
    rw [hmem] at hw
    exact Nat.lt_one_iff.1 hw
  rw [hw0]
  exact hkept

/-! ## A run of the switch -/

/-- What is public of the three folded rows before a switch from the stage s to the stage s'.
K: the statement's codes. nc, nz: the numbers of the new stage's codes. -/
structure FoldedFit (s s' : Sg) (K : Codes) (nc nz : ℕ) (old : SingleRows) : Prop where
  /-- the four codes are the two stages'; two mask rows; no kept member -/
  prog : CsProg s s' K old nc nz
  /-- no form on a kept member -/
  kept : old.kept = #[]
  /-- the vector on the carried mask row has the mask code's message length -/
  d0 : (old.d.getD 0 #[]).size = s.Z.l
  /-- the vector on the fresh mask row likewise -/
  d1 : (old.d.getD 1 #[]).size = s.Z.l
  /-- each tensor of the form has the variables of the main code's message -/
  vars : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l
  /-- each tensor of the form is in order -/
  order : OrderForm old.c

/-- The tie after a fold at the stage s, before a switch to the stage s'. K: the statement's
codes. nc, nz: the numbers of the new stage's codes. n: the number of the tree that holds the
group's members and the fresh mask. pt: the point at which the rows were folded. -/
structure SingleFit (s s' : Sg) (K : Codes) (nc nz n : Nat) (shapes : List OracleShape)
    (mainFirst maskFirst : Array (Option Nat)) (pt : Fin (s.h + s.g) → GE) (c : Ctx)
    (old : SingleRows) : Prop where
  /-- what a code switch asks of the three folded rows -/
  ok : FoldedFit s s' K nc nz old
  /-- the row variables of the main table -/
  k : old.layout.k = s.h + s.g
  /-- the row variables of the mask table -/
  h : old.layout.h = s.h
  /-- the point at which the rows were folded -/
  gamma : readP (s.h + s.g) old.gamma = pt
  /-- the members, and that they and the fresh mask are the parts of the tree -/
  seat : ∃ ms : List Nat, LayAt ms mainFirst maskFirst old.layout ∧
    Seat c (ms ++ [old.fresh]) n s.C.a shapes

/-- A tie after a fold looks at the book and at the oracle messages alone. -/
theorem SingleFit.congr {s s' : Sg} {K : Codes} {nc nz n : Nat} {shapes : List OracleShape}
    {mainFirst maskFirst : Array (Option Nat)} {pt : Fin (s.h + s.g) → GE} {c c' : Ctx}
    {old : SingleRows} (h : SingleFit s s' K nc nz n shapes mainFirst maskFirst pt c old)
    (hb : c'.book = c.book) (ho : c'.st.oracles = c.st.oracles) :
    SingleFit s s' K nc nz n shapes mainFirst maskFirst pt c' old := by
  obtain ⟨ms, h1, h2⟩ := h.seat
  exact ⟨h.ok, h.k, h.h, h.gamma, ms, h1, h2.congr hb ho⟩

/-- The positions that a written round draws, as a list by which trees of depth a are opened. -/
def listAt (a : ℕ) (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) : Positions :=
  Positions.ofDraws a (rvOf d m c).poss

/-- A listed position was drawn. -/
theorem mem_listAt (a : ℕ) (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) (x : ℕ)
    (h : x ∈ (listAt a d m c).all.toList) : x ∈ (rvOf d m c).poss := by
  have h' : x ∈ listOfT (rvOf d m c).poss := by simpa [listAt, Positions.ofDraws] using h
  rw [listOfT_eq, Fmt.listOf_mem] at h'
  exact h'

section
variable {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- The list of positions of a run of the switch is that of the written round of the positions. -/
theorem csRan_positions {s s' : Sg} {nc nz : ℕ}
    (h : CsRan old T gp others c c' out row lay theta D) (P : CsProg s s' c.st.codes old nc nz)
    (dS dC : PQ.RD) (τ : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView)
    (hp : c.ch.pending = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest) :
    out.positions = listAt s.C.a dC τ.2.2.1 τ.2.2.2.1 := by
  have e : D.rS :: D.rC :: D.rest = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest :=
    h.pending.symm.trans hp
  injection e with _ e2
  injection e2 with eC _
  have poC : D.rC.drawn.poss = (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [eC]; rfl
  have hl := h.logN_eq P
  rw [h.positions] at hl ⊢
  have hl' : D.code.logN = s.C.a := hl
  rw [hl', poC]
  rfl

end

/-- The symbols that the switch after a later stage's fold reads are, at each drawn position, the
long symbols of the three folded words of the written columns (colSt), and the run leaves what comes
after the tree's segment. d, m: the round that sent the stage's tree, and its written message. n:
the tree's number. sh, sh': the shapes of the stage's oracle message and of the fresh mask. pt: the
point of the fold. -/
theorem hread_stage_seg (F : Nat) (K : Codes) (roots : ℕ) {s s' : Sg} (dS dC : PQ.RD)
    (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView)
    (nc nz n : ℕ) (sh sh' : OracleShape) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD)
    (m : (wRound d).Msg) (hN : PQ.posN d.tree = 2 ^ s.C.a)
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (T : SwitchTarget) (others : Array OracleNotice)
    (c c' : Ctx) (rows : SingleRows) (gp : ℕ) (sw : Switched) (row' : GroupRow)
    (L' : GroupLayout) (theta : E) (D : CsTaken) (R : Cols)
    (hrun : RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c)
    (hop : c.ch.opened =
      segOf (n - F) (listAt s.C.a dC τC.2.2.1 τC.2.2.2.1).all.toList (treeCol d m) ++ R)
    (ht : SingleFit s s' K nc nz n [sh, sh'] #[some 0] #[some 0] pt c rows)
    (h : CsRan rows T gp others c c' sw row' L' theta D) :
    (∀ (i : Fin s.t) (α : s.cMid.Aa),
      s.cMid.T (wordMid s (colSt s d m.1) pt) ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
        symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α) ∧
      c'.ch.opened = R := by
  obtain ⟨ms, hl, hseat⟩ := ht.seat
  obtain ⟨o, rfl⟩ : ∃ o, ms = [o] := List.length_eq_one_iff.1 (by
    have k := hseat.len
    simp only [List.length_append, List.length_cons, List.length_nil] at k
    omega)
  have hP : CsProg s s' c.st.codes rows nc nz := hrun.codes ▸ ht.ok.prog
  have hlog : sw.positions.logN = s.C.a := h.logN_eq hP
  have hpos := csRan_positions h hP dS dC τC rest hrun.pending
  obtain ⟨k1, k2⟩ := stage_symS_seg s rows sw.positions D.cB D.cC D.y n o sh sh' (treeCol d m)
    (colSt s d m.1) h.dryB h.read ht.ok.prog.masks hl.members
    (hl.kept 0 Nat.one_pos) (by rw [hl.mainFirst]; rfl) (by rw [hl.maskFirst]; rfl) ht.k ht.h
    (by rw [hlog]; exact h.seatOld hseat) m1 m2 m3 f1 f3 R
    (by rw [h.openedB, h.firstB, hrun.first, hpos]; exact hop)
    (fun x hx => by
      rw [hpos] at hx
      have hlt := hr.cs.poss_lt τC.2.2.1 τC.2.2.2.1 x (mem_listAt _ _ _ _ x hx)
      unfold treeCol
      rw [if_pos (by rw [hN]; exact hlt)]
      rfl) (colSt_cut s d m hW)
  refine ⟨fun i α => ?_, h.opened.trans k2⟩
  rw [← ht.gamma]
  exact k1 _ (h.listed _ (h.drawn dS dC hr τC rest hrun.pending i)) α

end OnBytes.Slice.ProxRun
