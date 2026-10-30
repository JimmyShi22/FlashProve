-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsReadAt.lean: what a run of the program's code switch reads of the old rows, at
the standard readings.

A code switch reads the three folded rows at the drawn positions. The claim after the switch
(OnBytes/Slice/BlkCsClaim.lean) asks that the symbols which the run has read are the long symbols of
a word at these positions. This file shows it, for a run on a view, of the three folded words that
the standard readings take from the written tree (OnBytes/Slice/SemLib.lean: `col1`, `colSt`), in
the form in which the joints (what is known between two blocks of a run) ask it
(OnBytes/Slice/BlkJointCsAt.lean).

It joins what is shown elsewhere. The tie after a fold (OnBytes/Slice/BlkTies.lean) says in which
tree the old rows are. A run of the switch keeps that until it reads them. The reading gives the
view's columns, cut as the program cuts them, which is as the format cuts them
(OnBytes/Slice/BlkCsReadS.lean, BlkCsReadG.lean). The format can cut every column of a written tree
of the right width (OnBytes/Slice/BlkCuts.lean).

Main theorems.
 `CsRan.onViewB`, `CsRan.shapesKeepB`, `CsRan.seatOld`: what holds when the old rows are read.
 `CsRan.listed`, `CsRan.logN_eq`, `CsRan.drawn`: the drawn positions.
 `hread_stage`: the switch after a later stage's fold.
 `hread_group`: the switch after the first fold.

Not claimed. That the view shows the written tree's columns under the tree's number, the tree's
width, and the shapes' numbers of rows: these are hypotheses.
-/
import OnBytes.Slice.BlkTies
import OnBytes.Slice.BlkCsReadS
import OnBytes.Slice.BlkCsReadG
import OnBytes.Slice.BlkCuts

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-! ## Before the old rows are read -/

section
variable {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- A run of the switch on a view is a run on that view when it comes to read the old rows. -/
theorem CsRan.onViewB (h : CsRan old T gp others c c' out row lay theta D) (V : Fmt.View)
    (hv : OnView V c) : OnView V D.cB :=
  ⟨h.dryB, h.firstB.trans hv.first, fun o ho => hv.opened o (h.openedB ▸ ho)⟩

/-- Each older oracle message is there, with its shape, when the old rows are read. -/
theorem CsRan.shapesKeepB (h : CsRan old T gp others c c' out row lay theta D) :
    ShapesKeep c.st D.cB.st := by
  intro o x hx
  have ho : o < c.st.oracles.size := by
    rcases Nat.lt_or_ge o c.st.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  have h1 : (D.cB.st.oracles[o]?).map (·.shape)
      = ((stSent c.st (sentOf T others)).oracles[o]?).map (·.shape) := by
    rw [h.stB]
    unfold CsTaken.stA
    rw [admitted_shape]
  rw [stSent_old c.st _ o ho, hx] at h1
  cases hx' : D.cB.st.oracles[o]? with
  | none =>
    rw [hx'] at h1
    cases h1
  | some x' =>
    rw [hx'] at h1
    exact ⟨x', rfl, Option.some.inj h1⟩

/-- The parts of an older tree remain its parts when the old rows are read. -/
theorem CsRan.seatOld (h : CsRan old T gp others c c' out row lay theta D) {ids : List ℕ}
    {n logN : ℕ} {shapes : List OracleShape} (hs : Seat c ids n logN shapes) :
    Seat D.cB ids n logN shapes :=
  hs.keeps (by rw [h.bookB]; exact bookSent_keeps c _ D.lay) h.shapesKeepB

/-- A drawn position is in the list by which the trees are opened. -/
theorem CsRan.listed (h : CsRan old T gp others c c' out row lay theta D) (x : ℕ)
    (hx : x ∈ D.rC.drawn.poss) : x ∈ out.positions.all := by
  rw [h.positions]
  show x ∈ (listOfT D.rC.drawn.poss).toArray
  rw [listOfT_eq]
  exact List.mem_toArray.2 ((Fmt.listOf_mem _ x).2 hx)

/-- The list of positions has the logN of the old main code, which is the stage's. -/
theorem CsRan.logN_eq {s s' : Sg} {nc nz : ℕ}
    (h : CsRan old T gp others c c' out row lay theta D) (P : CsProg s s' c.st.codes old nc nz) :
    out.positions.logN = s.C.a := by
  have hC : codeOf D.code = s.C := by
    have k := P.code
    rw [h.code] at k
    exact Option.some.inj k
  rw [h.positions, ← hC]
  rfl

/-- The positions that the library reads off the written round are drawn in the run. -/
theorem CsRan.drawn {s s' : Sg} (h : CsRan old T gp others c c' out row lay theta D)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (τ : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (hp : c.ch.pending = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest)
    (i : Fin s.t) :
    ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i).val ∈ D.rC.drawn.poss := by
  have e : D.rS :: D.rC :: D.rest = PQ.rvSL (ckP .two) [dS, dC] τ ++ rest :=
    h.pending.symm.trans hp
  injection e with _ e2
  injection e2 with eC _
  have poC : D.rC.drawn.poss = (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [eC]; rfl
  obtain ⟨alpha, th, xs, hrv, hxs, _, _, hQ⟩ := cs_read hr.cs τ.2.2.1 τ.2.2.2.1
  rw [hrv] at poC
  rw [poC, hQ i, List.getD_eq_getElem _ _ (by rw [hxs]; exact i.isLt)]
  exact List.getElem_mem _

end

/-! ## The two switches -/

/-- The symbols that the switch after a later stage's fold reads are, at each drawn position, the
long symbols of the three folded words of the written columns (`colSt`). d, m: the round that sent
the stage's tree, and its written message. n: the tree's number. sh, sh': the shapes of the stage's
oracle message and of the fresh mask. pt: the point of the fold. -/
theorem hread_stage (V : Fmt.View) (K : Codes) (roots : ℕ) {s s' : Sg} (dS dC : PQ.RD)
    (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView)
    (nc nz n : ℕ) (sh sh' : OracleShape) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD)
    (m : (wRound d).Msg) (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (T : SwitchTarget) (others : Array OracleNotice)
    (c c' : Ctx) (rows : SingleRows) (gp : ℕ) (sw : Switched) (row' : GroupRow)
    (L' : GroupLayout) (theta : E) (D : CsTaken)
    (hrun : RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c)
    (ht : SingleTie s s' K nc nz n [sh, sh'] #[some 0] #[some 0] pt c rows)
    (h : CsRan rows T gp others c c' sw row' L' theta D) (i : Fin s.t) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s (colSt s d m.1) pt) ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
      symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α := by
  obtain ⟨ms, hl, hseat⟩ := ht.seat
  -- The group has one member.
  obtain ⟨o, rfl⟩ : ∃ o, ms = [o] := List.length_eq_one_iff.1 (by
    have k := hseat.len
    simp only [List.length_append, List.length_cons, List.length_nil] at k
    omega)
  have hlog : sw.positions.logN = s.C.a := h.logN_eq (hrun.codes ▸ ht.ok.prog)
  rw [← ht.gamma]
  exact stage_symS V s rows sw.positions D.cB D.cC D.y n o sh sh' (treeCol d m) (colSt s d m.1)
    (h.onViewB V hrun.onView) h.read ht.ok.prog.masks hl.members (hl.kept 0 Nat.one_pos)
    (by rw [hl.mainFirst]; rfl) (by rw [hl.maskFirst]; rfl) ht.k ht.h
    (by rw [hlog]; exact h.seatOld hseat) m1 m2 m3 f1 f3 hshow (colSt_cut s d m hW) _
    (h.listed _ (h.drawn dS dC hr τC rest hrun.pending i)) α

/-- The same for the switch after the first fold, with the columns `col1`. S: the sizes of the link,
whose group has two members of the kind mem, the second from row f1 on, without mask rows. d, m: the
round that sent the first tree, and its written message. n: the tree's number. sh, fr: the shapes of
a member and of the fresh mask. pt: the point of the fold. -/
theorem hread_group (V : Fmt.View) (K : Codes) (roots : ℕ) (S : Sz) {s s' : Sg} (hs0 : s.h = 0)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (nc nz n : ℕ) (sh fr : OracleShape) (pt : Fin (s.h + s.g) → GE)
    (d : PQ.RD) (m : (wRound d).Msg) (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf : mem.rows ≤ f1) (hk1 : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (T : SwitchTarget) (others : Array OracleNotice)
    (c c' : Ctx) (rows : SingleRows) (gp : ℕ) (sw : Switched) (row' : GroupRow)
    (L' : GroupLayout) (theta : E) (D : CsTaken)
    (hrun : RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c)
    (ht : SingleTie s s' K nc nz n [sh, sh, fr] #[some 0, some f1] #[none, none] pt c rows)
    (h : CsRan rows T gp others c c' sw row' L' theta D) (i : Fin s.t) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s (col1 S d m.1) pt) ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
      symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α := by
  obtain ⟨ms, hl, hseat⟩ := ht.seat
  -- The group has two members.
  obtain ⟨o0, o1, rfl⟩ : ∃ o0 o1, ms = [o0, o1] := List.length_eq_two.1 (by
    have k := hseat.len
    simp only [List.length_append, List.length_cons, List.length_nil] at k
    omega)
  have hlog : sw.positions.logN = s.C.a := h.logN_eq (hrun.codes ▸ ht.ok.prog)
  rw [← ht.gamma]
  exact group_symS V s hs0 rows sw.positions D.cB D.cC D.y n o0 o1 sh fr (treeCol d m)
    (col1 S d m.1) (h.onViewB V hrun.onView) h.read ht.ok.prog.masks hl.members hl.kept ht.k ht.h
    mem hE hm0 f1 hst hf hk1 (by rw [hl.mainFirst]; rfl) (by rw [hl.mainFirst]; rfl)
    (by rw [hl.maskFirst]; rfl) (by rw [hl.maskFirst]; rfl)
    (by rw [hlog]; exact h.seatOld hseat) hR h3 hz hfm hfz hshow
    (fun x w hx => hmems ▸ col1_cut S d m hW x w hx) _
    (h.listed _ (h.drawn dS dC hr τC rest hrun.pending i)) α

end OnBytes.Slice

#print axioms OnBytes.Slice.CsRan.onViewB
#print axioms OnBytes.Slice.CsRan.shapesKeepB
#print axioms OnBytes.Slice.CsRan.seatOld
#print axioms OnBytes.Slice.CsRan.listed
#print axioms OnBytes.Slice.CsRan.logN_eq
#print axioms OnBytes.Slice.CsRan.drawn
#print axioms OnBytes.Slice.hread_stage
#print axioms OnBytes.Slice.hread_group
