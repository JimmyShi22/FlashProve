-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/HyStage.lean: at a code switch out of a stage that is not the first: the symbols
that the description's switch has read of the old rows are the long symbols of the code word of the
folded messages with the folded tails: the premise `hy` of `claim_behind`
(Johnson/Prover/Link/SwitchHolds.lean), from the columns that the switch was dealt.

Main names (namespace `Johnson.Prover.Link`).
  `read_of_tie`   `ReadTie` (Johnson/Desc/K12/Law/JointK.lean) at the statement and the book in
      front of the switch, and what the switch has done (`Did`, Johnson/Desc/K12/Law/SwDid.lean):
      at each drawn position what was read is the long symbol of the three folded words
  `length_stageColW`   a written column has 3 * 2^k + 3 * (2 * 2^h) words
  `dStage`, `orcOf`, `colW_orcOf`   a round's data with a tree of the stage's depth and width, and
      the written oracle that a function from positions to columns makes; its columns are the
      function's
  `colSt_written`   the cut of that oracle's column, as the soundness side cuts it (`colSt`,
      OnBytes/Slice/SemLib.lean), is the cut of the written column
  `hy_stage`   each dealt column is the written column at its own position, which lies in the
      stage's range · the public premises of `SeatReads` · the old rows are a fold's output: then
      `hy` at `foldMsg` and `foldTl` (Johnson/Prover/Link/FoldEnc.lean)

On `dStage` and `orcOf`. `SeatReads` speaks of the dealt columns as values of a written oracle of
some round. Its end, and `hy_stage`'s, name neither the round nor the oracle: they speak of what
`readOld` returned on the dealt columns. So the round's data is made here, as a tool of the proof;
what ties the statement to the verifier is the list of the dealt columns in `Did`.

By: `seatReads` (Johnson/Desc/K12/Law/SwRead.lean), `Did.bookKeepsB`, `Did.shapesKeepB`,
`Did.listed` (Johnson/Desc/K12/Law/SwTies.lean), `wordIn_written`, `wordFr_written`
(Johnson/Prover/Link/SymTie.lean), `foldWords_enc`.

Limits. Every premise is asked. That `readOld` says yes is inside `Did`. The first stage's tree has
another reading law (Johnson/Desc/K12/Law/FirstRead.lean). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SymTie
import Johnson.Prover.Link.FoldEnc
import Johnson.Desc.K12.Law.SwRead
import Johnson.Desc.K12.Law.SwTies
import OnBytes.Slice.SemLib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK

section Tie
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **What was read is the long symbol of the three folded words.** -/
theorem read_of_tie (s : Sg) (y : s.cIn.Word) (z : s.cFr.Word) (F : FoldShape) (id : ℕ)
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hR : ReadTie ft s y z F S Bk id cols D.rC.drawn.poss)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ F row₀ id eps gamma claim) (hk : row₀.kept = #[])
    (hγ : gamma.length = s.h + s.g) (hlog : D.code.logN = s.C.a)
    (x : s.Ps) (hx : x.val ∈ D.rC.drawn.poss) (α : s.cMid.Aa) :
    s.cMid.T (foldWords s y z (readP (s.h + s.g) gamma)) x α =
      symS s old out.positions D.y x.val α := by
  obtain ⟨i0, left, i1, i2, i3, i4, i5, i6⟩ := h.read
  have e := hR i0 out.positions Bk' left D.y S₀ row₀ eps claim gamma
    (by rw [i2]; exact h.bookKeepsB) (by rw [i1]; exact h.shapesKeepB) i3 i4 (i5.trans hold) hk hγ
    (by rw [h.positions, hlog]) i6 x (h.listed _ hx) α
  rw [i5] at e
  exact e

end Tie

/-! ## A written oracle from a function of the position -/

variable (s : Sg) (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE)

theorem length_stageColW (x : ℕ) : (stageColW s tabM tabZ tM tZ fM fT x).length =
    3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h) := by
  unfold stageColW
  rw [length_wordsOf, List.length_append, List.length_append, length_wr, length_wr, length_wr]
  omega

/-- A round's data with a tree of the stage's depth and a column's width. A tool of the proof. -/
def dStage : PQ.RD :=
  ⟨{ name := "" }, .elems, [],
    some { a := s.C.a, W := 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h), tree := 0 }, []⟩

/-- The written oracle that a function from positions to columns makes. -/
def orcOf (d : PQ.RD) (f : ℕ → List UInt64) : (wRound d).Orc := fun x k => (f x.val).getD k.val 0

theorem colW_orcOf (d : PQ.RD) (f : ℕ → List UInt64) (x : ℕ) (hx : x < PQ.posN d.tree)
    (hl : (f x).length = PQ.colW d.tree) : OnBytes.Slice.colW d (orcOf d f) x = f x := by
  unfold OnBytes.Slice.colW
  rw [dif_pos hx]
  refine List.ext_getElem (by rw [List.length_ofFn, hl]) fun k h1 h2 => ?_
  rw [List.getElem_ofFn]
  show (f x).getD k 0 = _
  rw [List.getD_eq_getElem _ _ h2]

/-- The cut of the made oracle's column is the cut of the written column. -/
theorem colSt_written (x : ℕ) (hx : x < 2 ^ s.C.a) :
    Fmt.M1.stageCol s.st 0 (2 ^ s.st.k) (stageColW s tabM tabZ tM tZ fM fT x) =
      some (colSt s (dStage s) (orcOf (dStage s) (stageColW s tabM tabZ tM tZ fM fT)) x) := by
  obtain ⟨c, hc, -⟩ := stageCol_written s tabM tabZ tM tZ fM fT x
  unfold colSt
  rw [colW_orcOf (dStage s) _ x hx (length_stageColW s tabM tabZ tM tZ fM fT x), hc]
  rfl

section Stage
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **`hy` at a stage that is not the first.** -/
theorem hy_stage (hs : s.Sized) (cu : IoppStage) (L : GroupLayout) (o id n : ℕ)
    (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (h1 : 1 ≤ s.h + s.g)
    (hL : LayAt [o] #[some 0] #[some 0] L)
    (seat : SeatP S Bk [o, id] n s.C.a (stageShapes s cu))
    (hcols : ∀ c ∈ cols, c.2.1 < 2 ^ s.C.a ∧ c.2.2 = stageColW s tabM tabZ tM tZ fM fT c.2.1)
    (μ : s.cIn.J → GE) (ρ : s.cIn.Q → GE) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hM : ∀ b j, μ (.inl (b, j)) = tabM (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val))
    (hZ : ∀ b j, μ (.inr (b, j)) = tabZ (Sz.rowNo b + 2 ^ s.h * j.val))
    (hTM : ∀ b q, ρ (.inl (b, q)) = tM (Sz.rowNo b) q.val)
    (hTZ : ∀ b q, ρ (.inr (b, q)) = tZ (Sz.rowNo b) q.val)
    (hF : ∀ b j, φ (b, j) = fM (Sz.rowNo b) j.val) (hT : ∀ b q, ψ (b, q) = fT (Sz.rowNo b) q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g) (hlog : D.code.logN = s.C.a)
    (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (ht : D.rC.drawn.poss.length = s.t) :
    ∀ i α, s.cMid.T (s.cMid.enc (foldMsg s μ φ (readP (s.h + s.g) gamma))
        (foldTl s ρ ψ (readP (s.h + s.g) gamma))) (Qs i) α =
      symS s old out.positions D.y (Qs i).val α := by
  intro i α
  have hR := seatReads ft s cu L S Bk o id n (dStage s)
    (orcOf (dStage s) (stageColW s tabM tabZ tM tZ fM fT)) cols D.rC.drawn.poss hk hh h1 hL seat rfl
    (fun c hc => by
      rw [colW_orcOf (dStage s) _ c.2.1 (hcols c hc).1
        (length_stageColW s tabM tabZ tM tZ fM fT c.2.1)]
      exact (hcols c hc).2)
  have hx : (Qs i).val ∈ D.rC.drawn.poss := by
    rw [hQ i, List.getD_eq_getElem _ _ (by rw [ht]; exact i.isLt)]
    exact List.getElem_mem _
  have e := read_of_tie s _ _ (ioppFoldShape cu L) id h hR S₀ row₀ eps claim gamma hold hkept hγ
    hlog (Qs i) hx α
  rw [wordIn_written s tabM tabZ tM tZ fM fT _ μ ρ hM hZ hTM hTZ
      (fun x hx => colSt_written s tabM tabZ tM tZ fM fT x hx),
    wordFr_written s tabM tabZ tM tZ fM fT _ φ ψ hF hT
      (fun x hx => colSt_written s tabM tabZ tM tZ fM fT x hx),
    foldWords_enc s hs] at e
  exact e

end Stage

end Johnson.Prover.Link
