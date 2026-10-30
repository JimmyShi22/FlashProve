-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlocksBySource.lean: the blocks that take off a fold and the base case, below half the
stage's distance, with a count for each of the two codes by that code's own distance.

A stage has two codes, the main code and the mask code repeated to the main code's length, each with
a distance of its own (`Sg.dC`, `Sg.dZ`, OnBytes/Slice/Numbers.lean). The stage's distance `Sg.d` is
the smaller. At a radius e with 2 e below `Sg.d`, a line through two words under one of the codes
has at most e + 1 exceptional points if 3 e is below that code's own distance (`Fit.mca`), and at
most 2^a, the number of the main code's positions, in any case, if the code has a coefficient
(`Sg.Pos`; OnBytes/Slice/NumbersHalf.lean). This file takes for each code the smaller count that is
proved (`Sg.cntC`, `Sg.cntZ`). So one theorem holds four cases: 3 e below both codes' own distances;
below neither; below the mask code's alone (OnBytes/Slice/FoldAtMixed.lean); below the main code's
alone. All four under `Sg.Sized` and `Sg.Pos`; in the first case OnBytes/Slice/FoldAt.lean and
OnBytes/Slice/BaseAt.lean do without the second.

Main definitions: `Sg.cntC`, `Sg.cntZ`, `mixedSg`.
Main theorems.
 `Sg.mcaThird_cM`   one main row, below a third of the main code's own distance: e + 1.
 `Sg.mcaSrc_cM`, `Sg.mcaSrc_cZ`, `Sg.mcaSrc_cIn`   one main row, one mask row, the tables before the
                    fold: the counts cntC, cntZ, and their sum.
 `Sg.errOK_src`, `foldNums_src`, `fold_block_src`, `fold_holds_src`   the fold.
 `baseCodes_src`, `base_holds_src`   the base case.
 `mixed_sizes`      at a stage made by hand (`mixedSg`: 2^23 and 2^17 positions, 4,194,565 and 8,453
                    coefficients) the radius 2,097,021 is below half the stage's distance, and the
                    two counts differ: 2^23 for a main row, 2,097,022 for a mask row.

Not claimed. Nothing at half the stage's distance or beyond. Nothing for a stage without a mask
code: a stage here always has a mask row, and `Sg.Pos` asks that its code have a coefficient. That
these counts are the least, or the planner's, is not shown here. Where 3 e is below the stage's
distance (the first case), OnBytes/Slice/BaseAt.lean has the smaller count e + 1 for the tables
before the fold, where this file has 2 (e + 1). Each entry of `foldErr` and `baseErr` is a number of
the library's times the number in the law of the format's sampler. The counts enter thus: the round
of the j-th row variable (j = 1 .. h + g) has cntC + 2, and 2 cntZ more for j up to h; the base
case's first round has cntC + cntZ + 1. The fold's first round, before these (1), and the base
case's second ((2^a - e - 1)^t) hold no count. The blocks are applied at no stage here. Through
OnBytes/Slice/NumbersHalf.lean this file depends on the library's Code/Half.lean.

-/
import OnBytes.Slice.BaseAt
import OnBytes.Slice.NumbersHalf
import OnBytes.Slice.FoldAtMixed

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

namespace Sg

/-- The count for a main row at the radius e: e + 1 where 3 e is below the main code's own distance,
else 2^a. -/
def cntC (s : Sg) (e : ℕ) : ℕ := if 3 * e < s.dC then e + 1 else 2 ^ s.C.a

/-- The count for a mask row at the radius e: e + 1 where 3 e is below the repeated mask code's own
distance, else 2^a, a the main code's. -/
def cntZ (s : Sg) (e : ℕ) : ℕ := if 3 * e < s.dZ then e + 1 else 2 ^ s.C.a

variable {s : Sg}

/-- One main row, at a radius below a third of the main code's own distance: a line through two
words has at most e + 1 exceptional points. -/
theorem mcaThird_cM (h : s.Sized) {e : ℕ} (h3 : 3 * e < s.dC) : s.cM.MCAat e (e + 1) :=
  (fit_ldOf s.C s.C.a rfl h.small h.roomC).mca h3

/-- One main row, below half the stage's distance: at most cntC exceptional points. -/
theorem mcaSrc_cM (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cM.MCAat e (s.cntC e) := by
  unfold cntC
  split
  · exact mcaThird_cM h ‹_›
  · exact mcaHalf_cM h hp h2

/-- One mask row, below half the stage's distance: at most cntZ exceptional points. -/
theorem mcaSrc_cZ (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cZ.MCAat e (s.cntZ e) := by
  unfold cntZ
  split
  · exact mcaThird_cZ h ‹_›
  · exact mcaHalf_cZ h hp h2

/-- The tables before the fold, below half the stage's distance: at most cntC + cntZ exceptional
points. -/
theorem mcaSrc_cIn (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cIn.MCAat e (s.cntC e + s.cntZ e) :=
  ld_mca_pair GE s.Ps _ _ e _ _ ((fit_cM h).mcaRows (mcaSrc_cM h hp h2) _)
    ((fit_cZ h).mcaRows (mcaSrc_cZ h hp h2) _)

/-- The numbers of a folding over the codes of a stage, below half the stage's distance: lists of
one code word; at every halving at most cntC exceptional points for the main rows and at most cntZ
for each of the two tables of mask rows. -/
theorem errOK_src (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d)
    (Y : SumPar GE s.Ps) (hC : Y.C = s.cM) (hZ : Y.Z = s.cZ) (hW : Y.Zw = s.cZ) :
    Y.ErrOK e (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e) (fun _ => s.cntZ e) := by
  have he : e < s.d := by omega
  refine errOK_of Y s.d e _ _ _ ?_ h2 ?_ ?_ ?_
  · rw [hC, hZ, hW]
    exact codesOK h he
  · rw [hC]
    exact mcaSrc_cM h hp h2
  · rw [hZ]
    exact mcaSrc_cZ h hp h2
  · rw [hW]
    exact mcaSrc_cZ h hp h2

end Sg

/-- The numbers of a fold below half the stage's distance. -/
theorem foldNums_src {s : Sg} (hs : s.Sized) (hq : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    (s.par 0).ErrOK e (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e) (fun _ => s.cntZ e) :=
  Sg.errOK_src hs hq h2 (s.par 0) rfl rfl rfl

/-- A fold is taken off, at the format's rounds, below half the stage's distance. -/
theorem fold_block_src (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
    (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb))
    (t : Shape) (εt : Err t) (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col)
    (hno : ∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w)
    (bad : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT) ++ t) → Prop)
    (hp : ∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b))
    (H : ∀ (τ : Tr (PQ.uL (ckP .two) (dE :: List.replicate (s.h + s.g) dT))) sigma eps ps rs1 qs g,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[sigma], [eps], ps⟩, rs1) →
      Fmt.M1.takeRounds (s.h + s.g) rs1 = some (qs, g, []) →
      (∀ w, ¬ s.RMid e (stmMid s (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g),
        wordMid s col (ptL _ g)) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) :
    Doomed _ (Err.app (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e)
      (fun _ => s.cntZ e)) εt) bad :=
  fold_block s s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_src hs hq h2) dE dT
    (foldRounds_of hdE hdT) t εt G col hno bad hp H

/-- The same block, in the form in which the blocks are joined. -/
theorem fold_holds_src (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
    (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds s e dE dT (foldErr s dE dT (fun _ => 1) (fun _ => s.cntC e) (fun _ => s.cntZ e)
      (fun _ => s.cntZ e)) :=
  fun t εt G col hno bad hp H =>
    fold_block_src s hs hq e h2 dE dT na nb hdE hdT t εt G col hno bad hp H

/-- The numbers of the base case below half the stage's distance. -/
theorem baseCodes_src {s : Sg} (h : s.Sized) (hq : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    BaseCodes s e (s.cntC e + s.cntZ e) 1 :=
  ⟨(Sg.fit_cIn h).laws, Sg.mcaSrc_cIn h hq h2, Sg.list_pairs h h2⟩

/-- The base case is taken off, at the format's two rounds and below half the stage's distance, in
the form in which the blocks are joined. -/
theorem base_holds_src (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hs : s.Sized) (hq : s.Pos) (e : ℕ)
    (h2 : 2 * e < s.d) (dL dB : PQ.RD) (work tree : ℕ) (hL : IsRd dL Fmt.M1.rLambda)
    (hB : IsRd dB (Fmt.M1.rBase work s.st tree)) :
    BaseHolds s e dL dB (baseErr s e (s.cntC e + s.cntZ e) 1 dL dB) :=
  fun G col mk last hlast hno bad hp H =>
    base_block s h0 g0 e (s.cntC e + s.cntZ e) 1 dL dB (baseCodes_src hs hq h2)
      (rLambda_sd hL) (rBase_sd (s := s.st) hB (le_trans hs.small (by decide))) G col mk last hlast
      hno bad hp H

/-- A stage made by hand, to show the hypotheses on sizes and radius met: main code 2^23 positions
and 4,194,565 coefficients, mask code 2^17 positions and 8,453 coefficients. Its numbers of row
variables (two, one of them a mask variable) and of positions drawn (261) are made up, and
`mixed_sizes` reads none of them. Having row variables, it is no stage for `base_holds_src`. No
theorem ties these numbers to a file's plan. -/
def mixedSg : Sg := ⟨⟨23, 4194304, 261⟩, ⟨17, 8192, 261⟩, 1, 1, 261⟩

/-- The hypotheses are met together, with the two codes on different footings: at `mixedSg` the
radius 2,097,021 is below half the stage's distance, the count for a main row is 2^23 (3 e is not
below the main code's distance) and the count for a mask row is 2,097,022 (3 e is below the repeated
mask code's). -/
theorem mixed_sizes :
    mixedSg.Sized ∧ mixedSg.Pos ∧ 2 * 2097021 < mixedSg.d ∧ mixedSg.cntC 2097021 = 2 ^ 23 ∧
      mixedSg.cntZ 2097021 = 2097022 :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide,
    by decide⟩

end OnBytes.Slice
