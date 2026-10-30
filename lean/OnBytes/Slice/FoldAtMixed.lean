-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FoldAtMixed.lean: the hypotheses of the block that takes off a fold are met at a
radius below half the stage's distance and below a third of the repeated mask code's own distance,
with the smaller count for the mask rows.

OnBytes/Slice/FoldAtHalf.lean meets the hypotheses of the block of OnBytes/Slice/FoldPeel.lean for a
radius e with 2 e below the stage's distance, with the count 2^a, the number of the main code's
positions, for each of the three tables. A stage's distance is the smaller of two: the main code's
and the repeated mask code's (`Sg.d`, `Sg.dC`, `Sg.dZ`, OnBytes/Slice/Numbers.lean). Where the mask
code's is so much the larger that also 3 e is below it, a line of mask rows has at most e + 1
exceptional points (`Fit.mca` with `fit_ldRep`). This file takes that count for the two tables of
mask rows and keeps 2^a for the main rows. The radius e is one and the same for all three tables, in
positions of the main code's length.

Main theorems: `Sg.mcaThird_cZ`, `Sg.errOK_mixed`, `foldNums_mixed`, `fold_block_mixed`,
`fold_holds_mixed`.

Not claimed. Nothing at half the stage's distance or beyond, nor at a third of the repeated mask
code's distance or beyond. Nothing where 3 e is below the main code's own distance and not below the
repeated mask code's, and nothing on the base case (OnBytes/Slice/BlocksBySource.lean has both).
Where 3 e is below the stage's distance, OnBytes/Slice/FoldAt.lean has for the main rows too the
smaller count, e + 1. No theorem here is applied at a stage. That these counts are the planner's is
not shown here. An entry of `foldErr` is a sum of these counts and 2 (the first entry: 1), times the
number in the law of the format's sampler. Through OnBytes/Slice/NumbersHalf.lean this file depends
on the library's Code/Half.lean.

-/
import OnBytes.Slice.FoldAtHalf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

namespace Sg
variable {s : Sg}

/-- One mask row, under the mask code repeated to the main code's length, at a radius below a third
of the repeated code's own distance: a line through two words has at most e + 1 exceptional
points. -/
theorem mcaThird_cZ (h : s.Sized) {e : ℕ} (h3 : 3 * e < s.dZ) : s.cZ.MCAat e (e + 1) :=
  (fit_ldRep s.Z s.C.a h.short (h.short.trans h.small) h.roomZ).mca h3

/-- The numbers of a folding over the codes of a stage, at a radius e with 2 e below the stage's
distance and 3 e below the repeated mask code's: lists of one code word; at every halving at most
2^a exceptional points for the main rows, a the main code's, and at most e + 1 for each of the two
tables of mask rows. Of `Sg.Pos` only the main code's clause is read. -/
theorem errOK_mixed (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) (h3 : 3 * e < s.dZ)
    (Y : SumPar GE s.Ps) (hC : Y.C = s.cM) (hZ : Y.Z = s.cZ) (hW : Y.Zw = s.cZ) :
    Y.ErrOK e (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => e + 1) (fun _ => e + 1) := by
  have he : e < s.d := by omega
  refine errOK_of Y s.d e _ _ _ ?_ h2 ?_ ?_ ?_
  · rw [hC, hZ, hW]
    exact codesOK h he
  · rw [hC]
    exact mcaHalf_cM h hp h2
  · rw [hZ]
    exact mcaThird_cZ h h3
  · rw [hW]
    exact mcaThird_cZ h h3

end Sg

/-- The numbers of a fold at such a radius. -/
theorem foldNums_mixed {s : Sg} (hs : s.Sized) (hq : s.Pos) {e : ℕ} (h2 : 2 * e < s.d)
    (h3 : 3 * e < s.dZ) :
    (s.par 0).ErrOK e (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => e + 1) (fun _ => e + 1) :=
  Sg.errOK_mixed hs hq h2 h3 (s.par 0) rfl rfl rfl

/-- A fold is taken off, at the format's rounds, at a radius e with 2 e below the stage's distance
and 3 e below the repeated mask code's. -/
theorem fold_block_mixed (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
    (h3 : 3 * e < s.dZ) (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
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
    Doomed _ (Err.app (foldErr s dE dT (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => e + 1)
      (fun _ => e + 1)) εt) bad :=
  fold_block s s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_mixed hs hq h2 h3) dE dT
    (foldRounds_of hdE hdT) t εt G col hno bad hp H

/-- The same block, in the form in which the blocks are joined. -/
theorem fold_holds_mixed (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
    (h3 : 3 * e < s.dZ) (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds s e dE dT (foldErr s dE dT (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => e + 1)
      (fun _ => e + 1)) :=
  fun t εt G col hno bad hp H =>
    fold_block_mixed s hs hq e h2 h3 dE dT na nb hdE hdT t εt G col hno bad hp H

end OnBytes.Slice
