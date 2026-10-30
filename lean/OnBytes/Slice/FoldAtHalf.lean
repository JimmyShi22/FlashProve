-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FoldAtHalf.lean: the hypotheses of the block that takes off a fold are met within a
half of the distance.

OnBytes/Slice/FoldAt.lean meets the hypotheses of the block of OnBytes/Slice/FoldPeel.lean for a
radius e with 3 e below the distance of the stage's codes. This file does so for a radius e with 2 e
below it. Here too the lists have at most one member. A halving has at most as many exceptional
points as the stage's main code has positions, for the mask rows too, also where the mask code is
shorter (OnBytes/Slice/NumbersHalf.lean). Through that file this one rests on the library's
Code/Half.lean.

Main theorems: `foldNums_half`, `fold_block_half`, `fold_holds_half`.

Not claimed. Nothing at half the distance or beyond. That these counts are the planner's (the head
of OnBytes/Slice/NumbersHalf.lean says where they are above it).
-/
import OnBytes.Slice.FoldAt
import OnBytes.Slice.NumbersHalf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The numbers of a fold within a half of the distance. -/
theorem foldNums_half {s : Sg} (hs : s.Sized) (hq : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    (s.par 0).ErrOK e (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => 2 ^ s.C.a)
      (fun _ => 2 ^ s.C.a) :=
  Sg.errOK_half hs hq h2 (s.par 0) rfl rfl rfl

/-- A fold is taken off, at the format's rounds and within a half of the distance. -/
theorem fold_block_half (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
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
    Doomed _ (Err.app (foldErr s dE dT (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => 2 ^ s.C.a)
      (fun _ => 2 ^ s.C.a)) εt) bad :=
  fold_block s s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_half hs hq h2) dE dT
    (foldRounds_of hdE hdT) t εt G col hno bad hp H

/-- The block within a half of the distance, in the form in which the blocks are joined. -/
theorem fold_holds_half (s : Sg) (hs : s.Sized) (hq : s.Pos) (e : ℕ) (h2 : 2 * e < s.d)
    (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds s e dE dT (foldErr s dE dT (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => 2 ^ s.C.a)
      (fun _ => 2 ^ s.C.a)) :=
  fun t εt G col hno bad hp H =>
    fold_block_half s hs hq e h2 dE dT na nb hdE hdT t εt G col hno bad hp H

end OnBytes.Slice

#print axioms OnBytes.Slice.foldNums_half
#print axioms OnBytes.Slice.fold_block_half
#print axioms OnBytes.Slice.fold_holds_half
