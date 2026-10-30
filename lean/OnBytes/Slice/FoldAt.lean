-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FoldAt.lean: the hypotheses of the block that takes off a fold are met at the format's
own rounds, within a third of the distance.

OnBytes/Slice/FoldPeel.lean takes the rounds of a fold off the written proximity test under three
hypotheses: laws and a distance of the stage's codes, bounds on lists and on exceptional points, and
what the rounds send and draw. This file meets all three. The codes of a stage that fit their length
(OnBytes/Slice/Numbers.lean: `Sg.Sized`) have the laws and the distance `Sg.d`. For a radius e with
3 e below that distance all lists have at most one member and a halving has at most e + 1
exceptional points. The format's rounds `rEps` and `rTwo` (Fmt/M1Plan.lean) send and draw what the
block asks (OnBytes/Slice/RoundsOf.lean).

The code switch takes the folded words at the point that the format's function hands on. They are
the folded words at the drawn elements (`wordMid_foldStep`).

Main theorems: `foldRounds_of`, `foldNums_third`, `wordMid_foldStep`, `fold_block_third`,
`fold_holds`.
Not claimed. Nothing at a third of the distance or beyond.
-/
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.Numbers
import OnBytes.Slice.BlockHolds

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The format's rounds of a fold send and draw what the block asks. -/
theorem foldRounds_of {dE dT : PQ.RD} {na nb : String} (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb)) : FoldRounds dE dT :=
  ⟨rEps_sd hdE, rTwo_sd hdT⟩

/-- The numbers of a fold within a third of the distance. -/
theorem foldNums_third {s : Sg} (hs : s.Sized) {e : ℕ} (h3 : 3 * e < s.d) :
    (s.par 0).ErrOK e (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) :=
  errOK_third (s.par 0) s.d e (Sg.codesOK hs (by omega)) h3

/-- The folded words at the point that a fold hands on are those at the drawn elements. -/
theorem wordMid_foldStep (s : Sg) (col : ℕ → Fmt.M1.Col) (G : Fmt.M1.GRow)
    (sigma eps : Fmt.M1.E) (qs : List (Fmt.M1.E × Fmt.M1.E)) (g : List Fmt.M1.E) :
    wordMid s col (ptL _ (Fmt.M1.foldStep .two (s.h + s.g) s.h G sigma eps qs g).g) =
      wordMid s col (ptL _ g) := by
  rw [ptL_foldStep_g .two (s.h + s.g) s.h G sigma eps qs g (s.h + s.g) le_rfl]

/-- A fold is taken off, at the format's rounds and within a third of the distance. -/
theorem fold_block_third (s : Sg) (hs : s.Sized) (e : ℕ) (h3 : 3 * e < s.d)
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
    Doomed _ (Err.app (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1)
      (fun _ => e + 1)) εt) bad :=
  fold_block s s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_third hs h3) dE dT
    (foldRounds_of hdE hdT) t εt G col hno bad hp H

/-- The block within a third of the distance, in the form in which the blocks are joined. -/
theorem fold_holds (s : Sg) (hs : s.Sized) (e : ℕ) (h3 : 3 * e < s.d) (dE dT : PQ.RD)
    (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na)) (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds s e dE dT
      (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1)) :=
  fun t εt G col hno bad hp H =>
    fold_block_third s hs e h3 dE dT na nb hdE hdT t εt G col hno bad hp H

end OnBytes.Slice

#print axioms OnBytes.Slice.foldRounds_of
#print axioms OnBytes.Slice.foldNums_third
#print axioms OnBytes.Slice.wordMid_foldStep
#print axioms OnBytes.Slice.fold_block_third
#print axioms OnBytes.Slice.fold_holds
