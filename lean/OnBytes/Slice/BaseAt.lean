-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BaseAt.lean: the hypotheses of the block that takes off the base case are met within a
third of the distance, and at the format's own two rounds.

OnBytes/Slice/Base.lean takes the last two rounds of the written proximity test off under two kinds
of hypotheses: numbers on the last stage's codes (`BaseCodes`) and what the two rounds send and draw
(`SendsDraws`). This file meets both. For a stage whose codes fit their length
(OnBytes/Slice/Numbers.lean: `Sg.Sized`) and a radius e with 3 e below the stage's distance, a line
has at most e + 1 exceptional points and a list of pairs at most one member. The format's rounds
`rLambda` and `rBase` (Fmt/M1Plan.lean) send and draw what the block asks
(OnBytes/Slice/RoundsOf.lean). The head of OnBytes/Slice/Base.lean explains the words written,
format, taken off and has lost.

Main theorems: `baseCodes_third`, `base_block_at`, `base_holds` (the same in the form in
which the blocks are joined, OnBytes/Slice/BlockHolds.lean).

Not claimed. Nothing at a third of the distance or beyond.
-/
import OnBytes.Slice.Base
import OnBytes.Slice.Numbers
import OnBytes.Slice.BlockHolds

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The numbers of the base case within a third of the distance. -/
theorem baseCodes_third {s : Sg} (h : s.Sized) {e : ℕ} (h3 : 3 * e < s.d) :
    BaseCodes s e (e + 1) 1 :=
  ⟨(Sg.fit_cIn h).laws, Sg.mca_cIn h h3, Sg.list_pairs h (by omega)⟩

/-- The base case is taken off, at the format's two rounds and within a third of the distance:
`base_block` with its hypotheses on codes and rounds met. -/
theorem base_block_at (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hs : s.Sized) (e : ℕ)
    (h3 : 3 * e < s.d) (dL dB : PQ.RD) (work tree : ℕ) (hL : IsRd dL Fmt.M1.rLambda)
    (hB : IsRd dB (Fmt.M1.rBase work s.st tree))
    (G : Fmt.M1.GRow) (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E)
    (last : Tr (PQ.uL (ckP .two) [dL, dB]) →
      ℕ → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E))
    (hlast : ∀ τ x q, last τ x = some q → Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
      Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2)
    (hno : ∀ w, ¬ s.RIn e (stmIn s G, wordIn s col) w)
    (bad : Tr (PQ.uL (ckP .two) [dL, dB]) → Prop)
    (hp : ∀ τ, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad τ)
    (H : ∀ (τ : Tr (PQ.uL (ckP .two) [dL, dB])) tauS lam ps rs1 v,
      Fmt.M1.nextN 1 1 0 (rsOf _ τ) = some (⟨[tauS], [lam], ps⟩, rs1) →
      Fmt.M1.nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, []) →
      Fmt.M1.baseOK .two s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
        ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
        (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss (last τ) = false → bad τ) :
    Doomed _ (baseErr s e (e + 1) 1 dL dB) bad :=
  base_block s h0 g0 e (e + 1) 1 dL dB (baseCodes_third hs h3) (rLambda_sd hL)
    (rBase_sd (s := s.st) hB (le_trans hs.small (by decide))) G col mk last hlast hno bad hp H

/-- The same, in the form in which the blocks of the proximity test are joined. -/
theorem base_holds (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hs : s.Sized) (e : ℕ)
    (h3 : 3 * e < s.d) (dL dB : PQ.RD) (work tree : ℕ) (hL : IsRd dL Fmt.M1.rLambda)
    (hB : IsRd dB (Fmt.M1.rBase work s.st tree)) :
    BaseHolds s e dL dB (baseErr s e (e + 1) 1 dL dB) :=
  fun G col mk last hlast hno bad hp H =>
    base_block_at s h0 g0 hs e h3 dL dB work tree hL hB G col mk last hlast hno bad hp H

end OnBytes.Slice

#print axioms OnBytes.Slice.baseCodes_third
#print axioms OnBytes.Slice.base_block_at
#print axioms OnBytes.Slice.base_holds
