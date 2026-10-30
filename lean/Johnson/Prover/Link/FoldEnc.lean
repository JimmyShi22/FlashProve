-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldEnc.lean: the three folded words of a stage's code words are the code words
of the folded messages with the folded tails. General in the stage.

Main names (namespace `Johnson.Prover.Link`).
  `foldMsg s μ φ γ`   the three folded messages: the stage's main rows at the point γ; its carried
      mask rows and the fresh mask's rows at γ's first h coordinates
  `foldTl s ρ ψ γ`   the three folded tails, likewise
  `foldWords_enc`   `foldWords` (OnBytes/Slice/FoldPeel.lean) of the stage's code word of (μ, ρ) and
      the fresh mask's of (φ, ψ) is the code word of (`foldMsg`, `foldTl`) under the three folded
      rows' code

By: `enc_fold` (Cb/Ld/LdSumAcc.lean), three times; the codes' laws from the stage's sizes
(`Sg.fit_cM`, `Sg.fit_cZ`, OnBytes/Slice/Numbers.lean).

Limits. An equation between words. Asked: four inequalities on the stage's sizes (`Sg.Sized`).
Nothing on the fold's rounds or its claim. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.Numbers
import Cb.Ld.LdSumAcc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes.Slice Cb

/-- **The three folded messages.** -/
def foldMsg (s : Sg) (μ : s.cIn.J → GE) (φ : s.cFr.J → GE) (γ : Fin (s.h + s.g) → GE) :
    s.cMid.J → GE :=
  Sum.elim (foldV γ fun x => μ (.inl x))
    (Sum.elim (foldV (preP s γ) fun x => μ (.inr x)) (foldV (preP s γ) φ))

/-- **The three folded tails.** -/
def foldTl (s : Sg) (ρ : s.cIn.Q → GE) (ψ : s.cFr.Q → GE) (γ : Fin (s.h + s.g) → GE) :
    s.cMid.Q → GE :=
  Sum.elim (foldV γ fun x => ρ (.inl x))
    (Sum.elim (foldV (preP s γ) fun x => ρ (.inr x)) (foldV (preP s γ) ψ))

/-- **The fold of code words is the code word of the folds.** -/
theorem foldWords_enc (s : Sg) (hs : s.Sized) (μ : s.cIn.J → GE) (ρ : s.cIn.Q → GE)
    (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE) (γ : Fin (s.h + s.g) → GE) :
    foldWords s (s.cIn.enc μ ρ) (s.cFr.enc φ ψ) γ =
      s.cMid.enc (foldMsg s μ φ γ) (foldTl s ρ ψ γ) := by
  have e1 := enc_fold s.cM (Sg.fit_cM hs).laws γ (fun x => μ (.inl x)) (fun x => ρ (.inl x))
  have e2 := enc_fold s.cZ (Sg.fit_cZ hs).laws (preP s γ) (fun x => μ (.inr x))
    (fun x => ρ (.inr x))
  have e3 := enc_fold s.cZ (Sg.fit_cZ hs).laws (preP s γ) φ ψ
  funext p
  rcases p with p | p | p
  · exact congrFun e1 p
  · exact congrFun e2 p
  · exact congrFun e3 p

end Johnson.Prover.Link
