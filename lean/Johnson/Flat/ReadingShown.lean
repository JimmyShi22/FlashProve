-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingShown.lean: what the rounds of a view that is made of a written transcript are,
round by round, and that their elements drawn "never 0" are read as other than 0.
  `rvT_shown`: the list of rounds that a chain's view shows (`rvT (ckP .two) ds τ`) is, round by
  round along the data ds, `shownR d m c` (Johnson/Flat/ReadingBad.lean) at that round's messages m
  and c: the plain part of the prover's message, and `drawnOf` of the typed values of the verifier's
  message.
  `rvT_nz`: so, round by round: in a round that is not one of seeds the last drawNZ of the elements
  that the view shows as drawn are read by `toE` as other than 0 (`drawn_nz`,
  Johnson/Flat/ReadingNz.lean).
  `sView_rounds`: the rounds of a stage's view (`sView`, OnBytes/Maker/Stage.lean) are such a list,
  by definition. For a whole file's view (`viewOf`, OnBytes/Maker/Whole.lean) the like is
  `viewOf_rounds` (Johnson/Flat/ReadingLaw.lean).

Limits. Of an arbitrary value of the type `View` nothing is said. A round of seeds is not covered.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ReadingBad
import Johnson.Flat.ReadingNz
import OnBytes.Maker.Stage
import OnBytes.Maker.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open Iop Run OnBytes.Maker OnBytes.Slice

/-- The rounds that a chain's view shows, round by round. -/
theorem rvT_shown : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    List.Forall₂ (fun d r => ∃ m c, r = shownR d m c) ds (rvT (ckP .two) ds τ)
  | [], _ => .nil
  | _ :: ds, (m, c, τ) => .cons ⟨m, c, rfl⟩ (rvT_shown ds τ)

/-- Their elements drawn "never 0" are read as other than 0. -/
theorem rvT_nz : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    List.Forall₂ (fun d r => d.kind ≠ .seeds → ∀ j, j < d.entry.drawNZ →
      (r.drawn.elems.map toE).getD (d.entry.drawE - d.entry.drawNZ + j) 0 ≠ 0)
      ds (rvT (ckP .two) ds τ)
  | [], _ => .nil
  | d :: ds, (_, c, τ) => .cons (fun hk j hj => drawn_nz d c hk j hj) (rvT_nz ds τ)

/-- The rounds of a stage's view. -/
theorem sView_rounds (S : StageD) (y : S.Ei.Str) (τ : Tr (uLT (ckP .two) S.ds)) :
    (sView (ckP .two) S y τ).rounds = rvT (ckP .two) S.ds τ := rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.rvT_shown
#print axioms OnBytes.Flat.rvT_nz
#print axioms OnBytes.Flat.sView_rounds
