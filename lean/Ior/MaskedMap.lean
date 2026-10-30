-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/MaskedMap.lean: the item "masked messages" (`Honest.MM`, Ior/Masked.lean) when the witness is
re-typed.

`H.mapW fi fo` (Ior/KnowCollRulesFrame.lean) is an honest side of the same IOR (interactive oracle
reduction, Ior/Ior.lean) with another type of witnesses: the honest prover is given w', runs H on
fi w', and ends with fo w' (H's last witness).
(Say a block on messages is set over oracles: then w' holds messages with encoding randomness, and
fi w' holds the messages.)
A definition, a statement, its proof. No protocol, no code occurs here.
`H.MM D`, `MaskData`: see their rows in the head of Ior/Masked.lean and the fields' docstrings
there. The head of Ior/MaskedFrame.lean tells both.

Main names:
  `Spec.mm_mapW`: if H has the item with the parameters D (Ior/Masked.lean), `H.mapW fi fo` has it
    with `D.mapW fi`: what is read of w' is what D reads of fi w'. Same own masks, same closed
    form, same simulator. This goes with the rules of Ior/MaskedFrame.lean. The statement asks
    nothing of `fo`.
Notation: "own masks": the fields `Mk`, `put` of `MaskData`; "closed form": `msg`; "simulator":
`sim` (the fields' doc comments: Ior/Masked.lean).
Terms: lean/GLOSSARY.md.
-/
import Ior.MaskedFrame
import Ior.KnowCollRulesFrame

set_option autoImplicit false

namespace Iop
open Prob

/-- the parameters, read through fi -/
def IOR.MaskData.mapW {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wi' : Type} {R : IOR Xi Ei Xo Eo}
    (D : IOR.MaskData R Wi) (fi : Wi' → Wi) : IOR.MaskData R Wi' :=
  { Kc := D.Kc, kc := fun w => D.kc (fi w), Xp := D.Xp, pub := D.pub, Mk := D.Mk, put := D.put,
    Cl := D.Cl, msg := D.msg, sim := D.sim }

namespace Spec
open IOR

/-- States: the witness is re-typed: the item is kept, with the same simulator. -/
def mm_mapW : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo Wo' : Type)
      (H : R.Honest Wi Wo) (D : MaskData R Wi) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo'),
    H.MM D → (H.mapW fi fo).MM (D.mapW fi)

end Spec

open IOR

theorem mm_mapW : Spec.mm_mapW := fun _ _ _ _ _ _ _ _ _ H D fi _ h =>
  { noOrc := h.noOrc
    free := fun w x => h.free (fi w) x
    run := fun w x c ρ => by
      show ((Strat.map _ (H.strat (fi w) x c)).run ρ).1.plains = D.msg (D.kc (fi w)) (D.pub x) ρ
      rw [Strat.run_map]
      exact h.run (fi w) x c ρ
    stable := h.stable
    law := h.law }

end Iop
