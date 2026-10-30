-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefToyNoEv.lean: at the toy reference request's range check (`RefToy.p`) the window
event is impossible: the request's one hidden withheld set is empty at the toys, in this sense:
`rngEv RefToy.p Y = ∅` for every `Y : RefToy.p.Cells`.

One statement (`Cb.Spec.ldRng_toyNoEv`) and its proof.
The window event (`rngEv`, Cb/Ld/LdRng.lean) of a matrix Y of integer cells is the set of verifier
messages at which some combination of a row of Y with the drawn coefficients in {-1, 0, 1} is
outside [-D, D) (`Event`, Cb/Gen/RngAlg.lean), if all entries of Y are below B in absolute value;
otherwise it is empty. `rngDrawH` has `Hid w _ := rngEv p (r.yz (A₀.core w))` (Cb/Ld/LdRng.lean).

Main names:
  `Spec.ldRng_toyNoEv`: rngEv RefToy.p Y = ∅ for every matrix Y of cells (Cb/Ld/LdRng.lean: the
    event; Cb/Req1/LdSegRefToy.lean: the toy's parameters: B = 2, D = 2, one column, one
    combination).

Why: good for non-vacuity: "exact" and "fresh" at the toys (`RefToy.p`) are not emptied by a
withheld set that swallows everything.

Limits: executions that fail are not exercised, even in this library's own form: at the toy
parameters (`RefToy.p`) the one event at which the honest prover can give up is
empty, so none of the guards that stood at these parameters has a mask pending across a link that
can withhold (by reading).


By reading, every other honest side of the request's blocks has an empty hidden set, and RefToy.p
is the only record of a range check's parameters in the toys' files of Cb/Req1/.
The cure, not done: a toy whose window can be left.


Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefToy
import Cb.Ld.LdRng

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Rng

/-- States: the window event is impossible at the toy. -/
def Spec.ldRng_toyNoEv : Prop := ∀ Y : RefToy.p.Cells, rngEv RefToy.p Y = ∅

theorem ldRng_toyNoEv : Spec.ldRng_toyNoEv := by
  intro Y
  ext ρ
  constructor
  · rintro ⟨hY, ⟨x, hx⟩⟩
    apply hx
    have h := hY x.1 ()
    have hB : |Y x.1 ()| < 2 := h
    have e : comb (Y x.1) ((show RefToy.p.Chal × Unit from ρ).1 x.2) =
        (((show RefToy.p.Chal × Unit from ρ).1 x.2) ()).val * Y x.1 () := by
      unfold comb
      exact Fintype.sum_unique _
    have hD : RefToy.p.D = 2 := rfl
    rw [e, hD]
    rw [abs_lt] at hB
    rcases h3 : ((show RefToy.p.Chal × Unit from ρ).1 x.2) () with ⟨_ | _, _ | _⟩
      <;> simp only [Coef.val] <;> constructor <;> omega
  · intro h
    exact h.elim

end Cb
