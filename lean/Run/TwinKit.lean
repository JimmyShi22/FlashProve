-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TwinKit.lean: tools for protocols made as skeletons (Run/TwinDefs.lean): the annotation "local
rounds only" and a round with test bits, written so that the evaluator builds no round; each is the
library's term, by definition or, for `allLo`, by one induction.

Definitions and small theorems by `rfl` or one induction.
A skeleton of a round (`RS`) has the fields of a round (`Iop.Round`), with the instance
`Fintype Chal` behind a function of `Unit` (`finT`); `r.up` is the round. An annotation (`RAnn`,
`RoundSplits`, Iop/Batch.lean) says of each round of a batch protocol whether it is local or shared. A
round with b test bits is a round with a proof of work (`Round.grind`, Iop/Grind.lean): for b > 0
the prover sends a nonce more and the verifier b bits more; at b = 0 it is the round itself.

Why. Observed: the library's `RAnn.allLocal r` takes the round as an argument, and the evaluator
builds that argument (the list of all verifier messages with it), though the function's text reads
no data of it. So "a round in the types alone is not built" holds of some functions only (those that
the compiler inlines or frees of the argument): of each term that is handed to the twin (`verifyT`,
Run/TwinDefs.lean) a trace in `finT` tells whether it holds.

Limits: this file says nothing on wires with tests or on a protocol with tests: the library's steps
for whole shapes recurse on the shape.

Terms: lean/GLOSSARY.md.
-/
import Run.TwinDefs
import Iop.Grind

set_option autoImplicit false

namespace Run.Twin
open Iop Rom Compile Compile.Batch

/-- The annotation of a local round without a shared prover message. -/
@[reducible] def RS.lo (r : RS) : RAnn r.up where
  kind := .lo
  M0 := Unit
  Mj := r.Orc × r.Plain
  split := (Equiv.punitProd (r.Orc × r.Plain)).symm
  P0 := Unit
  Pj := r.Plain
  pl0 := fun _ => ()
  plj := fun m => m.2
  plain := (Equiv.punitProd r.Plain).symm
  own := fun _ => true

theorem lo_eq (r : RS) : r.lo = RAnn.allLocal r.up := rfl

/-- The annotation "local rounds only". -/
@[reducible] def allLo : (S : List RS) → RoundSplits (up S)
  | [] => PUnit.unit
  | r :: S => (r.lo, allLo S)

theorem allLo_eq : ∀ S : List RS, allLo S = RoundSplits.allLocal (up S)
  | [] => rfl
  | r :: S => by
      show (r.lo, allLo S) = (RAnn.allLocal r.up, RoundSplits.allLocal (up S))
      rw [allLo_eq S, lo_eq]

/-- The skeleton of the round with a nonce in W and b test bits. For b > 0 its fixed message
`dPlain` has the nonce `default`. -/
@[reducible] def RS.grind (W : Type) [Inhabited W] (r : RS) (b : ℕ) : RS where
  Orc := r.Orc
  Pos := r.Pos
  Sym := r.Sym
  rd := r.rd
  Plain := GPlain W b r.Plain
  Chal := GChal b r.Chal
  dOrc := r.dOrc
  dPlain := GPlain.mk b r.dPlain default
  finT := fun _ => (r.up.grind W b).finChal
  ne := (r.up.grind W b).neChal

theorem grind_up (W : Type) [Inhabited W] (r : RS) (b : ℕ) : (r.grind W b).up = r.up.grind W b :=
  rfl

end Run.Twin
