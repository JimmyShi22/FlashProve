-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Deco.lean: decorated rounds: every symbol of every prover oracle carries a second component, a
value in one fixed type D. (Words of this library: lean/GLOSSARY.md.)

`Round.deco`: a round with the same plain part, challenge and positions, in which the symbol at a
position p is a pair (the symbol of the round at p, a value in D). `Round.IsPoint.deco`: a round
whose oracle is a string keeps that form.

Limits: nothing is said on soundness. No protocol is named here.
-/
import Iop.ShapeKit
import Iop.Rbr
import Iop.InteractiveOracleProof

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Iop
open Prob

variable (D : Type) [Zero D]

/-- A round whose symbols carry a value in D. -/
def Round.deco (r : Round) : Round where
  Orc := r.Orc × (r.Pos → D)
  Pos := r.Pos
  Sym := fun p => r.Sym p × D
  rd := fun o p => (r.rd o.1 p, o.2 p)
  Plain := r.Plain
  Chal := r.Chal
  dOrc := (r.dOrc, fun _ => 0)
  dPlain := r.dPlain
  finChalT := r.finChalT
  neChal := r.neChal

def Round.IsPoint.deco {r : Round} (h : r.IsPoint) : (r.deco D).IsPoint where
  finPos := h.finPos
  decPos := h.decPos
  ofSyms := fun f => (h.ofSyms fun p => (f p).1, fun p => (f p).2)
  rd_ofSyms := fun f p => by
    show (r.rd (h.ofSyms fun p => (f p).1) p, (f p).2) = f p
    rw [h.rd_ofSyms]
    rfl
  ofSyms_rd := fun o => by
    show (h.ofSyms (fun p => r.rd o.1 p), fun p => o.2 p) = o
    rw [h.ofSyms_rd]
    rfl
  zero := fun p => (h.zero p, 0)

end Iop
