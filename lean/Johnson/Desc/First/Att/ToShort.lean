-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ToShort.lean: from what K5 hands on (Att/K5Heard.lean) to Att/Hear.lean's record, which
holds OnBytes/Model's record of a sumcheck. Pure. A seat's tool; no part of the kind.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5AttentionKind
import Johnson.Desc.First.Att.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open VerifiableInference.Desc.Part

/-- How a variable is summed, as OnBytes/Model's record. -/
def weightOf : MaskedSum.Var → OnBytes.Psc.Weight
  | .plain d => .plain d
  | .point z d => .equality z d

/-- A sumcheck's record. -/
def sumOf (h : MaskedSum.Heard) : Short.Sum :=
  { r := h.r.dropLast.toArray, ends := h.sEnd
    p := { start := h.start, target := h.target, eps := h.eps, claim := h.claim, first := h.first,
           vars := (h.vars.map weightOf).toArray, r := h.r.toArray, ended := true, rowMade := true, started := true } }

def toShort (h : Heard) : Short.Heard :=
  { remainders := h.remainders, scores := h.scores.map fun u => (u.1, sumOf u.2), five := h.five, bits := h.bits,
    two := h.two, division := sumOf h.division, gam := h.gam, values := h.values, below := sumOf h.below,
    on := sumOf h.on, point := h.point, maxima := h.maxima, om := h.om, atIndex := sumOf h.atIndex, om' := h.om',
    key := sumOf h.key, om'' := h.om'', cells := sumOf h.cells }

end VerifiableInference.Desc.First.Att.P
