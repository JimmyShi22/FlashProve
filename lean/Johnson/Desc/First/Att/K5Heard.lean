-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Heard.lean: what the kind K5, an attention segment's own rounds, hands on:
one record, in a file of its own, so that the first chain's state (Johnson/Desc/First/State.lean)
can hold it without importing the kind's text or Johnson/Desc/Block.lean.

The fields stand in the order of the hearing. A field of type Nat is the number, in the sub-proof's
ledger, of the first of the scalars named. A field of type Array E holds drawn elements: a point's
coordinates, or the powers of one batching element from power 0 on. A field of the part's type
MaskedSum.Heard is what the part "the masked sumcheck" hands back of one sumcheck.

The fields (lt, lgk, NP: numbers of the place):
  remainders      for each remainder unit: its 3 scalars
  scores          for each softmax-table unit (query times key): its 7 scalars; its sumcheck
  five, bits, two, division
                  5, lt and 2 scalars; the sumcheck "denominator times output"
  gam, values, below, on
                  two powers of a batching element; 2 scalars; the value product's two sumchecks:
                  below the diagonal, on it
  point           the 2 lgk + 2 lt + 4 coordinates drawn in front of the three sumchecks that follow
  maxima, om, atIndex
                  NP scalars; NP powers of a batching element; the sumcheck "the score at the index"
  om', key        NP powers of a second; the sumcheck "the key at the index"
  om'', cells     NP powers of a third; the sumcheck "the index's cells are bits"

It imports the part's file alone (Johnson/Desc/Part/MaskedSum4.lean).

A definition; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open VerifiableInference.Desc.Part

/-- What was heard. A field of type Nat: the number of the first of the scalars named. -/
structure Heard where
  remainders : Array Nat
  scores : Array (Nat × MaskedSum.Heard)
  five : Nat
  bits : Nat
  two : Nat
  division : MaskedSum.Heard
  gam : Array E
  values : Nat
  below : MaskedSum.Heard
  on : MaskedSum.Heard
  point : Array E
  maxima : Nat
  om : Array E
  atIndex : MaskedSum.Heard
  om' : Array E
  key : MaskedSum.Heard
  om'' : Array E
  cells : MaskedSum.Heard

end VerifiableInference.Desc.First.Att.P
