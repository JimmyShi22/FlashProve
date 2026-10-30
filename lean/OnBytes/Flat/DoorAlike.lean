-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/DoorAlike.lean: two equations in which a link's sub-proof ends, alike but for the
values that the request reaches.

A link's check hands the chain one equation (`ReqEquation`, OnBytes/Iop/ReqRows.lean). At two
requests the head's two equations differ in the weights that are written out on the arrays' columns
and in the public target, and in nothing else. This file has the relations alone.

Main definitions: `TermAlike` (two terms: all is equal but the written-out weights on the columns,
of which there are as many), `EqnAlike` (two equations: terms alike, member by member; the
coefficients on the masks equal; the targets free), `AddTermsAlike` (what is asked of
`ReqRows.addTerms`: at two lists of terms that are alike and two rows of one kind it returns
nothing both times, or rows of one kind).

Not claimed: `AddTermsAlike`. For proofs only; no module of the program imports this file.

-/
import OnBytes.Flat.LinksFreeLayer
import OnBytes.Iop.ReqRows

set_option autoImplicit false

namespace OnBytes.Flat

/-- Two terms of an equation: all is equal but the weights on the columns, which are written out in
both, as many. -/
def TermAlike (t t' : ReqTerm) : Prop :=
  t' = { t with onColumns := t'.onColumns } ∧
    ∃ L L' : Array E, t.onColumns = { values := some L } ∧ t'.onColumns = { values := some L' } ∧
      L.size = L'.size

/-- Two equations: the terms are alike, the coefficients on the masks are equal. -/
def EqnAlike (e e' : ReqEquation) : Prop :=
  All2 TermAlike e.terms.toList e'.terms.toList ∧ e.onMasks = e'.onMasks

/-- What is asked of `ReqRows.addTerms`. -/
def AddTermsAlike : Prop :=
  ∀ (R : ReqRows) (f : ReqFrame) (S : Statement) (ts ts' : List ReqTerm) (row row' : Row),
    All2 TermAlike ts ts' → row.kind = row'.kind →
    OptRel (fun r r' => r.kind = r'.kind) (R.addTerms f S ts row) (R.addTerms f S ts' row')

end OnBytes.Flat
