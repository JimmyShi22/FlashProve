-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/RowsFitStatement.lean: UNDER THE LIBRARY's HEAD THE MATRIX's ROWS FIT THE
BITS THAT NAME A ROW: WITH NO STATE AND NO ROW READ: A STATEMENT ALONE: a definition of a
proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's
statement.

  `RowsFitAtHead`   the head: `OnBytes.Flat.numsFull.rows ≤ 2 ^ h.𝔇.d1.lin.kRow`

Why. `RowsFitAtFull` (NumsAtFullStatement.lean of this folder) has this end from a row that is read
at a state. The law on the merge's exchange at a thread of the honest side takes it as a field with
no state.

Limits. A fact on public numbers alone. The full size alone. The head is a premise here, at the
earlier hash. Nothing on any property.
-/
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def RowsFitAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x),
    OnBytes.Flat.numsFull.rows ≤ 2 ^ h.𝔇.d1.lin.kRow

end Johnson.Desc.First.ForkMerge.Exchange

#print axioms Johnson.Desc.First.ForkMerge.Exchange.RowsFitAtHead
