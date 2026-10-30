-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/LookO.lean: what the lookup's kind hands kind K5 for its tables and for its
test on the padding, made of the lookup's heard record and shape by the lookup's own plain functions
(Johnson/Desc/First/Look/ShapeOwn.lean): no function of OnBytes/Model that can refuse is called.

Main names:
  `lookOfO lmb g`: the record that Att/TablesP.lean takes: the lookup's point; whether the planes'
    matrix of 2^lmb rows has a lawful number of row bits (Look.planesOk); the weights under which
    the planes are read at the lookup's two points (Look.phiBOwn; the empty array for nothing) and
    under which the counts are summed.
  `padOfO h`: the record that Att/RunsP.lean takes: the planned counts of padding keys a tree, the
    counts to begin from, and the counting of a run of padding places (Look.pubRunOwn).
That the two records are those of Att/SeatC.lean (lookOf, padOf) is Att/LookOAgrees.lean's.
Still called of OnBytes/Model: Forest.phiP, Forest.noPub and the two records' fields, and, through
Look.phiBOwn, the table of equality weights eqTab: none can refuse.
Limits: that the three vectors are the right ones for the lookup's claims on the planes is the
lookup's kind's to say; it is not shown in this file or in what it imports.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.RunsP
import Johnson.Desc.First.Look.ShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

def lookOfO (lmb : Nat) (g : Forest.Heard) : LookIn :=
  { zx := g.zx, planesOk := Look.planesOk g.shape lmb, phiB0 := (Look.phiBOwn g lmb 0).getD #[]
    phiB1 := (Look.phiBOwn g lmb 1).getD #[], phiP := Forest.phiP lmb }

def padOfO (h : Forest.Shape) : Runs.PadIn :=
  { pub := h.pub, noPub := Forest.noPub h, pubRun := Look.pubRunOwn h }

end VerifiableInference.Desc.First.Att.P
