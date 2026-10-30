-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/TestScd.lean: tests on Cb/Pv/Att/Scd.lean and Cb/Pv/Att/ScdProofs.lean.

The walk of Cb/G6/WalkCmd.lean is run over the statement, the block, its errors, its joints, the
parameters, and the premises of three theorems: each line is an error unless it comes out as it
says. The walk goes by names: it looks for a notion of an honest prover. The degrees of the rounds
are evaluated at two sizes.

Limits: the walk does not read proofs, and it sees only the names on its list.

-/
import Cb.Pv.Att.ScdProofs
import Cb.G6.WalkCmd

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Cb.Pv.Att

#tw_walk Cb.Pv.Att.H_scd clean
#tw_walk Cb.Pv.Att.scdR clean
#tw_walk Cb.Pv.Att.scdE clean
#tw_walk Cb.Pv.Att.scdIn clean
#tw_walk Cb.Pv.Att.scdOut clean
#tw_walk Cb.Pv.Att.Scd clean
#tw_premises Cb.Pv.Att.scd_know_at clean
#tw_premises Cb.Pv.Att.scd_knowAt clean
#tw_premises Cb.Pv.Att.scd_knowAt_of clean

-- the degrees of the rounds at two sizes
example : List.ofFn (ScdSize.deg ⟨2, 1, 1, 1⟩) = [2, 2, 4, 3, 3] := by decide
example : List.ofFn (ScdSize.deg ⟨3, 2, 2, 2⟩) = [2, 2, 2, 5, 5, 4, 4, 4] := by decide
