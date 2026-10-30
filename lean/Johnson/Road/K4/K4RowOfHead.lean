-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowOfHead.lean: the head gives K4's one closed test.

What it says. `k4Row_of_head`: under the head (`P5J.AtMgA` at the second hash function
`OnBytes.secondHashFunction`), `k4RowB Zp = true`. No other premise.

How. `k4Row_of_parts` (Johnson/Road/K4/K4RowOfParts.lean) at its two parts:
  the listing at the groups 0 and 1: `front_at_head` (Johnson/Road/K4/RowHead/FrontFreeK.lean): the
  makers' texts less the lines at which Lean's kernel stops, evaluated by the kernel with the eight
  free numbers, the padding counts, the scales and the rotary table as free letters; the stops fall
  by inversion, since the head hands out that the makers returned;
  the arithmetic test at the twelve groups: `Pend.rowLight_of_head_noPin`
  (Johnson/Road/K4/RowLightInScope.lean over RowLightOfHead.lean): a view of the groups' units that
  reads no free number, one fact by the kernel, and three laws of
  Johnson/Desc/Sound/K11Tests/PendAllNoPin.lean: the test reads of the table's shape `lin` its
  number of rows alone; that number is the committed table's layout's; in the goals' scope it is the
  written one. That `lin` as a whole is the written shape is not used on this route: it holds under
  the first pin, which comes off the head (`first_written_in_scope`,
  Johnson/Goal/Numbers/MadeInScope.lean; RowLightOfHead.lean). NO ENTRY TEST IS SPENT HERE.

Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/): no public files are shown here to have a head. The head in this tree stands over
fourteen entry tests; the file names none of them. Nothing on soundness.
-/
import Johnson.Road.K4.K4RowOfParts
import Johnson.Road.K4.RowLightInScope
import Johnson.Road.K4.RowHead.FrontFreeK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Total (frontB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE HEAD GIVES K4's ONE CLOSED TEST.** -/
theorem k4Row_of_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : k4RowB Zp = true :=
  k4Row_of_parts hA
    (fun g hg hp e => by
      have t : ((P5J.At.X Zp).G[g]?).any (fun hp =>
          frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo) = true :=
        List.all_eq_true.1 (front_at_head hA) g (List.mem_range.2 hg)
      rw [e] at t
      exact t)
    (fun g hg hp e => Pend.rowLight_of_head_noPin hA g hg hp e)

#print axioms OnBytes.Road.K4.k4Row_of_head

end OnBytes.Road.K4
