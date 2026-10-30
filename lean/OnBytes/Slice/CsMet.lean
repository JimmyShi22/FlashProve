-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsMet.lean: what the block on a code switch asks of sizes and rounds, from the format.

The theorem on the two rounds of a code switch (OnBytes/Slice/BlockCs.lean) has two hypotheses on
public data: the sizes of the old and the new stage fit (`CsFit`, OnBytes/Slice/CsData.lean), and
the two written rounds send and draw what a switch sends and draws (`CsRounds`). This file derives
the first from the format's own test of a switch's sizes and the second from the format's own two
rounds, and shows the first at the two switches of the small test configuration. The block's other
hypotheses are not treated here.

Main theorems.
 `csFit_of`       the sizes fit if the format's test `csFits` (Fmt/M1Cs.lean) says so, the lengths
                  of the new rows' messages are powers of two, and the old mask code is not longer
                  than the old main code.
 `csRounds_of`    the rounds are right if they are the format's rounds `rSeed` of the new stage and
                  `rCs` of the old one, and the old tree has at most 2^64 positions.
 `toy_fit12`, `toy_fit23`   the sizes fit, for the switch from the first
                  stage to the second and from the second to the third.

Not claimed. Nothing on the block's other hypotheses: the laws of the old code, the list of the new
one, and what is lost in the rounds that follow.
-/
import OnBytes.Slice.BlockCs
import OnBytes.Slice.RoundsOf
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry
import OnBytes.Slice.ToySg

set_option autoImplicit false

namespace OnBytes.Slice
open Run

/-- The sizes fit, from the format's own test of a switch's sizes. -/
theorem csFit_of {s s' : Sg} (h : Fmt.M1.csFits s.st s'.st = true)
    (hC : s'.C.l = 2 ^ Fmt.M1.lg s'.C.l) (hZ : s'.Z.l = 2 ^ Fmt.M1.lg s'.Z.l)
    (ha : s.Z.a ≤ s.C.a) : CsFit s s' := by
  unfold Fmt.M1.csFits at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, hC, hZ, ha⟩

/-- The rounds are a switch's, if they are the format's own two rounds. -/
theorem csRounds_of {s s' : Sg} {dS dC : PQ.RD} {work tree W : ℕ}
    (hS : IsRd dS (Fmt.M1.rSeed s'.st)) (hC : IsRd dC (Fmt.M1.rCs work s.st tree W))
    (ha : s.C.a ≤ 64) : CsRounds s s' dS dC :=
  ⟨rSeed_sd hS, rSeed_nz hS, rCs_sd hC ha⟩

/-- The switch from the first stage of the small test configuration to the second. -/
theorem toy_fit12 : CsFit toySg1 toySg2 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (Nat.le_refl _)

/-- The switch from the second stage to the third. -/
theorem toy_fit23 : CsFit toySg2 toySg3 :=
  csFit_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (Nat.le_refl _)

end OnBytes.Slice

#print axioms OnBytes.Slice.csFit_of
#print axioms OnBytes.Slice.csRounds_of
#print axioms OnBytes.Slice.toy_fit12
#print axioms OnBytes.Slice.toy_fit23
