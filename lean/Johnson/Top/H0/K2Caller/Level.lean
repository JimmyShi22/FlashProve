-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Level.lean: the level at the written places of the code switch: at each of
the 5 and the 25 written records each of the block's two errors, as a share, is at most 2 ^ work / 2
^ target.

The general theorem stands in LevelDef.lean, the evaluations in LevelSmall.lean and LevelFull.lean;
this file joins them, so that whoever imports it has all their names (SwRow.levelOK, bitsAt,
Letters.level, SwRow.works; small_level_ok, full_level_ok, small_works, full_works).
  level_small, level_full: Letters.level at each written record
Limits: those of LevelDef.lean, Row.lean and LitRows.lean. Nothing on soundness of the protocol. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Lit
import Johnson.Top.H0.K2Caller.LevelSmall
import Johnson.Top.H0.K2Caller.LevelFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Cb Iop IOR
open scoped ENNReal

/-- **At the 5 switches of the small example.** -/
theorem level_small (r : SwRow) (hr : r ∈ tableSmallLit) (X : Letters r (r.ok_says
    (List.all_eq_true.1 tableSmallLit_ok r hr))) :
    Err.BelowG (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller) (ENNReal.ofReal ((2 : ℝ) ^
        r.set.target)⁻¹) :=
  Letters.level (List.all_eq_true.1 tableSmallLit_ok r hr) (List.all_eq_true.1 small_level_ok r hr)
      X

/-- **At the 25 switches of the full example.** -/
theorem level_full (r : SwRow) (hr : r ∈ tableFullLit) (X : Letters r (r.ok_says (List.all_eq_true.1
    tableFullLit_ok r hr))) :
    Err.BelowG (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller) (ENNReal.ofReal ((2 : ℝ) ^
        r.set.target)⁻¹) :=
  Letters.level (List.all_eq_true.1 tableFullLit_ok r hr) (List.all_eq_true.1 full_level_ok r hr) X

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.Letters.level
#print axioms VerifiableInference.Desc.First.K2Caller.small_level_ok
#print axioms VerifiableInference.Desc.First.K2Caller.full_level_ok
#print axioms VerifiableInference.Desc.First.K2Caller.small_works
#print axioms VerifiableInference.Desc.First.K2Caller.full_works
#print axioms VerifiableInference.Desc.First.K2Caller.level_small
#print axioms VerifiableInference.Desc.First.K2Caller.level_full
