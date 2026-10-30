-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDescOk.lean: at any ground and every digest of 32 bytes the description
`entryXD G c` passes the second compiler's test of descriptions (`TypedOracleCompiler.Run.PQ.ok`), if at the
ground's own digest its base is in order at an empty statement.

At a digest that has not 32 bytes the test fails (`Fmt.Spec.ok` holds the clause `S.cfg.size ==
32`): `entryXD_not_ok`. So "∀ c" without the guard cannot be met.

The file serves `HomeData.ok` (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) and the run's `ownES`
(OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryDescWire

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Tie (EntryGround linkAtCfg)

/-- At every digest of 32 bytes the description passes the test. -/
theorem entryXD_ok (G : EntryGround)
    (hb0 : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true) (c : ByteArray)
    (hc : c.size = 32) : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true := by
  rw [entryXD_eq_xdOf]
  exact okT_of_within _ _ (entryXD_within G hb0 c hc)

/-- At a digest that has not 32 bytes it fails. -/
theorem entryXD_not_ok (G : EntryGround) (c : ByteArray) (hc : c.size ≠ 32) :
    TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = false := by
  have h : (entryXD G c).base.ok = false := by
    unfold Fmt.Spec.ok
    have e : ((entryXD G c).base.cfg.size == 32) = false := by
      rw [entryXD_cfg]
      exact beq_false_of_ne hc
    simp [e]
  unfold TypedOracleCompiler.Run.PQ.ok
  simp [h]

theorem record_ok (c : ByteArray) (hc : c.size = 32) :
    TypedOracleCompiler.Run.PQ.ok (entryXD OnBytes.Tie.recordGround c).base = true :=
  entryXD_ok OnBytes.Tie.recordGround OnBytes.Tie.okRL c hc

theorem small_record_ok (c : ByteArray) (hc : c.size = 32) :
    TypedOracleCompiler.Run.PQ.ok (entryXD OnBytes.Tie.smallRecordGround c).base = true :=
  entryXD_ok OnBytes.Tie.smallRecordGround OnBytes.Tie.okSL c hc

end TypedOracleCompiler.Slice
