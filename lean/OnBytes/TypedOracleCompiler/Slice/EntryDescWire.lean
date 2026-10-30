-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDescWire.lean: the wiring of `Link0` at the description `entryXD G c` is
lawful, at any ground and every digest of 32 bytes.

It follows from the ground's own fact "within the limits" and one more: the description's base is in
order at an empty statement. No new evaluation: by `workT_of_within` and `okxT_of_within`
(OnBytes/TypedOracleCompiler/Slice/PartEntryFull.lean) and `wq0_okg` (OnBytes/TypedOracleCompiler/Slice/EntryX.lean). At both
grounds the one more fact is `okRL` or `okSL` (OnBytes/Tie/EntryRecord.lean,
OnBytes/Tie/EntryGrounds.lean: by the kernel).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Slice.PartEntryFull

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Tie (EntryGround linkAtCfg withinX)

/-- The description `entryXD G c` is `TypedOracleCompiler.Run.PQ.xdOf` of the port's description at an empty
statement. -/
theorem entryXD_eq_xdOf (G : EntryGround) (c : ByteArray) :
    entryXD G c = TypedOracleCompiler.Run.PQ.xdOf
      (OnBytes.Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty)
      (fun r0 r1 => OnBytes.Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩) := rfl

/-- At every digest of 32 bytes the port's description at an empty statement is within the limits
(`Tie.withinX`), if at the ground's own digest its base is in order. -/
theorem entryXD_within (G : EntryGround)
    (hb0 : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true) (c : ByteArray)
    (hc : c.size = 32) :
    withinX (OnBytes.Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true := by
  refine G.within_at c hc ByteArray.empty ?_
  rw [OnBytes.Tie.baseOk_linkAtCfg G.q c G.rs ByteArray.empty (hc.trans G.cfg32.symm) G.spelled]
  exact hb0

/-- The wiring of `Link0` at the description `entryXD G c` is lawful, at every digest of 32
bytes. -/
theorem entryXD_wiring (G : EntryGround)
    (hb0 : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true) (c : ByteArray)
    (hc : c.size = 32) : (wq0 (entryXD G c) fun _ => true).OKG := by
  have hw := entryXD_within G hb0 c hc
  rw [entryXD_eq_xdOf]
  exact wq0_okg _ _ (workT_of_within _ _ hw) (okxT_of_within _ _ hw)

/-- At the full size. -/
theorem record_wiring (c : ByteArray) (hc : c.size = 32) :
    (wq0 (entryXD OnBytes.Tie.recordGround c) fun _ => true).OKG :=
  entryXD_wiring OnBytes.Tie.recordGround OnBytes.Tie.okRL c hc

/-- At the small example (target_small_f2_roomy's lines). -/
theorem small_record_wiring (c : ByteArray) (hc : c.size = 32) :
    (wq0 (entryXD OnBytes.Tie.smallRecordGround c) fun _ => true).OKG :=
  entryXD_wiring OnBytes.Tie.smallRecordGround OnBytes.Tie.okSL c hc

end TypedOracleCompiler.Slice
