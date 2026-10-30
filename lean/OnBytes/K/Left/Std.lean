-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Std.lean: the test `Params.stdEntry` on the three public files
(OnBytes/Params/Std.lean) says yes, if the parameter file says the ground's lines and the three
files are not too long.

The test has two clauses. On the lines: the reader of a parameter file returns the size's lines:
this is `G.SaysLines pol` (OnBytes/Tie/EntryGround.lean) where the size's lines are the ground's. On
the bytes: what is hashed for the configuration's digest has at most 2^32 - 144 bytes: these are 32
bytes and the three files.

Main names:
  `configBytes_size`: the number of bytes that are hashed.
  `std_of_sizes`: the test's yes. `std_of_limits`: the same from the shell's limits on its reads.
  `record_std`, `small_record_std`: at the two grounds with a record and their sizes.

Limits: that the three files are so short is a premise: the shell's reads are capped, but no
statement on a call is used here. That a parameter file says the ground's lines is a premise too.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Rules23Laws
import OnBytes.Params.Std
import OnBytes.Shell.Ask
import OnBytes.Tie.EntryGrounds
import OnBytes.Tie.EntryRecord

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (EntryGround)

/-- What is hashed for the configuration's digest: 32 bytes and the three files. -/
theorem configBytes_size (pol lay kl : ByteArray) :
    (Fmt.configBytes [pol, lay, kl]).size = 32 + pol.size + lay.size + kl.size := by
  unfold Fmt.configBytes Fmt.cat Fmt.text
  simp only [List.map, List.foldl, ByteArray.size_append, Fmt.size_u64n, ByteArray.size_empty]
  omega

/-- The test's yes. -/
theorem std_of_sizes (G : EntryGround) (zS : Params.StdSize) (hz : zS.lines = G.lines)
    {pol lay kl : ByteArray} (hL : G.SaysLines pol)
    (hb : pol.size + lay.size + kl.size ≤ 2 ^ 32 - 176) :
    Params.stdEntry zS ⟨pol, lay, kl⟩ = true := by
  unfold Params.stdEntry Params.stdLines Params.stdBytes
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [hz]
    exact hL
  · rw [configBytes_size]
    omega

/-- The same from the shell's limits on its reads. -/
theorem std_of_limits (G : EntryGround) (zS : Params.StdSize) (hz : zS.lines = G.lines)
    {pol lay kl : ByteArray} (hL : G.SaysLines pol) (hp : pol.size ≤ Shell.textLimit)
    (hl : lay.size ≤ Shell.textLimit) (hk : kl.size ≤ Shell.fileLimit) :
    Params.stdEntry zS ⟨pol, lay, kl⟩ = true := by
  refine std_of_sizes G zS hz hL ?_
  have e1 : Shell.textLimit = 1048576 := rfl
  have e2 : Shell.fileLimit = 268435456 := rfl
  omega

/-- At the full-size ground with a record. -/
theorem record_std {pol lay kl : ByteArray} (hL : OnBytes.Tie.recordGround.SaysLines pol)
    (hb : pol.size + lay.size + kl.size ≤ 2 ^ 32 - 176) :
    Params.stdEntry Params.stdFull ⟨pol, lay, kl⟩ = true :=
  std_of_sizes _ _ rfl hL hb

/-- At the small ground with a record. -/
theorem small_record_std {pol lay kl : ByteArray}
    (hL : OnBytes.Tie.smallRecordGround.SaysLines pol)
    (hb : pol.size + lay.size + kl.size ≤ 2 ^ 32 - 176) :
    Params.stdEntry Params.stdSmall ⟨pol, lay, kl⟩ = true :=
  std_of_sizes _ _ rfl hL hb

end OnBytes.K.Left
