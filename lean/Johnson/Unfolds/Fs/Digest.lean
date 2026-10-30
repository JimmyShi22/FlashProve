-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Fs/Digest.lean: **the digest of the verifier's table FS, at the stored example's
numbers (routed experts, the gate's clamp), is 32 written bytes**: `fs_digest`: `secondHashFunction 72` of the
bytes that `tableHeld` and `tableHeldO` make of `(gateTables 8 4095 true true).2` is `D`
(States.lean).
How. As Johnson/Unfolds/Silu/Digest.lean: `tableDigest_list`; `fs_list`: the table is the library's
stored words (from `Meaning.Gate.fs_get`, `sig_word`, `fs_upper`, Johnson/Meaning/GateRows.lean);
the chain in eight pieces by Lean's kernel (Chain.lean).
Limits. At these numbers alone. That the stored full-size files give them, and that `D` is what the
parameter file's words `tsig` spell, is not said here.

-/
import Johnson.Unfolds.Fs.Chain
import Johnson.Meaning.GateRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds.Fs
open OnBytes.Model.Layer

theorem fsWord_stored {u : Nat} (hu : u < 65536) :
    fsWord true (expPowers 8 32768) u = fsW u := by
  have h1 := Meaning.Gate.fs_get hu
  unfold fsW
  by_cases h : u < 32768
  · have h2 := Meaning.Gate.sig_word h
    rw [h1] at h2
    rw [if_pos h, ← h2, Int.toNat_natCast]
  · have h2 := Meaning.Gate.fs_upper (Nat.le_of_not_lt h) hu
    rw [h1] at h2
    rw [if_neg h, ← h2, Int.toNat_natCast]

theorem fs_list : (gateTables 8 4095 true true).2.toList = fromTo fsW 0 65536 := by
  unfold gateTables
  dsimp only
  rw [if_pos (show (true : Bool) = true from rfl)]
  exact toList_of_range_map _ fsW 65536 fun _ hu => fsWord_stored hu

theorem fs_size : (gateTables 8 4095 true true).2.size = 65536 := by
  rw [← Array.length_toList, fs_list, length_fromTo]

/-- **THE DIGEST OF TABLE FS.** -/
theorem fs_digest :
    OnBytes.secondHashFunction 72 ((gateTables 8 4095 true true).2.foldl
                  (fun b x => b ++ OnBytes.word32 x) ByteArray.empty) = D := by
  rw [tableDigest_list, fs_size, fs_list, digestL]

end Johnson.Unfolds.Fs

#print axioms Johnson.Unfolds.Fs.fsWord_stored
#print axioms Johnson.Unfolds.Fs.fs_list
#print axioms Johnson.Unfolds.Fs.fs_size
#print axioms Johnson.Unfolds.Fs.fs_digest
