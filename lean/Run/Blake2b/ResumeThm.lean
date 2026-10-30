-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Run.Blake2b.WordsThm
/-!
# A message cut in two

The hash of a message that begins with whole blocks can be continued from the state after these
blocks. The state carries its counter, so nothing else has to be kept.

* updateBlocks_add: a + b blocks are a blocks and then b blocks.
* updateBlocks_congr, updateBlocks_shift, message_congr: which blocks the loop and a message read.
* message_split: a message cut after k whole blocks, if at least one byte follows them.

Not proved here: anything about a message whose rest is empty (an example where the equation fails:
Test/Salted.lean). The last block of a message has the flag and its own count of bytes, also if it
is a full block. If nothing follows the beginning, then the beginning's last block is the message's
last block, and the state after it is not a stage of that message's hash.
Source. updateBlocks_succ and updateBlocks_one write out again the step of updateBlocks (Hash.lean):
incrementCounter, then compress. They follow, at one remove, what Hash.lean names as its source.
Hash.lean's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
-/
namespace Run.Blake2b

theorem updateBlocks_zero (blk : Nat → MessageBlock) (i : Nat) (S : State) :
    updateBlocks blk 0 i S = S := rfl

theorem updateBlocks_succ (blk : Nat → MessageBlock) (n i : Nat) (S : State) :
    updateBlocks blk (n + 1) i S =
      updateBlocks blk n (i + 1) (compress (incrementCounter S 128) (blk i)) := rfl

/-- One block: the two equations above, one after the other. -/
theorem updateBlocks_one (blk : Nat → MessageBlock) (i : Nat) (S : State) :
    updateBlocks blk 1 i S = compress (incrementCounter S 128) (blk i) :=
  (updateBlocks_succ blk 0 i S).trans (updateBlocks_zero blk (i + 1) _)

/-- a + b blocks are a blocks and then b blocks. -/
theorem updateBlocks_add (blk : Nat → MessageBlock) (a b i : Nat) (S : State) :
    updateBlocks blk (a + b) i S = updateBlocks blk b (i + a) (updateBlocks blk a i S) := by
  induction a generalizing i S with
  | zero => rw [Nat.zero_add, updateBlocks_zero, Nat.add_zero]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 from by omega, updateBlocks_succ, updateBlocks_succ, ih,
      show i + 1 + a = i + (a + 1) from by omega]

/-- The loop reads the blocks i, .., i + n - 1 only. -/
theorem updateBlocks_congr {blk blk' : Nat → MessageBlock} (n i : Nat) (S : State)
    (e : ∀ j, i ≤ j → j < i + n → blk j = blk' j) :
    updateBlocks blk n i S = updateBlocks blk' n i S := by
  induction n generalizing i S with
  | zero => rfl
  | succ n ih =>
    rw [updateBlocks_succ, updateBlocks_succ, e i (Nat.le_refl _) (by omega)]
    exact ih _ _ (fun j h1 h2 => e j (by omega) (by omega))

/-- The loop from block k + i on is the loop from block i on of the blocks numbered from k. -/
theorem updateBlocks_shift (blk : Nat → MessageBlock) (k n i : Nat) (S : State) :
    updateBlocks blk n (k + i) S = updateBlocks (fun j => blk (k + j)) n i S := by
  induction n generalizing i S with
  | zero => rfl
  | succ n ih =>
    rw [updateBlocks_succ, updateBlocks_succ]
    exact ih (i + 1) _

/-- A message reads the blocks 0, .., (inlen - 1) / 128 only. -/
theorem message_congr {blk blk' : Nat → MessageBlock} (inlen : Nat) (S : State)
    (e : ∀ j, j ≤ (inlen - 1) / 128 → blk j = blk' j) :
    message blk inlen S = message blk' inlen S := by
  rw [message_eq, message_eq, e _ (Nat.le_refl _),
    updateBlocks_congr _ _ _ (fun j _ h2 => e j (by omega))]

/-- A message cut after k whole blocks. If at least one byte follows them, the message's last state
is that of the rest, begun in the state after the k blocks. -/
theorem message_split (blk : Nat → MessageBlock) (k inlen : Nat) (S : State) (hl : 0 < inlen) :
    message blk (128 * k + inlen) S =
      message (fun j => blk (k + j)) inlen (updateBlocks blk k 0 S) := by
  have e : (128 * k + inlen - 1) / 128 = k + (inlen - 1) / 128 := by omega
  have r : 128 * k + inlen - 128 * (k + (inlen - 1) / 128) = inlen - 128 * ((inlen - 1) / 128) := by
    omega
  have s := updateBlocks_shift blk k ((inlen - 1) / 128) 0 (updateBlocks blk k 0 S)
  rw [Nat.add_zero] at s
  rw [message_eq, message_eq, e, r, updateBlocks_add, Nat.zero_add, s]

end Run.Blake2b
