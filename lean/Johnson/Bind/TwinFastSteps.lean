-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastSteps.lean: the committer at the fast encoder, at the identity monad, is a
chain of plain steps: one block's leaves after another, the tree's depths, the closing steps.

A program that runs the committer (Johnson/Bind/TwinFast.lean) on a large table wants to print
between the steps and to compare what each has made. Such a program calls `leavesBlocksW` for one
block at a time, with that block's table made beforehand, then `climbW`, then `closeW`; and it may
keep answers that it has made already at the same seeds. This file says that the chain of these
steps is the committer's own value.
Main theorems, at every hash h with values in the identity monad and every shape:
   `leavesBlocksW_steps`: the loop over n blocks is the fold, over these blocks in order, of the
      loop over one block at that block's table.
   `answers_kept`: the function that returns kept answers at the seeds at which they were made, and
      makes them anew at others, is `answers S T`.
   `fastW_steps`: `fastW h S cfg T` is: prepare; that fold from no leaves; `climbW`; `closeW`.
   `commitFastW_steps`: the same behind the digest of the public files.
No Mathlib.
Limits. Equations between this library's own terms. That a program with prints computes the chain on
the right is for a reading of that program: nothing here speaks of IO.

-/
import Johnson.Bind.TwinFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Fmt (Ext)

variable (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)

/-- One block's leaves behind those that are there, at that block's table. -/
def blockStep (S : Shape) (start : Nat → ByteArray) (salt : Nat → ByteArray)
    (table : Array ByteArray) (B : Nat) (acc : Array ByteArray) : Array ByteArray :=
  Id.run (leavesBlocksW h S start (fun _ => table) salt 1 B acc)

/-- **The loop over n blocks is the fold of the loop over one block.** -/
theorem leavesBlocksW_steps (S : Shape) (start : Nat → ByteArray) (block : Nat → Array ByteArray)
    (salt : Nat → ByteArray) :
    ∀ (n B : Nat) (acc : Array ByteArray),
      Id.run (leavesBlocksW h S start block salt n B acc) =
        (List.range' B n).foldl (fun acc B' => blockStep h S start salt (block B') B' acc) acc
  | 0, _, _ => rfl
  | n + 1, B, acc => by
    rw [List.range'_succ, List.foldl_cons, ← leavesBlocksW_steps S start block salt n (B + 1)]
    rfl

/-- Answers that are kept at the seeds at which they were made. -/
theorem answers_kept (S : Shape) (T : Table) (seeds : List (List Ext × Ext)) :
    (fun sd => if sd == seeds then answers S T seeds else answers S T sd) = answers S T := by
  funext sd
  split
  · rename_i e
    rw [eq_of_beq e]
  · rfl

/-- The chain of steps behind the digest of the public files. -/
def fastSteps (S : Shape) (cfg : ByteArray) (T : Table) : Out :=
  let P := prepare S T
  let leaves := (List.range (2 ^ (S.a - S.span))).foldl
    (fun acc B => blockStep h S (fun _ => cfg) T.salt (blockAt S P B) B acc) #[]
  let root := Id.run (climbW h cfg S.a leaves)
  Id.run (closeW h S cfg root (answers S T))

/-- **The committer at the fast encoder is the chain of its steps.** -/
theorem fastW_steps (S : Shape) (cfg : ByteArray) (T : Table) :
    Id.run (fastW h S cfg T) = fastSteps h S cfg T := by
  show _ = Id.run (closeW h S cfg (Id.run (climbW h cfg S.a
    ((List.range (2 ^ (S.a - S.span))).foldl
      (fun acc B => blockStep h S (fun _ => cfg) T.salt (blockAt S (prepare S T) B) B acc) #[])))
    (answers S T))
  rw [List.range_eq_range', ← leavesBlocksW_steps h S (fun _ => cfg) (blockAt S (prepare S T))
    T.salt (2 ^ (S.a - S.span)) 0 #[]]
  rfl

theorem commitFastW_steps (S : Shape) (files : List ByteArray) (T : Table) :
    Id.run (commitFastW h S files T) =
      fastSteps h S (Id.run (Fmt.configDigestW h files)) T :=
  fastW_steps h S _ T

end Bind.Twin

#print axioms Bind.Twin.leavesBlocksW_steps
#print axioms Bind.Twin.answers_kept
#print axioms Bind.Twin.fastW_steps
#print axioms Bind.Twin.commitFastW_steps
