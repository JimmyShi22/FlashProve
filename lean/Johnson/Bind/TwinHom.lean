-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinHom.lean: a morphism of monads passes through the committer that runs.

The committer (Johnson/Bind/Twin.lean) is written once, over a variable monad m, with the
hash h as an argument. For every morphism of monads φ (`Run.Hom`, Run/Hom.lean) and every function F
of that file that hashes: φ.app (F h ..) = F (φ.on h) .. . The same is shown of `Fmt.recordSeedsW`,
which the committer calls; for the chain's step beneath it the library has it
(Run/HomFmtProofs.lean). It is used at φ := "the tree of queries, run at an oracle"
(Johnson/Bind/TwinAlgorithm.lean): the committer as an algorithm that asks an oracle has, at each
oracle, the value that the committer as a function has at that oracle.
No Mathlib.

Main theorem: `hom_commitW`.
Limits. Bookkeeping on this library's own terms: nothing on what the committer computes.

-/
import Johnson.Bind.Twin
import Run.HomFmtProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Fmt (Ext)

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

theorem hom_leavesFromW (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (k x : Nat) (acc : Array ByteArray),
      φ.app (leavesFromW h S start col salt k x acc) =
        leavesFromW (φ.on h) S start col salt k x acc
  | 0, _, _ => φ.app_pure _
  | k + 1, x, acc => by
    simp only [leavesFromW, φ.app_bind, hom_leavesFromW S start col salt k]
    rfl

theorem hom_upFromW (cfg : ByteArray) (below : Array ByteArray) :
    ∀ (k i : Nat) (acc : Array ByteArray),
      φ.app (upFromW h cfg below k i acc) = upFromW (φ.on h) cfg below k i acc
  | 0, _, _ => φ.app_pure _
  | k + 1, i, acc => by
    simp only [upFromW, φ.app_bind, hom_upFromW cfg below k]
    rfl

theorem hom_climbW (cfg : ByteArray) :
    ∀ (d : Nat) (now : Array ByteArray),
      φ.app (climbW h cfg d now) = climbW (φ.on h) cfg d now
  | 0, _ => φ.app_pure _
  | d + 1, now => by
    simp only [climbW, φ.app_bind, hom_upFromW, hom_climbW cfg d]

theorem hom_rootW (S : Shape) (cfg : ByteArray) (start : Nat → ByteArray)
    (col : Nat → List UInt64) (salt : Nat → ByteArray) :
    φ.app (rootW h S cfg start col salt) = rootW (φ.on h) S cfg start col salt := by
  simp only [rootW, φ.app_bind, hom_leavesFromW, hom_climbW]

theorem hom_recordSeedsW (f : Fmt.Fld) (name : ByteArray) (v a : Nat) :
    φ.app (Fmt.recordSeedsW h f name v a) = Fmt.recordSeedsW (φ.on h) f name v a := by
  unfold Fmt.recordSeedsW
  simp only [φ.app_bind, Run.Hom.queryW]
  refine congrArg _ (funext fun rho0 => ?_)
  refine congrArg _ (funext fun x => ?_)
  cases x with
  | none => exact φ.app_pure _
  | some y =>
    obtain ⟨y1, y2⟩ := y
    exact φ.app_pure _

theorem hom_seedsW (S : Shape) (name : ByteArray) :
    φ.app (seedsW h S name) = seedsW (φ.on h) S name := by
  unfold seedsW
  split
  · exact φ.app_pure _
  · simp only [φ.app_bind, φ.app_pure, hom_recordSeedsW]

theorem hom_closeW (S : Shape) (cfg root : ByteArray)
    (answersAt : List (List Ext × Ext) → List Ext) :
    φ.app (closeW h S cfg root answersAt) = closeW (φ.on h) S cfg root answersAt := by
  simp only [closeW, φ.app_bind, φ.app_pure, hom_seedsW]
  rfl

theorem hom_coreW (S : Shape) (cfg : ByteArray) (col : Nat → List UInt64) (T : Table) :
    φ.app (coreW h S cfg col T) = coreW (φ.on h) S cfg col T := by
  simp only [coreW, φ.app_bind, hom_rootW, hom_closeW]

theorem hom_plainW (S : Shape) (cfg : ByteArray) (T : Table) :
    φ.app (plainW h S cfg T) = plainW (φ.on h) S cfg T :=
  hom_coreW φ h S cfg _ T

/-- **A morphism of monads passes through the committer.** -/
theorem hom_commitW (S : Shape) (files : List ByteArray) (T : Table) :
    φ.app (commitW h S files T) = commitW (φ.on h) S files T := by
  simp only [commitW, φ.app_bind, hom_plainW]
  rfl

end Bind.Twin

#print axioms Bind.Twin.hom_leavesFromW
#print axioms Bind.Twin.hom_upFromW
#print axioms Bind.Twin.hom_climbW
#print axioms Bind.Twin.hom_rootW
#print axioms Bind.Twin.hom_recordSeedsW
#print axioms Bind.Twin.hom_seedsW
#print axioms Bind.Twin.hom_closeW
#print axioms Bind.Twin.hom_coreW
#print axioms Bind.Twin.hom_plainW
#print axioms Bind.Twin.hom_commitW
