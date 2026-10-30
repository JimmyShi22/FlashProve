-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinCost.lean: how often the committer that runs calls the hash.

The committer (Johnson/Bind/Twin.lean) is written over a variable monad m, with the hash h
as an argument. For every count of questions c (`Run.CostP`, Run/CostP.lean): if each call of h asks
at most k, the committer asks at most `calls S` times k, at every shape S, all public files and
every table. `calls S` is read off the text: the public files' digest (1), the leaves (2^a), the
vertices (2^a - 1), the seeds' chain (`seedCalls S`: its first value, and the calls under the number
162 that `Fmt.recordSeedsW` fetches), the commitment ID (1).
No Mathlib.

Main definitions: `seedCalls`, `calls`. Main theorem: `cost_commitW`.
Limits. An upper bound. What "asks at most" says hangs on the count c alone (Run/CostP.lean, 4): it
is laid at the trees of queries in Johnson/Bind/TwinAlgorithm.lean. Where the shape has no
answers the seeds' chain is not asked, and the bound still counts it.

-/
import Johnson.Bind.Twin
import Run.CostFmtProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open Fmt (Ext)

/-- The calls of the hash for the OOD seeds: the chain's first value, then the round's calls. -/
def seedCalls (S : Shape) : Nat :=
  1 + (Fmt.firstBlock 0 + Fmt.blocksFor (S.s * (S.cube * 18 + 36)) + 1) / 2

/-- The calls of the hash in one commitment, at most. -/
def calls (S : Shape) : Nat := 1 + 2 ^ S.a + (2 ^ S.a - 1) + seedCalls S + 1

theorem two_pow_step (d k : Nat) : 2 ^ d * k + (2 ^ d - 1) * k ≤ (2 ^ (d + 1) - 1) * k := by
  rw [← Nat.add_mul]
  refine Nat.mul_le_mul_right k ?_
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  rw [Nat.pow_succ]
  omega

variable {m : Type → Type} [Monad m] (c : Run.CostP m)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem cost_leavesFromW (S : Shape) (start : Nat → ByteArray) (col : Nat → List UInt64)
    (salt : Nat → ByteArray) :
    ∀ (n x : Nat) (acc : Array ByteArray),
      c.le (leavesFromW h S start col salt n x acc) (n * k) fun _ => True
  | 0, _, _ => c.pureLe _ _ _ trivial
  | n + 1, x, acc => by
    simp only [leavesFromW]
    exact c.le_mono _ (k + n * k) _ _ _
      (c.le_bind _ _ k (n * k) _ _ (hk _ _ _ _ _) fun _ _ =>
        cost_leavesFromW S start col salt n _ _)
      (by rw [Nat.succ_mul]; omega) fun _ h => h

theorem cost_upFromW (cfg : ByteArray) (below : Array ByteArray) :
    ∀ (n i : Nat) (acc : Array ByteArray),
      c.le (upFromW h cfg below n i acc) (n * k) fun _ => True
  | 0, _, _ => c.pureLe _ _ _ trivial
  | n + 1, i, acc => by
    simp only [upFromW]
    exact c.le_mono _ (k + n * k) _ _ _
      (c.le_bind _ _ k (n * k) _ _ (hk _ _ _ _ _) fun _ _ => cost_upFromW cfg below n _ _)
      (by rw [Nat.succ_mul]; omega) fun _ h => h

theorem cost_climbW (cfg : ByteArray) :
    ∀ (d : Nat) (now : Array ByteArray),
      c.le (climbW h cfg d now) ((2 ^ d - 1) * k) fun _ => True
  | 0, _ => c.pureLe _ _ _ trivial
  | d + 1, now => by
    simp only [climbW]
    exact c.le_mono _ (2 ^ d * k + (2 ^ d - 1) * k) _ _ _
      (c.le_bind _ _ (2 ^ d * k) ((2 ^ d - 1) * k) _ _ (cost_upFromW c h k hk cfg now _ _ _)
        fun _ _ => cost_climbW cfg d _)
      (two_pow_step d k) fun _ h => h

theorem cost_rootW (S : Shape) (cfg : ByteArray) (start : Nat → ByteArray)
    (col : Nat → List UInt64) (salt : Nat → ByteArray) :
    c.le (rootW h S cfg start col salt) (2 ^ S.a * k + (2 ^ S.a - 1) * k) fun _ => True := by
  simp only [rootW]
  exact c.le_bind _ _ _ _ _ _ (cost_leavesFromW c h k hk S start col salt _ _ _)
    fun _ _ => cost_climbW c h k hk cfg _ _

theorem cost_recordSeedsW (f : Fmt.Fld) (name : ByteArray) (v a : Nat) :
    c.le (Fmt.recordSeedsW h f name v a)
      (k + (Fmt.firstBlock 0 + Fmt.blocksFor (a * (v * 18 + 36)) + 1) / 2 * k) fun _ => True := by
  unfold Fmt.recordSeedsW
  refine c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun rho0 _ => ?_
  refine c.le_mono _ (_ + 0) _ _ _
    (c.le_bind _ _ _ 0 _ _ (c.queryW h k hk _ _ _ _ _ _) fun x _ => ?_)
    (Nat.le_of_eq (Nat.add_zero _)) fun _ h => h
  cases x with
  | none => exact c.le_pure _ _ trivial
  | some y =>
    obtain ⟨y1, y2⟩ := y
    exact c.le_pure _ _ trivial

theorem cost_seedsW (S : Shape) (name : ByteArray) :
    c.le (seedsW h S name) (seedCalls S * k) fun _ => True := by
  unfold seedsW
  split
  · exact c.pureLe _ _ _ trivial
  · exact c.le_mono _ _ _ _ _
      (c.bindPure _ _ _ _ _ (cost_recordSeedsW c h k hk _ _ _ _) fun _ _ => trivial)
      (by unfold seedCalls; rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_refl _) fun _ h => h

theorem cost_closeW (S : Shape) (cfg root : ByteArray)
    (answersAt : List (List Ext × Ext) → List Ext) :
    c.le (closeW h S cfg root answersAt) (seedCalls S * k + (k + 0)) fun _ => True := by
  simp only [closeW]
  exact c.le_bind _ _ _ _ _ _ (cost_seedsW c h k hk S _) fun _ _ =>
    c.le_bind _ _ k 0 _ _ (hk _ _ _ _ _) fun _ _ => c.le_pure _ _ trivial

theorem cost_coreW (S : Shape) (cfg : ByteArray) (col : Nat → List UInt64) (T : Table) :
    c.le (coreW h S cfg col T)
      (2 ^ S.a * k + (2 ^ S.a - 1) * k + (seedCalls S * k + (k + 0))) fun _ => True := by
  simp only [coreW]
  exact c.le_bind _ _ _ _ _ _ (cost_rootW c h k hk S cfg _ col T.salt) fun _ _ =>
    cost_closeW c h k hk S cfg _ _

/-- **Where a call of the hash asks at most k, the committer asks at most `calls S` times k.** -/
theorem cost_commitW (S : Shape) (files : List ByteArray) (T : Table) :
    c.le (commitW h S files T) (calls S * k) fun _ => True := by
  simp only [commitW]
  exact c.le_mono _ (k + (2 ^ S.a * k + (2 ^ S.a - 1) * k + (seedCalls S * k + (k + 0)))) _ _ _
    (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun cfg _ => cost_coreW c h k hk S cfg _ T)
    (by simp only [calls, Nat.add_mul, Nat.one_mul]; omega) fun _ h => h

end Bind.Twin

#print axioms Bind.Twin.two_pow_step
#print axioms Bind.Twin.cost_leavesFromW
#print axioms Bind.Twin.cost_upFromW
#print axioms Bind.Twin.cost_climbW
#print axioms Bind.Twin.cost_rootW
#print axioms Bind.Twin.cost_recordSeedsW
#print axioms Bind.Twin.cost_seedsW
#print axioms Bind.Twin.cost_closeW
#print axioms Bind.Twin.cost_coreW
#print axioms Bind.Twin.cost_commitW
