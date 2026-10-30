-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostLax.lean: how many questions the lenient reader of a proof file asks at most: a number that
is a function of the description alone, with no term for the openings.

Run/CostFmt.lean has the counts of the format's own functions, up to the strict reader (`fileN S`).
The lenient reader (Run/ParseLax.lean) computes the parameters' digest, the run's value, the first
value and each round's blocks, as the strict one does, and hashes no leaf and no vertex. A count is
a `c : CostP m`; what it says depends on the instance c: Run/CostP.lean, the head, 4.

1. What the file contains. Three definitions, a statement (`Run.Spec.cost_lax`) and proofs.
   `laxRoundN r`: the questions of one round, in units of k (k: what one call of the hash costs):
      (the first block's number + the message's blocks + 1) / 2: the first summand of
      Run/CostFmt.lean's `roundN`.

2. What is checked when the file compiles. Only the types and proofs.

3. Theorems. For every count c : `CostP m` and every hash h of which each call asks at most k.
   By name: `Run.CostP.laxQueryW`, `cutStep`, `cutFold`, `cutChain`, `cutWhole`, `laxWhole`,
      `parseLaxW` in the same namespace. The functions cut.. take a reader of openings in the
      monad: if it costs at most kO at every call, a round costs laxRoundN r · k + kO.
   `cost_lax`: `laxWhole` and `parseLaxW`: (laxN S) · k; and laxN S ≤ fileN S (`laxRoundsN_le`).

4. What is not claimed. These are upper bounds. What Run/CostFmt.lean's head says is not counted
there is not counted here. Nothing on what the functions compute.

Terms: lean/GLOSSARY.md.
-/
import Run.CostFmtProofs
import Run.ParseLax

set_option autoImplicit false

namespace Run
open _root_.Fmt (Plan Spec St Chain Kind Round firstBlock wordsAtMost)

/-- The questions of one round of the lenient reader, in units of k (an upper bound: the head, 4).
-/
def laxRoundN (r : Round) : Nat :=
  (firstBlock r.entry.work + (wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2

def laxRoundsN : List Round → Nat
  | [] => 0
  | r :: rs => laxRoundN r + laxRoundsN rs

/-- The questions of the lenient reader on a whole file, in units of k (an upper bound: the head,
4). -/
def laxN (S : Spec) : Nat := 3 + laxRoundsN S.rounds

open Iop Compile.Batch in
def Spec.cost_lax : Prop :=
  (∀ (m : Type → Type) [Monad m] (c : CostP m)
        (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat),
      (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
      ∀ (S : _root_.Fmt.Spec) (b : ByteArray),
        c.le (laxWhole h S b) (laxN S * k) (fun _ => True) ∧
        ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (T : Typing Q),
          c.le (parseLaxW h S T b) (laxN S * k) fun _ => True) ∧
  ∀ S : _root_.Fmt.Spec, laxN S ≤ fileN S

namespace CostP
variable {m : Type → Type} [Monad m] (c : CostP m)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem laxQueryW (ch : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    c.le (Run.laxQueryW h ch msg kind work nonce K)
      ((firstBlock work + K + 1) / 2 * k) fun _ => True := by
  unfold Run.laxQueryW
  split
  · exact c.bindPure _ _ _ _ _ (c.fetchW h k hk _ _ _ _ _ _ _ _) fun _ _ => trivial
  · exact c.pureLe _ _ _ trivial

theorem cutStep (ops : OpsW m) (kO : Nat)
    (ho : ∀ run roots poss os i, c.le (ops run roots poss os i) kO fun _ => True) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round) :
    c.le (Run.cutStep h ops P run b s r) (laxRoundN r * k + kO) fun _ => True := by
  unfold Run.cutStep
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_bind _ _ _ _ _ _ (c.laxQueryW h k hk _ _ _ _ _ _) fun q _ => ?_
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_bind _ _ kO 0 (fun _ => True) _ (ho _ _ _ _ _) fun q _ => ?_
            cases q <;> exact c.le_pure _ _ trivial

theorem cutFold (ops : OpsW m) (kO : Nat)
    (ho : ∀ run roots poss os i, c.le (ops run roots poss os i) kO fun _ => True) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      c.le (Run.cutFold h ops P run b rs s) (laxRoundsN rs * k + rs.length * kO) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | r :: rs, s => by
    simp only [Run.cutFold]
    refine c.le_mono _ ((laxRoundN r * k + kO) + (laxRoundsN rs * k + rs.length * kO)) _ _ _
      (c.le_bind _ _ _ _ _ _ (c.cutStep h k hk ops kO ho P run b s r) fun q _ => ?_)
      (by simp only [laxRoundsN, Nat.add_mul, List.length_cons, Nat.one_mul]; omega) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ trivial
    | some s' => exact cutFold ops kO ho P run b rs s'

theorem cutChain (ops : ByteArray → OpsW m) (kO : Nat)
    (ho : ∀ b run roots poss os i, c.le (ops b run roots poss os i) kO fun _ => True) (S : Spec)
    (b : ByteArray) (i : Nat) :
    c.le (Run.cutChain h ops S b i) (laxN S * k + S.rounds.length * kO) fun _ => True := by
  unfold Run.cutChain
  split
  · exact c.pureLe _ _ _ trivial
  · simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _
        (k + (2 * k + ((laxRoundsN S.rounds * k + S.rounds.length * kO) + 0))) _ _ _
        (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
          c.le_bind _ _ _ _ _ _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
        (by simp only [laxN, Nat.add_mul]; omega) fun _ h => h
      cases q with
      | none => exact c.pureLe _ _ _ trivial
      | some hd =>
        refine c.le_bind _ _ _ 0 _ _ (c.cutFold h k hk (ops b) kO (ho b) _ _ _ _ _) fun q _ => ?_
        cases q <;> exact c.le_pure _ _ trivial

theorem cutWhole (ops : ByteArray → OpsW m) (kO : Nat)
    (ho : ∀ b run roots poss os i, c.le (ops b run roots poss os i) kO fun _ => True)
    (S : Spec) (b : ByteArray) :
    c.le (Run.cutWhole h ops S b) (laxN S * k + S.rounds.length * kO) fun _ => True := by
  simp only [Run.cutWhole]
  refine c.le_bind _ _ _ 0 _ _ (c.cutChain h k hk ops kO ho S b 0) fun q _ => ?_
  cases q <;> exact c.le_pure _ _ trivial

theorem laxWhole (S : Spec) (b : ByteArray) :
    c.le (Run.laxWhole h S b) (laxN S * k) fun _ => True := by
  unfold Run.laxWhole
  exact c.le_mono _ _ _ _ _ (c.cutWhole h k hk _ 0 (fun _ _ _ _ _ _ => c.le_pure _ _ trivial) S b)
    (by omega) fun _ h => h

open Iop Compile.Batch in
theorem parseLaxW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) :
    c.le (Run.parseLaxW h S T b) (laxN S * k) fun _ => True := by
  simp only [Run.parseLaxW]
  exact c.bindPure _ _ _ _ _ (c.laxWhole h k hk S b) fun _ _ => trivial

end CostP

theorem laxRoundsN_le : ∀ rs : List Round, laxRoundsN rs ≤ roundsN rs
  | [] => Nat.le_refl _
  | r :: rs => by
    simp only [laxRoundsN, roundsN, roundN, laxRoundN]
    have := laxRoundsN_le rs
    omega

theorem cost_lax : Spec.cost_lax :=
  ⟨fun _ _ c h k hk S b => ⟨c.laxWhole h k hk S b, fun _ _ _ T => c.parseLaxW h k hk S T b⟩, fun S => by
    simp only [laxN, fileN]
    have := laxRoundsN_le S.rounds
    omega⟩

end Run
