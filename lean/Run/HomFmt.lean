-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HomFmt.lean: every function of Fmt/Rules23.lean, Fmt/Rules4.lean, Fmt/Rules5.lean,
Fmt/Rules7.lean, Fmt/Rules8.lean that is written over a variable monad and takes the hash as a
parameter, read through a morphism of monads, is the same function at the hash read through the
morphism.

Statements; the proofs are in Run/HomFmtProofs.lean. Bookkeeping on this library's own terms: no
rule of the page is stated here; the functions are those of Fmt/Rules23.lean, Fmt/Rules4.lean,
Fmt/Rules5.lean, Fmt/Rules7.lean, Fmt/Rules8.lean, as they stand.

Why (Run/Hom.lean): these functions are written once, over a variable monad m, the hash h first.
For every morphism `φ : Hom m n` and every function F among them: φ.app (F h ..) = F (φ.on h) ..
(for `HM` and the three walks: with ask, comb in the place of h).

Main names:
  `Spec.hom_HM`: the hash by asking the one oracle (`HM`).
  `Spec.hom_first`: the head of a chain (`startChainW`). The functions that are one call of h
    (among them the parameters' digest, the run's value, the first value, the first value of a
    record's chain, the configuration's digest, a leaf, a vertex, a call of a round) need no
    statement: there both sides are the same term.
  `Spec.hom_round`: a round's blocks and the step of a chain (`fetchFrom`, `fetchW`,
    `Chain.queryW`).
  `Spec.hom_tree`: the walk (for any way of combining two values), the opened leaves, an opening's
    reader and its check.
  `Spec.hom_file`: the openings after a draw, one round, the fold, a chain in a file, a whole file
    (`wholeChain`).

The last clause is used at φ := "the tree of queries, run at the oracle f" (into Id) and h := the
hash that asks (`hT`): the parser's tree, run at f, gives what the function that is evaluated gives
at the hash made from f (Run/TieRules.lean).

Limits: this file says nothing on what the functions compute. This file does not say the counts of
questions: Run/CostFmt.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.Hom
import Fmt.Rules8

set_option autoImplicit false

namespace Run
namespace Spec
open _root_.Fmt

def hom_HM : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n) (ask : ByteArray → m ByteArray)
      (number tree index : Nat) (start bytes : ByteArray),
    φ.app (HM ask number tree index start bytes) =
      HM (fun s => φ.app (ask s)) number tree index start bytes

def hom_first : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (lab : Nat)
      (pd statement : ByteArray) (rnd : Option ByteArray),
    φ.app (startChainW h lab pd statement rnd) = startChainW (φ.on h) lab pd statement rnd

def hom_round : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray),
    (∀ (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind)
          (w nonce k j : Nat) (acc : Array ByteArray),
        φ.app (fetchFrom h lab rho i msg kind w nonce k j acc) =
          fetchFrom (φ.on h) lab rho i msg kind w nonce k j acc) ∧
    (∀ (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce k : Nat),
      φ.app (fetchW h lab rho i msg kind w nonce k) =
        fetchW (φ.on h) lab rho i msg kind w nonce k) ∧
    ∀ (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat),
      φ.app (c.queryW h msg kind work nonce K) = c.queryW (φ.on h) msg kind work nonce K

def hom_tree : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n),
    (∀ (α σ : Type) (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ)),
      (∀ (d i : Nat) (x : α) (s : σ), φ.app (walkLoneW comb give d i x s) =
        walkLoneW (fun a b c e => φ.app (comb a b c e)) give d i x s) ∧
      (∀ (d : Nat) (l : List (Nat × α)) (s : σ), φ.app (walkLevelW comb give d l s) =
        walkLevelW (fun a b c e => φ.app (comb a b c e)) give d l s) ∧
      ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
        φ.app (walkW comb give d now s met) =
          walkW (fun a b c e => φ.app (comb a b c e)) give d now s met) ∧
    ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray),
      (∀ (sh : Shape) (start : ByteArray) (xs : List Nat) (cs : List (List UInt64 × ByteArray)),
        φ.app (leavesW h sh start xs cs) = leavesW (φ.on h) sh start xs cs) ∧
      (∀ (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray) (xs : List Nat)
            (b : ByteArray) (i : Nat),
          φ.app (readOpeningW h cfg f salt sh start xs b i) =
            readOpeningW (φ.on h) cfg f salt sh start xs b i) ∧
      ∀ (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start root : ByteArray)
          (xs : List Nat) (opening : ByteArray),
        φ.app (checkOpeningW h cfg f salt sh start root xs opening) =
          checkOpeningW (φ.on h) cfg f salt sh start root xs opening

/-- States the equation for the openings after a draw, a round, the fold over rounds, a chain in a
file, and a whole file. -/
def hom_file : Prop :=
  ∀ (m n : Type → Type) [Monad m] [Monad n] (φ : Hom m n)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray),
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (roots : Array ByteArray)
          (poss : List Nat) (b : ByteArray) (os : List (Shape × Src)) (sn : Seen) (i : Nat),
        φ.app (readOpens h cfg P run roots poss b os sn i) =
          readOpens (φ.on h) cfg P run roots poss b os sn i) ∧
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round),
      φ.app (step h cfg P run b s r) = step (φ.on h) cfg P run b s r) ∧
    (∀ (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray)
          (rs : List Round) (s : St),
        φ.app (foldRounds h cfg P run b rs s) = foldRounds (φ.on h) cfg P run b rs s) ∧
    (∀ (S : Fmt.Spec) (seen : Seen) (b : ByteArray) (i : Nat),
      φ.app (readChain h S seen b i) = readChain (φ.on h) S seen b i) ∧
    ∀ (S : Fmt.Spec) (b : ByteArray), φ.app (wholeChain h S b) = wholeChain (φ.on h) S b

end Spec
end Run
