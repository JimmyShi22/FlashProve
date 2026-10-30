-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawRow.lean: a reader of a row of words, as a tree.

This file is about how a verifier message is made from a row of words when the number of words that
a step uses depends on the words themselves, as in rejection sampling. Definitions only. The laws
(the theorems on the count `N` and on `Good`): Run/DrawCount.lean. From words to blocks and to the
block samplers of Iop/Draw.lean: Run/DrawBS.lean.

Why: the block samplers of Iop/Draw.lean give every coordinate of a verifier message blocks of its
own, at fixed places. The programs' format draws otherwise: a round's answer is cut into a row of
words, each draw takes the next words of the row, and how many it takes depends on the words (a try
that fails costs a word). So the place at which a draw reads moves with the draws before it.
A reader that takes the next words of a row, one at a time, and says after each whether it takes
another, is a tree.

Main names:
  `Tr W C`: `ret c`: "the value is c"; `ask k`: "take the next word w, go on as k w".
  `tries ok dflt n`: at most n words: the value of the first word on which ok gives one; if all n
    fail, the constant dflt, and the n words are used up.
  `run d t row`: on a list of words: (the value, what is left). Beyond the end of the list the word
    is d and the list stays empty: so `run` is total.
  `N d K t c`: the number of rows of K words on which t has the value c.
  `Good d t K w κ`: the law, in the form of `Iop.BS.Good`: t asks for at most K words; every value
    has at most w rows of K words; w · |C| ≤ κ · |W|^K. So, if C is finite, one value takes at most
    κ times its even share of all rows of K words: κ bounds the bias.

All functions here compute, but for `N`; `N` and `Good` are used in statements and are no part of a
verifier.

Limits: this file does not say which readers the format has: Run/DrawPage.lean. It says nothing on
where the words come from.

Terms: lean/GLOSSARY.md.
-/
import Iop.Draw
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Run
open Prob
open scoped ENNReal

/-- A reader of a row of words. -/
inductive Tr (W C : Type) : Type
  | ret : C → Tr W C
  | ask : (W → Tr W C) → Tr W C

namespace Tr
variable {W C D : Type}

/-- first t, then f of its value on what is left -/
def bind : Tr W C → (C → Tr W D) → Tr W D
  | ret c, f => f c
  | ask k, f => ask fun w => (k w).bind f

def map (g : C → D) (t : Tr W C) : Tr W D := t.bind fun c => ret (g c)

/-- s, then t -/
def pair (s : Tr W C) (t : Tr W D) : Tr W (C × D) := s.bind fun c => t.map fun d => (c, d)

/-- t n times, coordinate 0 first -/
def vec : (n : ℕ) → Tr W C → Tr W (Fin n → C)
  | 0, _ => ret Fin.elim0
  | n + 1, t => (t.pair (vec n t)).map fun x => Fin.cons x.1 x.2

/-- the next word -/
def word : Tr W W := ask ret

/-- At most n tries, a word each; then the constant. -/
def tries (ok : W → Option C) (dflt : C) : ℕ → Tr W C
  | 0 => ret dflt
  | n + 1 => ask fun w => match ok w with
    | some c => ret c
    | none => tries ok dflt n

/-- on a list of words: the value, and what is left -/
def run (d : W) : Tr W C → List W → C × List W
  | ret c, r => (c, r)
  | ask k, [] => run d (k d) []
  | ask k, w :: r => run d (k w) r

/-- on a row of exactly K words -/
def ev (d : W) : (K : ℕ) → Tr W C → (Fin K → W) → C
  | _, ret c, _ => c
  | 0, ask k, u => ev d 0 (k d) u
  | K + 1, ask k, u => ev d K (k (u 0)) (Fin.tail u)

/-- no branch asks for more than K words -/
inductive Most : Tr W C → ℕ → Prop
  | ret (c : C) (K : ℕ) : Most (ret c) K
  | ask (k : W → Tr W C) (K : ℕ) : (∀ w, Most (k w) K) → Most (ask k) (K + 1)

/-- the number of rows of K words with the value c -/
def N [Finite W] (d : W) (K : ℕ) (t : Tr W C) (c : C) : ℕ :=
  cnt fun u : Fin K → W => ev d K t u = c

/-- The law of a reader, in the form of `Iop.BS.Good`: the head tells its three clauses. -/
structure Good [Finite W] (d : W) (t : Tr W C) (K w : ℕ) (κ : ℝ≥0∞) : Prop where
  most : t.Most K
  fib : ∀ c, N d K t c ≤ w
  ratio : (w : ℝ≥0∞) * (Nat.card C : ℝ≥0∞) ≤ κ * (Nat.card W : ℝ≥0∞) ^ K

end Tr
end Run
