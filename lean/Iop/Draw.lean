-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Draw.lean: challenge samplers: how a challenge is computed from hash blocks of λ bits,
coordinate by coordinate. Definitions and a statement; proofs: Iop/DrawProofs.lean. (Words of this
library: lean/GLOSSARY.md.)

Iop/Univ.lean has one sampler for every round: all blocks are read as one binary number, which is
reduced modulo the number of values of the challenge and looked up in a numbering of these values.
The implementation does not do that, and the numbering exists in no explicit form that a program
could use (in Lean it is a datum of the caller: `Shape.NumChal`, Iop/Num.lean). Here a sampler is a
datum of the round (`BS lam C`: a number b of blocks, a function from b blocks to C, a bound w on
its fibres), and samplers of large challenges are composed of samplers of their coordinates, each of
which reads its own blocks:
    unit, map, prod, vec, pi, bits   see their docstrings
    modN m k            a number below m: the binary value of k blocks, modulo m. With k = 1 and m =
                        2^L this is "the low L bits of the block"
    three ok el         rejection sampling with three attempts, one block each: the first block that
                        passes the check ok gives the value el; if the first two fail, the third
                        gives its value whether it passes or not

The check for a sampled 0. A sampler has two more data: z, a public check on the value that it has
computed (true: stop), and nz, a number. They are there for one rule of the implementation: "every
element of the field E that is drawn from hash output and is 0 is rejected, whatever it is for". A
challenge is a bare type here, and only its sampler knows which of its coordinates are sampled
elements of E. So a sampler of E is meant to have z x = "x is 0" and nz = 1 (arguments of `three`);
a sampler without elements of E (unit, modN, bits) has z false everywhere and nz = 0; prod, vec, pi
say "one of the coordinates stops" (z is true if it is for one of the coordinates) and add the
numbers up; map carries the check along the bijection. No condition of this file reads z or nz, and
no sampled value depends on them.

The condition on a sampler (`BS.Good s κ`), as in Iop/Pull.lean: every value has at most w
preimages, and w · |C| ≤ κ · 2^(λ b). The bias is multiplicative. For a whole list of rounds the
statement is in one number κ₀ ≥ 1: every round with b blocks has κ = κ₀^b (`Shape.Draws.Good`), so
that the largest round error grows by at most the factor κ₀^(largest b) and the probability of a set
of whole ρ by at most κ₀^(sum of the b) (`Spec.drawsGood`, with `prRho_preimage_le`,
Iop/PullProofs.lean).

Notation: `Dig lam : Type` (Iop/Wire.lean): a hash block (a digest or a chaining value): lam bits;
`cnt P : ℕ` (Prob/Cnt.lean): the number of elements of a finite type with the property P;
`Num.blocks lam k` (Iop/Num.lean): the binary value of k blocks of lam bits, as a numbering.

Limits. Nothing is said on which sampler a given implementation uses: this file has no sampler for a
concrete field; tools for the samplers of the protocols are in Blocks/Draws.lean.
Nothing on where the blocks come from: in the implementation (by reading its sources) each block is
a call of the hash function of its own, block 0 on the round's whole body and every later block on
the round's state and a counter; here the blocks of a round are the blocks of one answer of an
oracle.
The number of blocks of a round is fixed. A sampler that asks for a further block only after a
rejection computes the same value; it makes fewer queries, and no count of queries here knows of
that: all blocks of a round are counted.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.Univ
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

namespace Iop
open Prob
open scoped ENNReal

/-- A challenge sampler for the type C: the element of C is φ of b uniform blocks of lam bits; w
bounds the fibres of φ. -/
structure BS (lam : ℕ) (C : Type) where
  b : ℕ
  φ : (Fin b → Dig lam) → C
  w : ℕ
  /-- the sampler's public check on the value (true: stop) -/
  z : C → Bool
  /-- the number of sampled elements that the check looks at -/
  nz : ℕ

namespace BS
variable {lam : ℕ} {C D : Type}

/-- As a sampler of a round (Iop/Pull.lean). -/
def sampler {r : Round} (s : BS lam r.Chal) : Sampler r where
  Src := Fin s.b → Dig lam
  φ := s.φ
  w := s.w

/-- no block -/
def unit : BS lam Unit := ⟨0, fun _ => (), 1, fun _ => false, 0⟩

/-- the image under a bijection; the check is carried along -/
def map (e : C ≃ D) (s : BS lam C) : BS lam D :=
  ⟨s.b, fun u => e (s.φ u), s.w, fun d => s.z (e.symm d), s.nz⟩

/-- a pair: the blocks of the first coordinate, then those of the second -/
def prod (s : BS lam C) (t : BS lam D) : BS lam (C × D) :=
  ⟨s.b + t.b,
    fun u => (s.φ fun i => u (Fin.castAdd t.b i), t.φ fun i => u (Fin.natAdd s.b i)),
    s.w * t.w,
    fun c => s.z c.1 || t.z c.2,
    s.nz + t.nz⟩

/-- a vector: coordinate i reads the blocks t + b · i, t < b -/
def vec (n : ℕ) (s : BS lam C) : BS lam (Fin n → C) :=
  ⟨n * s.b, fun u i => s.φ fun t => u (finProdFinEquiv (i, t)), s.w ^ n,
    fun c => (List.finRange n).any fun i => s.z (c i), n * s.nz⟩

/-- coordinates of several kinds: coordinate j reads its blocks after those of the coordinates
before it -/
def pi {n : ℕ} {C : Fin n → Type} (s : ∀ j, BS lam (C j)) : BS lam (∀ j, C j) :=
  ⟨∑ j, (s j).b,
    fun u j => (s j).φ fun t => u (finSigmaFinEquiv ⟨j, t⟩),
    ∏ j, (s j).w,
    fun c => (List.finRange n).any fun j => (s j).z (c j),
    ∑ j, (s j).nz⟩

/-- a number below m: the binary value of k blocks (bit i of block j has the weight 2^i (2^lam)^j),
modulo m -/
def modN (lam m k : ℕ) (h : 0 < m) : BS lam (Fin m) :=
  ⟨k, fun u => ⟨(Num.blocks lam k u).val % m, Nat.mod_lt _ h⟩,
    (2 ^ (lam * k) + (m - 1)) / m, fun _ => false, 0⟩

/-- n ≤ lam bits: the first n bits of one block; the others are thrown away -/
def bits (n : ℕ) (h : n ≤ lam) : BS lam (Fin n → Bool) :=
  ⟨1, fun u i => u 0 ⟨i.val, lt_of_lt_of_le i.isLt h⟩, 2 ^ (lam - n), fun _ => false, 0⟩

/-- Rejection sampling with three attempts, one block each. A, R, T are numbers of blocks: at most A
blocks pass the check and give a fixed value, at most R fail the check, at most T give a fixed
value, passed or not (not asked here: hypotheses of `three_fib`, Iop/DrawProofs.lean). z, nz: given
by the caller (the sampler of a field: "the element is 0", 1). -/
def three (ok : Dig lam → Bool) (el : Dig lam → C) (A R T : ℕ) (z : C → Bool) (nz : ℕ) : BS lam C :=
  ⟨3, fun u => if ok (u 0) then el (u 0) else if ok (u 1) then el (u 1) else el (u 2),
    A * 2 ^ lam * 2 ^ lam + R * A * 2 ^ lam + R * R * T, z, nz⟩

/-- The condition on a sampler. The number of elements of C is `Nat.card`, so that the condition
depends on no instance. (`Nat.card` of an infinite type is 0, and the second clause would then hold
for free: the challenges of a round are a finite type by `Iop.Round`, and `Spec.drawsGood` below is
about their `Fintype.card`.) -/
structure Good (s : BS lam C) (κ : ℝ≥0∞) : Prop where
  fib : ∀ c, cnt (fun a : Fin s.b → Dig lam => s.φ a = c) ≤ s.w
  ratio : (s.w : ℝ≥0∞) * (Nat.card C : ℝ≥0∞) ≤ κ * (Fintype.card (Fin s.b → Dig lam) : ℝ≥0∞)

end BS

/-- One sampler for each round. -/
def Shape.Draws (lam : ℕ) : Shape → Type
  | [] => Unit
  | r :: s => BS lam r.Chal × Shape.Draws lam s

namespace Shape.Draws
variable {lam : ℕ}

def app : {s t : Shape} → s.Draws lam → t.Draws lam → Shape.Draws lam (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (a, as), b => (a, app as b)

def rep (r : Round) (h : BS lam r.Chal) :
    (n : ℕ) → {t : Shape} → t.Draws lam → Shape.Draws lam (List.replicate n r ++ t)
  | 0, _, b => b
  | n + 1, _, b => (h, rep r h n b)

/-- the largest number of blocks of a round -/
def maxB : (s : Shape) → s.Draws lam → ℕ
  | [], _ => 0
  | _ :: s, (d, ds) => max d.b (maxB s ds)

/-- the blocks of all rounds -/
def totB : (s : Shape) → s.Draws lam → ℕ
  | [], _ => 0
  | _ :: s, (d, ds) => d.b + totB s ds

/-- the blocks of round i (0 beyond the last round) -/
def bAt : (s : Shape) → s.Draws lam → ℕ → ℕ
  | [], _, _ => 0
  | _ :: _, (d, _), 0 => d.b
  | _ :: s, (_, ds), i + 1 => bAt s ds i

/-- every round with b blocks satisfies `BS.Good` with κ = κ₀^b -/
def Good (κ₀ : ℝ≥0∞) : (s : Shape) → s.Draws lam → Prop
  | [], _ => True
  | _ :: s, (d, ds) => d.Good (κ₀ ^ d.b) ∧ Good κ₀ s ds

end Shape.Draws

/-- The samplers in the form of Iop/Pull.lean. -/
def Samplers.ofDraws {lam : ℕ} : (s : Shape) → s.Draws lam → Samplers s
  | [], _ => PUnit.unit
  | _ :: s, (d, ds) => (d.sampler, Samplers.ofDraws s ds)

namespace Spec



/-- From the rounds to the list of rounds: if 1 ≤ κ₀, `Shape.Draws.Good κ₀` gives `Samplers.Good`
(what `pullPropsB` asks) with κ₀^a and κ₀^c, for every bound a on the blocks
of a round and c on the blocks of all rounds (the three protocols of a record of protocols share one
pair of numbers). -/
def drawsGood : Prop :=
  ∀ (lam : ℕ) (κ₀ : ℝ≥0∞), 1 ≤ κ₀ →
    ∀ (s : Shape) (ds : s.Draws lam), ds.Good κ₀ s →
      ∀ a c : ℕ, Shape.Draws.maxB s ds ≤ a → Shape.Draws.totB s ds ≤ c →
        (Samplers.ofDraws s ds).Good (κ₀ ^ a) (κ₀ ^ c)

end Spec

end Iop
