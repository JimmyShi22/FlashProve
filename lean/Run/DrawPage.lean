-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawPage.lean: the format's draws as readers of a row of machine words, a round's draws as one
block sampler, and, under the hypotheses below, its bias: 1 + 2^-128 a block, in both fields.

This file is about how one round's verifier message is made from blocks of 256 bits by the format's
rules of drawing, and how much more often than its even share a value can come. Definitions and
statements (each a `Prop` in `Run.Spec`); the proofs are in Run/DrawPageProofs.lean.
A reader (`Tr W C`, Run/DrawRow.lean) makes a value from the next words of a row. Its law
`Tr.Good d t K w κ`: t asks for at most K words, every value has at most w rows of K words, and
w · |C| ≤ κ · |W|^K.
A block sampler (`Iop.BS`, Iop/Draw.lean) is a function from b blocks to the values, with a bound
on its fibres. Under its law `BS.Good s κ` one value of a finite type of values takes at most κ
times its even share of all tuples of b blocks: κ bounds the bias.
This file uses Run/DrawRow.lean (readers as trees, the law `Tr.Good`), Run/DrawWord.lean (one word:
the try, the low bits), Run/DrawCount.lean (a reader after a reader), Run/DrawCountNum.lean (the
readers `trF`, `trE`, `trNZ`, `trOne`, `trMany` for arbitrary parameters, their laws, the numerals'
facts), Run/DrawBS.lean (words and blocks), Fmt/Rules6.lean (`Fmt.Draw`: a round's draws as data;
`Draw.most`: the most words of a draw).

The values (`DVal f d`): finite types, so that "uniform" has a meaning:
  `elem`: an element of the extension field: three numbers below p.
  `elemNZ`: such a triple other than (0, 0, 0).
  `pos k`: a number below 2^k.
  `trits n`: n pairs of bits. (An entry of the matrix is a function of its pair: 0 if the first bit
    is 0, else 1 or -1 by the second. The pairs are uniform; the entries are not, and are not meant
    to be.)
  `sealed`: four words.
The readers (`tree f d`):
  `elem`: three times "at most six tries, a word each; then 0".
  `elemNZ`: at most two of these triples; the first that is not 0; then (1, 0, 0).
  `pos k`: the low k bits of one word.
  `trits n`: one word for each run of 32 pairs; pair j of a run is the bits 2 j, 2 j + 1 of its
    word; what is left of the last word is dropped.
  `sealed`: four words.
  `all f ds`: the draws of a list, one after the other, each on what the draws before it have left;
    `Vals f ds`: their values.
The numbers: `Draw.most` (18, 36, 1, ⌈n / 32⌉, 4) and `mostAll` are those of Fmt/Rules6.lean;
`ex d`: 3, 3, 0, 0, 0; `wt f d`: a bound on the number of rows with one value, in closed form
(`w0`, `wN` of Run/DrawCountNum.lean at the field's two numbers: words that give one value, words
that fail).

Main names:
  `Lawful d`: a position has at most 64 bits.
  `Spec.drawPage_one`: for each field and each draw with `Lawful d`:
    `Tr.Good 0 (tree f d) d.most (wt f d) (kapSl 128 ^ ex d)`, and 4 · ex d ≤ d.most.
  `Spec.drawPage_all`: the same for a list of draws that all have `Lawful`, with the sums and the
    product.
  `bsOf f ds`: the block sampler of a round: ⌈mostAll ds / 4⌉ blocks of 256 bits.
  `Spec.drawPage_bs`: for such a list of draws: `(bsOf f ds).Good (kapSl 128 ^ b)`, b its number
    of blocks: the clause of `Iop.Shape.Draws.Good` at κ₀ = 1 + 2^-128 = `Iop.kapSl 128`; and b is
    `Fmt.blocksFor (Fmt.mostAll ds)`.

Limits: this file does not say that these readers are the functions on bytes that run:
Run/DrawTie.lean (there: on machine words; on the blocks' bytes: `Spec.bs_bytes`,
Run/ToyChalLaw.lean). It says nothing on the least κ₀ (it is smaller in both fields).
What is handed on from the drawn positions (the draws in the order drawn, repeats kept; the set in
increasing order) are functions of this sampler's value, the tuple of draws, and no part of the
sampler.
The field elements among the values are triples of numbers below p: the protocols that are made
from a plan at the choice `ck f` take the values themselves as their verifier messages
(Run/PlanDrawsQ.lean: "challenges as sampled values"); a bijection to a field's own type
(`Iop.BS.map` along a bijection: no bias) is not made here.
This file does not say which draws a round of a protocol has.
-/
import Run.DrawWord
import Run.DrawCountNum

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

section
variable (f : _root_.Fmt.Fld)

theorem one_lt_p : 1 < f.p := by cases f <;> decide

/-- an element of the extension field: its three coordinates -/
abbrev EV : Type := FV f × FV f × FV f

def zF : FV f := ⟨0, p_pos f⟩
/-- the elements other than 0 -/
abbrev NZ : Type := {e : EV f // e ≠ (zF f, zF f, zF f)}
/-- The element 1 = (1, 0, 0), as an element other than 0. -/
def oE : NZ f :=
  ⟨(⟨1, one_lt_p f⟩, zF f, zF f),
    fun h => absurd (congrArg (fun e : EV f => e.1.val) h) (by show (1 : ℕ) ≠ 0; decide)⟩

end

/-- pair j of n pairs of bits, 32 to a word -/
def bitsOf (n : ℕ) (ws : Fin ((n + 31) / 32) → UInt64) (j : Fin n) : Bool × Bool :=
  ((ws ⟨j.val / 32, by omega⟩).toNat.testBit (2 * (j.val % 32)),
    (ws ⟨j.val / 32, by omega⟩).toNat.testBit (2 * (j.val % 32) + 1))

/-- the values of a draw -/
def DVal (f : _root_.Fmt.Fld) : _root_.Fmt.Draw → Type
  | .elem => EV f
  | .elemNZ => NZ f
  | .pos k => Fin (2 ^ k)
  | .trits n => Fin n → Bool × Bool
  | .sealed => Fin 4 → UInt64

/-- The reader of a draw. -/
def tree (f : _root_.Fmt.Fld) : (d : _root_.Fmt.Draw) → Tr UInt64 (DVal f d)
  | .elem => trE (okF f) (zF f)
  | .elemNZ => trNZ (okF f) (zF f) (oE f)
  | .pos k => trOne (low k)
  | .trits n => trMany ((n + 31) / 32) (bitsOf n)
  | .sealed => trMany 4 id

/-- the values of a list of draws -/
def Vals (f : _root_.Fmt.Fld) : List _root_.Fmt.Draw → Type
  | [] => Unit
  | d :: ds => DVal f d × Vals f ds

/-- A round's draws, one after the other. -/
def all (f : _root_.Fmt.Fld) : (ds : List _root_.Fmt.Draw) → Tr UInt64 (Vals f ds)
  | [] => Tr.ret ()
  | d :: ds => (tree f d).pair (all f ds)

/-- a position has at most 64 bits -/
def Lawful : _root_.Fmt.Draw → Prop
  | .pos k => k ≤ 64
  | _ => True

/-- the words that fail; the words that give one value -/
def nFail : _root_.Fmt.Fld → ℕ
  | .one => 8
  | .two => 2 ^ 32 - 1
def nGive : _root_.Fmt.Fld → ℕ
  | .one => 8
  | .two => 1

/-- A bound on the rows with one value. -/
def wt (f : _root_.Fmt.Fld) : _root_.Fmt.Draw → ℕ
  | .elem => w0 (nGive f) (nFail f) (2 ^ 64) ^ 3
  | .elemNZ => wN (nGive f) (nFail f) (2 ^ 64)
  | .pos k => 2 ^ (64 - k)
  | .trits n => 2 ^ (64 * ((n + 31) / 32) - 2 * n)
  | .sealed => 1

/-- the exponent of the bias -/
def ex : _root_.Fmt.Draw → ℕ
  | .elem => 3
  | .elemNZ => 3
  | _ => 0

def wtAll (f : _root_.Fmt.Fld) : List _root_.Fmt.Draw → ℕ
  | [] => 1
  | d :: ds => wt f d * wtAll f ds
def exAll : List _root_.Fmt.Draw → ℕ
  | [] => 0
  | d :: ds => ex d + exAll ds

/-- The block sampler of a round. -/
def bsOf (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) : BS 256 (Vals f ds) :=
  toBS e64 0 (all f ds) (_root_.Fmt.mostAll ds) (wtAll f ds)

namespace Spec

def drawPage_one : Prop :=
  ∀ (f : _root_.Fmt.Fld) (d : _root_.Fmt.Draw),
    Lawful d → (tree f d).Good 0 d.most (wt f d) (kapSl 128 ^ ex d) ∧ 4 * ex d ≤ d.most

def drawPage_all : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw), (∀ d ∈ ds, Lawful d) →
    (all f ds).Good 0 (_root_.Fmt.mostAll ds) (wtAll f ds) (kapSl 128 ^ exAll ds) ∧
    4 * exAll ds ≤ _root_.Fmt.mostAll ds

/-- The bias of a round. -/
def drawPage_bs : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw), (∀ d ∈ ds, Lawful d) →
    (bsOf f ds).Good (kapSl 128 ^ (bsOf f ds).b) ∧
    (bsOf f ds).b = _root_.Fmt.blocksFor (_root_.Fmt.mostAll ds)

end Spec
end Run
