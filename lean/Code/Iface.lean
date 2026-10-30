-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Iface.lean: linear codes with an encoder, and the properties that the protocols assume.

The file defines a code with encoder (`Enc`), its properties (`Enc.Props`: (P1) distance, (P2)
mutual correlated agreement, (P3) hiding, with msg + r ≤ k and 2 e < d) and a code family
(`Family`).

Data and properties are separate: `Enc` and `Family` hold data only, so that the protocols can be
defined before anything is proved; `Enc.Props` is what Code/RS.lean and Code/Circle.lean prove of
their codes, under hypotheses, and what the protocols assume (some assume other properties of a
code: see `LdCf.OK`, Cb/Obj/LdObjectConf.lean). Errors are counts of bad values of θ in E. The cost
of a row of the generator is left out.

Notation: F, E: fields, E an algebra over F (`[Algebra F E]`; Code/Facts.lean's head: F is the field
of the code and E an extension field of F); θ: an element of E, the coefficient of f₁ in f₀ + θ f₁
(`Enc.MCA`); `cnt P` (`Prob.cnt`, Prob/Cnt.lean): a natural number, the number of elements of a
finite type with the property P.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Probability.Distributions.Uniform
import Prob.Cnt

namespace Code
open Prob

/-- A code with encoder: the data. The generator matrix has n rows (positions) and k columns. The
encoder applies it to a vector that holds the message at the first msg places, then r uniform
coordinates, then zeros. -/
structure Enc (F : Type) where
  n : ℕ
  k : ℕ
  msg : ℕ
  r : ℕ
  G : Matrix (Fin n) (Fin k) F
  /-- distance; proximity parameter in positions; number of hidden positions; count of bad θ -/
  d : ℕ
  e : ℕ
  b : ℕ
  mca : ℕ

variable {F : Type} [Field F]

/-- The full input of the generator over any field K: message, randomness, zeros. -/
def Enc.fm (C : Enc F) {K : Type} [Zero K] (m : Fin C.msg → K) (ρ : Fin C.r → K) : Fin C.k → K :=
  fun i => if h : i.val < C.msg then m ⟨i.val, h⟩
    else if h' : i.val - C.msg < C.r then ρ ⟨i.val - C.msg, h'⟩ else 0

/-- The generator over an extension field. -/
def Enc.GE (C : Enc F) (E : Type) [Field E] [Algebra F E] : Matrix (Fin C.n) (Fin C.k) E :=
  C.G.map (algebraMap F E)

/-- The encoding of the message m under the randomness ρ, over F. -/
def Enc.enc (C : Enc F) (m : Fin C.msg → F) (ρ : Fin C.r → F) : Fin C.n → F := C.G.mulVec (C.fm m ρ)

/-- `Enc.enc` over E. -/
def Enc.encE (C : Enc F) (E : Type) [Field E] [Algebra F E] (m : Fin C.msg → E) (ρ : Fin C.r → E) :
    Fin C.n → E :=
  (C.GE E).mulVec (C.fm m ρ)

/-- The rows of the interleaved word f (rows indexed by R, over E) agree with codewords on the set S
of positions.
A codeword is the image of any vector of length k. -/
def Enc.OnCode (C : Enc F) (E : Type) [Field E] [Algebra F E] {R : Type}
    (f : R → Fin C.n → E) (S : Finset (Fin C.n)) : Prop :=
  ∃ M : R → Fin C.k → E, ∀ j ∈ S, ∀ a, f a j = (C.GE E).mulVec (M a) j

/-- (P2) Mutual correlated agreement on lines, for any number of rows, as a count:
at most bad values of θ admit a set of at least n - e positions on which f₀ + θ f₁ agrees with a
codeword while f₀ and f₁ do not both. -/
def Enc.MCA (C : Enc F) (E : Type) [Field E] [Finite E] [Algebra F E] (e bad : ℕ) : Prop :=
  ∀ (R : Type) [Finite R] (f₀ f₁ : R → Fin C.n → E),
    cnt (fun θ : E => ∃ S : Finset (Fin C.n), C.n ≤ S.card + e ∧
      C.OnCode E (fun a j => f₀ a j + θ * f₁ a j) S ∧ ¬ (C.OnCode E f₀ S ∧ C.OnCode E f₁ S)) ≤ bad

/-- The properties of a code with encoder. -/
structure Enc.Props (C : Enc F) [Fintype F] (E : Type) [Field E] [Finite E] [Algebra F E] :
    Prop where
  place  : C.msg + C.r ≤ C.k
  /-- (P1) a non-zero vector has an image of weight at least d -/
  dist   : ∀ v : Fin C.k → F, v ≠ 0 → C.d ≤ cnt (fun j => C.G.mulVec v j ≠ 0)
  /-- unique decoding -/
  unique : 2 * C.e < C.d
  /-- (P2) -/
  mca    : C.MCA E C.e C.mca
  /-- (P3) any b positions of an encoding are uniform, for every message -/
  hides  : ∀ (S : Finset (Fin C.n)), S.card ≤ C.b →
    ∀ m : Fin C.msg → F,
      (PMF.uniformOfFintype (Fin C.r → F)).map (fun ρ => fun j : S => C.enc m ρ j) =
        PMF.uniformOfFintype (S → F)

/-- A code family: the data: one code for each kind of vector that the protocols send. -/
structure Family (F : Type) where
  Kind : Type
  [finKind : Fintype Kind]
  [decKind : DecidableEq Kind]
  enc : Kind → Enc F
  /-- is a vector of this kind over E (else over F) -/
  overE : Kind → Bool
  /-- number of stripes of a vector of this kind: the rows of the interleaved word: a vector of kind
  Z is cut into `stripes Z` rows of `(enc Z).msg` entries -/
  stripes : Kind → ℕ
  /-- `q`: positions that one run reads in a vector of this kind; `a`: the number of runs that read
  it. (A run is one use of a sub-protocol that checks a list of linear claims on encoded
  vectors.) -/
  q : Kind → ℕ
  a : Kind → ℕ
  /-- `idx`: the kind of the encoded index; `qT`, `qon`, `qpar`, `qch`: the numbers of positions
  that the three protocols read in it: Test, Batch, and Link in its two strings, parent and child
  -/
  idx : Kind
  qT : ℕ
  qon : ℕ
  qpar : ℕ
  qch : ℕ

/-- All codes of the family have the properties. -/
def Family.Props (𝒞 : Family F) [Fintype F] (E : Type) [Field E] [Finite E] [Algebra F E] : Prop :=
  ∀ Z, (𝒞.enc Z).Props E

end Code
