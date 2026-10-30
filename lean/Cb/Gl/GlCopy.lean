-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlCpJ` does not ask a radius within half the distance; nor do `IsGlJ`, `IsGlS` in
Cb/Gl/GlLdJ.lean.
Cb/Gl/GlCopy.lean: the c-fold repetition of a short Reed-Solomon code over p = 2^64 - 2^32 + 1, as a
code of its own and as a subcode of a long Reed-Solomon code.

Exactly: copied rows: a short plain Reed-Solomon code whose codewords are written out c times as one
long native word, the copies not compared by anybody: the code, two predicates "this code is a
family of such", and what they give.

Definitions and statements; the proofs are in Cb/Gl/GlCopyProofs.lean. Nothing assumed in this file
beyond the hypotheses of the statements.

Why: in this protocol's technical report (lean/CREDITS.md) a mask row has one of two forms, a public
parameter. Native: a short word, read by repetition (Cb/Gl/GlLd.lean, Cb/Gl/GlLdJ.lean have that: a
reading with a
multiplicity). Copied: a long word; the honest prover writes the short codeword c times; a cheating
prover may write anything. The code is then the repetition of the short code: a subcode of a long
Reed-Solomon code (the polynomials in X^c). The report's reference parameters copy all mask
rows but three.

Main names (each statement under the hypotheses of its statement; c = 2^(b - a)):
  `rsCp a b k msg r`: the code (a ≤ b ≤ 32): length 2^b, dimension k + 1; as data: distance
    2^b - c k = c (2^a - k), r uniform coordinates. c = 1 (a = b) is allowed.
  `Spec.glCp_enc`: it is the repetition of the short code (rs a k msg r: Cb/Gl/GlCodes.lean).
  `Spec.glCp_dist`: for a ≤ b ≤ 32, k < 2^a: the distance.
  `IsGlCp C d t`: C is T.ld E R (Cb/Ld/LdRelRep.lean) for a reading T of a finite family of such
    codes with k i < 2^(a i), msg i + r i ≤ k i + 1, each with rows, read evenly at the long
    positions P; d at most mult i · (2^(b i) - c i · k i); t at most r i.
  `Spec.glCp_code`: `IsGlCp C d t` gives: laws, transparent, reads what it declares, distance d as
    read, zero knowledge of the encoding at t long positions.
  `IsGlCpJ C d t e bad`: the same with 0 < k i, mult i ≤ e, and: bad is at least the sum of the
    counts of the statement on codes at the long lengths (2^(b i), c i · k i, e / mult i), each
    rounded down, plus listMax |P| d e.
  `Spec.glCp_sub`: the family of copied codes is a subcode (Cb/Ld/LdRelSub.lean: `SubOf`) of the
    family of the long codes rs (b i) (c i · k i) (Cb/Gl/GlCodes.lean) whose message fills the
    dimension, under the same reading, with the same rows.
The closures `GlC` (Cb/Gl/GlLd.lean) and `GlJ` (Cb/Gl/GlLdJ.lean) have `IsGlCp`, `IsGlCpJ` as
leaves (the constructors `copy`): so every record that requires `GlC` or
`GlJ` of a code admits copied rows, alone or side by side with native ones.

On hiding, plainly. A copied code does not have "any r positions of an encoding are uniform" (the
clause "hides" of `Code.Enc.Core`, Cb/Gen/CodeList.lean): two copies of one short position hold the
same symbol. Under `IsGlCp C d t` (so t ≤ r i: `Spec.glCp_code`): what it has is the notion that the
blocks ask (`LdCode.Zk t`, Cb/Ld/LdRel.lean): the law of what is read at any t long positions does
not depend on the message, error 0. It follows from the short code's: t long positions lie over at
most t short ones.

How it compares with the report, by inspection: the long code, the bound, the count of hidden
positions in long positions are the report's. Narrower: the short domain is a subgroup (there:
a coset); the copy map is "modulo the short length" (there: any map with fibres of c elements; the
even reading can take a renumbering). Wider: message and randomness need not fill the dimension.

Notation: `F`: the integers modulo p (Cb/Gl/GlField.lean); `E`: the challenge field
(Cb/Gl/GlField.lean); `T`: a reading (`Reading`, Cb/Gen/CodeRep.lean): the data P, pos and mult;
`mult i`: how often a position of the component i is read; even (`Reading.Even`): every position of
i is read exactly mult i > 0 times; `R i`: the rows of component i; `T.ld E R`: the family as one
code read under a transformation (Cb/Ld/LdRelRep.lean).

Limits: agreement is not in this file: Cb/Gl/GlCopyJ.lean (through `Cb.ld_sub_rows`: the whole
code's count plus one list). Within a third of the distance nothing is needed: agreement follows
from laws and distance for every code. Copied rows inside an object: not at a guard in this file.

This file does not say that the counts are small. It
says nothing on lengths above 2^32, but for `Spec.glCp_sub`, which has no bound on b i. It does not
say that a copied row stands in the main rows' tree at the compiler: a matter of format, not
touched.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlCodesLd
import Cb.Ld.LdRelSub
import Cb.Ld.LdRelJohnson
import Cb.Ld.LdSwitch
import Cb.Ld.LdSig

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

/-- The short code [2^a, k + 1], copied to the length 2^b. -/
@[reducible] def rsCp (a b k msg r : ℕ) : Code.Enc F where
  n := 2 ^ b
  k := k + 1
  msg := msg
  r := r
  G := Matrix.of fun j i => pts b j ^ (2 ^ (b - a) * (i : ℕ))
  d := 2 ^ b - 2 ^ (b - a) * k
  e := 0
  b := r
  mca := 0

/-- a family of such codes -/
@[reducible] def grpCp {A : Type} (a b k msg r : A → ℕ) : A → Code.Enc F := fun i =>
  rsCp (a i) (b i) (k i) (msg i) (r i)

/-- the short position under a long one -/
def cpDn (a b : ℕ) (j : Fin (2 ^ b)) : Fin (2 ^ a) :=
  ⟨(j : ℕ) % 2 ^ a, Nat.mod_lt _ (pow_pos (by norm_num) a)⟩

/-- C is a family of copied plain Reed-Solomon codes, with rows, read evenly. -/
def IsGlCp {P : Type} [Fintype P] (C : LdCode E P) (d t : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (a b k msg r : A → ℕ)
      (pos : ∀ i, P → Fin (2 ^ b i)) (mult : A → ℕ) (R : A → Type)
      (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i)),
    C = (⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).ld E R ∧
    (∀ i, a i ≤ b i) ∧ (∀ i, b i ≤ 32) ∧
    (∀ i, k i < 2 ^ a i) ∧
    (∀ i, msg i + r i ≤ k i + 1) ∧
    (⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).Even ∧
    (∀ i, d ≤ mult i * (2 ^ b i - 2 ^ (b i - a i) * k i)) ∧
    ∀ i, t ≤ r i

/-- The same, with 0 < k i, mult i ≤ e, and with the numbers for agreement below the Johnson radius:
the counts of the statement on codes at the long lengths, and one list. -/
def IsGlCpJ {P : Type} [Fintype P] (C : LdCode E P) (d t e bad : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (a b k msg r : A → ℕ)
    (pos : ∀ i, P → Fin (2 ^ b i)) (mult : A → ℕ) (R : A → Type)
    (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i)),
    C = (⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).ld E R ∧ (∀ i, a i ≤ b i) ∧ (∀ i, b i ≤ 32) ∧
    (∀ i, 0 < k i) ∧ (∀ i, k i < 2 ^ a i) ∧ (∀ i, msg i + r i ≤ k i + 1) ∧
    (⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).Even ∧ (∀ i, d ≤ mult i * (2 ^ b i - 2 ^ (b i - a i) * k i)) ∧ (∀ i, t ≤ r i) ∧ (∀ i, mult i ≤ e)  ∧
    ∑ i, ⌊Cb.bchksBound (2 ^ b i) (2 ^ (b i - a i) * k i) (e / mult i)⌋₊ +
        listMax (Fintype.card P) d e ≤ bad

namespace Spec

/-- For a ≤ b ≤ 32 it is the repetition of the short code. -/
def glCp_enc : Prop :=
  ∀ (a b k msg r : ℕ), a ≤ b → b ≤ 32 →
    ∀ (m : Fin msg → E) (ρ : Fin r → E) (j : Fin (2 ^ b)),
      (rsCp a b k msg r).encE E m ρ j = (rs a k msg r 0 0).encE E m ρ (cpDn a b j)

def glCp_dist : Prop :=
  ∀ (a b k msg r : ℕ),
    a ≤ b → b ≤ 32 → k < 2 ^ a → HasDist (rsCp a b k msg r).G (rsCp a b k msg r).d

/-- What the blocks ask of a code. -/
def glCp_code : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t : ℕ),
    IsGlCp C d t → C.Laws ∧ C.Transparent ∧ C.Reads ∧ C.Dist d ∧ C.Zk t

def glCp_mono : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t d' t' : ℕ),
    IsGlCp C d t → d' ≤ d → t' ≤ t → IsGlCp C d' t'

def glCp_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t : ℕ) (pos' : P' → P) (m : ℕ),
    IsGlCp C d t → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) → IsGlCp (C.atPos pos') (m * d) t

def glCpJ_cp : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ), IsGlCpJ C d t e bad → IsGlCp C d t

def glCpJ_mono : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad t' : ℕ),
    IsGlCpJ C d t e bad → t' ≤ t → IsGlCpJ C d t' e bad

/-- A subcode of the family of the long codes. -/
def glCp_sub : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (a b k msg r : A → ℕ) (P : Type)
      [Fintype P] (pos : ∀ i, P → Fin (2 ^ b i)) (mult : A → ℕ) (R : A → Type)
      [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)],
    ((⟨P, pos, mult⟩ : Reading
          (grp b (fun i => 2 ^ (b i - a i) * k i)
            (fun i => 2 ^ (b i - a i) * k i + 1) fun _ => 0)).ld
        E R).SubOf
      ((⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).ld E R) fun α => α

end Spec
end Cb.Gl
