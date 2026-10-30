-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlJ`, `IsGlS` (Cb/Gl/GlLdJ.lean) and `IsGlCpJ` (Cb/Gl/GlCopy.lean) do not ask a radius within
half the distance.
Cb/Ld/LdBldCode.lean: this file defines the codes of the proximity test over p = 2^64 - 2^32 + 1,
interleaved Reed-Solomon codes with free parameters, and states the inequalities on these parameters
from which two predicates on codes (`GlC`, `GlJ`) follow.

Definitions and statements; the proofs are in Cb/Ld/LdBldCodeProofs.lean. Nothing is assumed in
either file beyond the hypotheses of the statements: `GlC` and `GlJ` are predicates on codes; the
statement on codes enters only where agreement is drawn from `GlJ` (Cb/Gl/GlLdJ.lean).
`GlC C d t` (Cb/Gl/GlLd.lean) says that C is made by interleaving, pairing and forming families from
plain or copied Reed-Solomon codes on subgroups of order at most 2^32, every position of each read
equally often; d is at most the distance of each as read, t at most its number r of uniform
coefficients. It is an inductive predicate ("the closure"); its leaves are the constructors base and
copy, those of `GlJ` base, sub and copy. `GlJ C d t e bad` (Cb/Gl/GlLdJ.lean) asks moreover at each
leaf: 0 < k; a radius e that is at least each multiplicity; at the leaf `GlJ.base`, that message and
randomness fill the dimension; and bad is at least the sum of the leaves' counts, one bound
`Cb.bchksBound`, rounded down, for each code of a leaf, plus `listMax` at the leaves sub and copy.

Why: the records on towers, tests and sendings over this field (Cb/GlVal/GlThird.lean,
Cb/GlVal/GlJohn.lean, Cb/Gl/GlFinal.lean) ask of each code `GlC C d t` (Cb/Gl/GlLd.lean) or
`GlJ C d t e bad` (Cb/Gl/GlLdJ.lean). Here the lengths, dimensions, messages, numbers of uniform
coefficients, radii are parameters (no value is fixed).

The three forms, all codes read under a transformation (Cb/Ld/LdRel.lean) at the long positions
`Fin (2 ^ a)`, all with rows R (R := Unit: one row):
  `rsLd a k msg r R`: the code [2^a, k + 1] (`rs`, Cb/Gl/GlCodes.lean) read as it stands:
    multiplicity 1.
  `cpLd a' a k msg r R`, copied: the short code [2^a', k + 1] written out 2^(a - a') times as one
    native word of length 2^a (`rsCp`, Cb/Gl/GlCopy.lean), for a' ≤ a ≤ 32 (`Spec.glCp_enc`,
    Cb/Gl/GlCopy.lean); nobody compares the copies.
  `repLd a' a k msg r h R` (h : a' ≤ a), native: a native word of length 2^a'; the long position x
    is read at x modulo 2^a': multiplicity 2^(a - a').
The three have the same coordinates of message, randomness and long symbol, by definition; `sgU` and
`rsLdJ`, `rsLdQ`, `rsLdA` (likewise for `cpLd`, `repLd`) number them: (row, place below msg), (row,
place below r), row.

Main names:
  `Spec.bld_rs_glC`, `Spec.bld_cp_glC`, `Spec.bld_rep_glC`: `GlC` at (d, t) from: a' ≤ a; lengths at
    most 2^32 (own length and copied: the long length 2^a; native: the short length 2^a' alone is
    asked to be at most 2^32, as the leaf asks it of the member's own length); the dimension within
    the (short) length; message and randomness within the dimension; d at most the distance as read
    (2^a - k; 2^a - 2^(a - a') k; 2^(a - a') (2^a' - k): the last two are one number,
    `Spec.bld_dist_eq`); t at most r.
  `Spec.bld_rs_glJ`: `GlJ` at (d, t, e, bad): moreover 0 < k, message and randomness fill the
    dimension, 1 ≤ e, and bad is at least the count of the statement on codes at (2^a, k, e),
    rounded down.
  `Spec.bld_rs_glS`: the same for a proper subcode (msg + r ≤ k + 1): bad is at least that count
    plus listMax 2^a d e.
  `Spec.bld_cp_glJ`: copied: moreover 0 < k, 1 ≤ e, and bad is at least the count at the long length
    (2^a, 2^(a - a') k, e) plus listMax 2^a d e. Message and randomness need not fill the dimension.
  `Spec.bld_rep_glJ`: native: moreover 0 < k; they fill the dimension; 2^(a - a') ≤ e; bad is at
    least the count at the short length (2^a', k, e / 2^(a - a')).
  `Spec.bld_in_glC`, `Spec.bld_in_glJ`: the input code of a fold = the new code of the code switch
    before it (main rows on a cube beside mask rows on a cube: `inCd C Z kk h`): from `GlC`, `GlJ`
    of its two codes at the same d, t, e; the counts add.
  `Spec.bld_john`: the Johnson condition with the number of long positions written as 2^a.
  `Spec.bld_rs_read`, `Spec.bld_rep_read`: what the codes are. For msg + r ≤ k + 1, the long symbol
    at x, row i, of an honest encoding is the value at `pts a x`, for a ≤ 32 the x-th point of the
    subgroup of order 2^a (for the native form, where a' ≤ a: at the (x modulo 2^a')-th point of the
    subgroup of order 2^a', for a' ≤ 32), of the polynomial whose coefficients are row i of the
    message, then row i of the randomness. Copied and native differ in the native word, so in what a
    cheating prover can write, and in the counts above (their long symbols: `Spec.bld_cp_read`).
  `Spec.bld_card_rs` to `Spec.bld_card_out`: the numbers of coordinates of message and randomness
    (for equivalences of coordinate types that are made from an equation between cardinalities).

Notation: `F`: the integers modulo p; `E`: the challenge field, an algebra over F (both:
Cb/Gl/GlField.lean); `cpDn a' a`: the short position under a long one (Cb/Gl/GlCopy.lean).

Limits: this file does not say that the inequalities can be met at numbers of interest.
It does not say that any count is small. `GlJ` is not monotone in d
at the leaves with a list (copied; subcode): every statement is at the d that the caller names. This
file says nothing on families with several members of different lengths in one leaf. A group's
complex is made by the closure: pair,
fam. It says nothing on cosets. The points are those of subgroups. It says nothing on lengths above
2^32. This limit is meant of native words in the statements on `GlC` and `GlJ`: the native form's
long length 2^a may be above it.
A declared difference of format (by a reading of a print of the technical report; not held against
the report's latest edition): the order of the coefficients in the encoder. Here
(Code/Iface.lean: fm; polyAt below) the message holds the lowest coefficients and the r uniform
coefficients stand above it; the technical report puts the uniform coefficients lowest and the
message above them. The same code as a set of words: the same distance, lists, agreement; both hide
r positions (this order needs points other than 0: a subgroup has none). What differs: the
generator's rows, so the rows that a code switch and the locations write down, and every transcript.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Gl.GlLdJ

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

/-! ### The three forms -/

/-- Rows R under the code [2^a, k + 1], read as it stands. -/
@[reducible] def rsLd (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] :
    LdCode E (Fin (2 ^ a)) :=
  (Reading.one (rs a k msg r 0 0)).ld E fun _ => R

/-- Copied: rows R under the short code [2^a', k + 1] written out as a native word of length 2^a
(for a' ≤ a ≤ 32: the head's row). -/
@[reducible] def cpLd (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] :
    LdCode E (Fin (2 ^ a)) :=
  (Reading.one (rsCp a' a k msg r)).ld E fun _ => R

/-- Native: rows R under the short code [2^a', k + 1], read by repetition at 2^a long positions. -/
@[reducible] def repLd (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R] :
    LdCode E (Fin (2 ^ a)) :=
  (Reading.rep (grp (fun _ : Unit => a') (fun _ => k) (fun _ => msg) fun _ => r)
      (2 ^ a) fun _ => pow_dvd_pow 2 h).ld
    E fun _ => R

/-- The input code of a fold; the new code of the code switch before it: main rows on the cube of kk
variables under C, mask rows on the cube of h variables under Z. -/
@[reducible] def inCd {P : Type} (C Z : LdCode E P) (kk h : ℕ) : LdCode E P :=
  (C.il (Fin kk → Bool)).pair (Z.il (Fin h → Bool))

/-! ### Coordinates -/

/-- a family with one member -/
def sgU (X : Type) : X ≃ (Σ _ : Unit, X) where
  toFun x := ⟨(), x⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

section Coord
variable (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R]

def rsLdJ : R × Fin msg ≃ (rsLd a k msg r R).J := sgU (R × Fin msg)
def rsLdQ : R × Fin r ≃ (rsLd a k msg r R).Q := sgU (R × Fin r)
def rsLdA : R ≃ (rsLd a k msg r R).Aa := (Equiv.prodPUnit R).symm.trans (sgU (R × Unit))
def cpLdJ : R × Fin msg ≃ (cpLd a' a k msg r R).J := sgU (R × Fin msg)
def cpLdQ : R × Fin r ≃ (cpLd a' a k msg r R).Q := sgU (R × Fin r)
def cpLdA : R ≃ (cpLd a' a k msg r R).Aa := (Equiv.prodPUnit R).symm.trans (sgU (R × Unit))
def repLdJ : R × Fin msg ≃ (repLd a' a k msg r h R).J := sgU (R × Fin msg)
def repLdQ : R × Fin r ≃ (repLd a' a k msg r h R).Q := sgU (R × Fin r)
def repLdA : R ≃ (repLd a' a k msg r h R).Aa := (Equiv.prodPUnit R).symm.trans (sgU (R × Unit))

/-- the coordinates of a long symbol are finitely many, and can be told apart (no global instances:
pass them) -/
@[reducible] def rsLdFinA : Fintype (rsLd a k msg r R).Aa :=
  inferInstanceAs (Fintype (Σ _ : Unit, R × Unit))
@[reducible] def rsLdDecA : DecidableEq (rsLd a k msg r R).Aa :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, R × Unit))
@[reducible] def cpLdFinA : Fintype (cpLd a' a k msg r R).Aa :=
  inferInstanceAs (Fintype (Σ _ : Unit, R × Unit))
@[reducible] def cpLdDecA : DecidableEq (cpLd a' a k msg r R).Aa :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, R × Unit))
@[reducible] def repLdFinA : Fintype (repLd a' a k msg r h R).Aa :=
  inferInstanceAs (Fintype (Σ _ : Unit, R × Unit))
@[reducible] def repLdDecA : DecidableEq (repLd a' a k msg r h R).Aa :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, R × Unit))

end Coord

/-- the value at z of the polynomial whose coefficients are the message, then the randomness -/
def polyAt {msg r : ℕ} (z : E) (m : Fin msg → E) (ρ : Fin r → E) : E :=
  ∑ j : Fin msg, z ^ (j : ℕ) * m j + ∑ q : Fin r, z ^ (msg + (q : ℕ)) * ρ q

namespace Spec

/-! ### GlC -/

def bld_rs_glC : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] (d t : ℕ),
    a ≤ 32 → k < 2 ^ a → msg + r ≤ k + 1 → d ≤ 2 ^ a - k → t ≤ r → GlC (rsLd a k msg r R) d t

def bld_cp_glC : Prop :=
  ∀ (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] (d t : ℕ), a' ≤ a →
    a ≤ 32 → k < 2 ^ a' → msg + r ≤ k + 1 → d ≤ 2 ^ a - 2 ^ (a - a') * k →
    t ≤ r → GlC (cpLd a' a k msg r R) d t

def bld_rep_glC : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R] (d t : ℕ), a' ≤ 32 →
    k < 2 ^ a' → msg + r ≤ k + 1 → d ≤ 2 ^ (a - a') * (2 ^ a' - k) →
    t ≤ r → GlC (repLd a' a k msg r h R) d t

/-- the two ways of writing a short code's distance as read -/
def bld_dist_eq : Prop :=
  ∀ a' a k : ℕ, a' ≤ a → 2 ^ (a - a') * (2 ^ a' - k) = 2 ^ a - 2 ^ (a - a') * k

/-! ### GlJ -/

/-- At its own length; message and randomness fill the dimension. (not all hypotheses are named
here: see the statement below) -/
def bld_rs_glJ : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] (d t e bad : ℕ), a ≤ 32 → 0 < k →
    k < 2 ^ a → msg + r = k + 1 → d ≤ 2 ^ a - k → t ≤ r → 1 ≤ e →
    ⌊Cb.bchksBound (2 ^ a) k e⌋₊ ≤ bad → GlJ (rsLd a k msg r R) d t e bad

/-- At its own length; a proper subcode is allowed; one more term. (not all hypotheses are named
here: see the statement below) -/
def bld_rs_glS : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] (d t e bad : ℕ), a ≤ 32 → 0 < k →
    k < 2 ^ a → msg + r ≤ k + 1 → d ≤ 2 ^ a - k → t ≤ r → 1 ≤ e →
    ⌊Cb.bchksBound (2 ^ a) k e⌋₊ + listMax (2 ^ a) d e ≤ bad → GlJ (rsLd a k msg r R) d t e bad

/-- Copied: the count at the long length, and one list. (not all hypotheses are named here: see the
statement below) -/
def bld_cp_glJ : Prop :=
  ∀ (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R] (d t e bad : ℕ), a' ≤ a → a ≤ 32 →
    0 < k → k < 2 ^ a' → msg + r ≤ k + 1 → d ≤ 2 ^ a - 2 ^ (a - a') * k → t ≤ r → 1 ≤ e →
     ⌊Cb.bchksBound (2 ^ a) (2 ^ (a - a') * k) e⌋₊ + listMax (2 ^ a) d e ≤ bad →
    GlJ (cpLd a' a k msg r R) d t e bad

/-- Native: the count at the short length, at the radius' share. (not all hypotheses are named here:
see the statement below) -/
def bld_rep_glJ : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R] (d t e bad : ℕ), a' ≤
      32 →
    0 < k → k < 2 ^ a' → msg + r = k + 1 → d ≤ 2 ^ (a - a') * (2 ^ a' - k) → t ≤ r →
    2 ^ (a - a') ≤ e  → ⌊Cb.bchksBound (2 ^ a') k (e / 2 ^ (a - a'))⌋₊ ≤ bad →
    GlJ (repLd a' a k msg r h R) d t e bad

/-! ### A fold's input code -/

def bld_in_glC : Prop :=
  ∀ (P : Type) [Fintype P] (C Z : LdCode E P) (kk h d t : ℕ),
    GlC C d t → GlC Z d t → GlC (inCd C Z kk h) d t

def bld_in_glJ : Prop :=
  ∀ (P : Type) [Fintype P] (C Z : LdCode E P) (kk h d t e bC bZ : ℕ),
    GlJ C d t e bC → GlJ Z d t e bZ → GlJ (inCd C Z kk h) d t e (bC + bZ)

def bld_john : Prop :=
  ∀ a d e : ℕ, InJohnson (Fintype.card (Fin (2 ^ a))) d e ↔ InJohnson (2 ^ a) d e

/-! ### What the codes are -/

def bld_rs_read : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R], msg + r ≤ k + 1 →
    ∀ (m : (rsLd a k msg r R).J → E) (ρ : (rsLd a k msg r R).Q → E) (x : Fin (2 ^ a)) (i : R),
      (rsLd a k msg r R).T ((rsLd a k msg r R).enc m ρ) x (rsLdA a k msg r R i) =
        polyAt (algebraMap F E (pts a x)) (fun j => m (rsLdJ a k msg r R (i, j)))
          fun q => ρ (rsLdQ a k msg r R (i, q))

def bld_rep_read : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R], msg + r ≤ k + 1 →
    ∀ (m : (repLd a' a k msg r h R).J → E)
        (ρ : (repLd a' a k msg r h R).Q → E) (x : Fin (2 ^ a)) (i : R),
      (repLd a' a k msg r h R).T ((repLd a' a k msg r h R).enc m ρ) x (repLdA a' a k msg r h R i) =
        polyAt (algebraMap F E (pts a' (cpDn a' a x))) (fun j => m (repLdJ a' a k msg r h R (i, j)))
          fun q => ρ (repLdQ a' a k msg r h R (i, q))

/-- Copied and native: the same long symbols for the same message and randomness
(for a' ≤ a ≤ 32). -/
def bld_cp_read : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R], a ≤ 32 →
    ∀ (m : (Σ _ : Unit, R × Fin msg) → E)
        (ρ : (Σ _ : Unit, R × Fin r) → E) (x : Fin (2 ^ a)) (α : Σ _ : Unit, R × Unit),
      (cpLd a' a k msg r R).T ((cpLd a' a k msg r R).enc m ρ) x α =
        (repLd a' a k msg r h R).T ((repLd a' a k msg r h R).enc m ρ) x α

/-! ### Numbers of coordinates -/

def bld_card_rs : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R],
    Fintype.card (rsLd a k msg r R).J = Fintype.card R * msg ∧
    Fintype.card (rsLd a k msg r R).Q = Fintype.card R * r

def bld_card_cp : Prop :=
  ∀ (a' a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R],
    Fintype.card (cpLd a' a k msg r R).J = Fintype.card R * msg ∧
    Fintype.card (cpLd a' a k msg r R).Q = Fintype.card R * r

def bld_card_rep : Prop :=
  ∀ (a' a k msg r : ℕ) (h : a' ≤ a) (R : Type) [Fintype R] [DecidableEq R],
    Fintype.card (repLd a' a k msg r h R).J = Fintype.card R * msg ∧
    Fintype.card (repLd a' a k msg r h R).Q = Fintype.card R * r

def bld_card_il : Prop :=
  ∀ (P : Type) (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R],
    Fintype.card (C.il R).J = Fintype.card R * Fintype.card C.J ∧
    Fintype.card (C.il R).Q = Fintype.card R * Fintype.card C.Q

def bld_card_pair : Prop :=
  ∀ (P : Type) (C₁ C₂ : LdCode E P),
    Fintype.card (C₁.pair C₂).J = Fintype.card C₁.J + Fintype.card C₂.J ∧
    Fintype.card (C₁.pair C₂).Q = Fintype.card C₁.Q + Fintype.card C₂.Q

/-- a fold's input code -/
def bld_card_in : Prop :=
  ∀ (P : Type) (C Z : LdCode E P) (kk h : ℕ),
    Fintype.card (inCd C Z kk h).J = 2 ^ kk * Fintype.card C.J + 2 ^ h * Fintype.card Z.J ∧
    Fintype.card (inCd C Z kk h).Q = 2 ^ kk * Fintype.card C.Q + 2 ^ h * Fintype.card Z.Q

/-- a fold's output code: the folded main row, the folded carried mask, the folded fresh mask -/
def bld_card_out : Prop :=
  ∀ (P : Type) (Y : SumPar E P),
    Fintype.card Y.Cout.J = Fintype.card Y.C.J + 2 * Fintype.card Y.Z.J ∧
    Fintype.card Y.Cout.Q = Fintype.card Y.C.Q + 2 * Fintype.card Y.Z.Q

end Spec
end Cb.Gl.Bld
