-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Ld/LdBldCodeAt.lean: `GlJ` along a reading at other positions: a code
built from plain Reed-Solomon families, read at other long positions, each old position m times, 0 <
m, is again such a code, at m times the distance and m times the radius, with the same count.

Statements (in `Cb.Gl.Bld.Spec`); the proofs are in Cb/Ld/LdBldCodeAtProofs.lean. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A code `C : LdCode E P` (Cb/Ld/LdRel.lean) is read at the long positions P (its transformation `C.T`
takes a native word to a long word, with a symbol at each long position); `C.atPos pos'`
(Cb/Ld/LdSig.lean) is the same code read at other long positions P': the position x is read where
pos' x was. `GlJ C d t e bad` (Cb/Gl/GlLdJ.lean) is the closure, under interleaving, pairs, families
and a larger count, of three kinds of leaves (`IsGlJ`, `IsGlS`, `IsGlCpJ`); d stands for a distance,
e for a radius, bad for the count. Statements that have `GlJ` among their hypotheses:
Cb/Gl/GlLdJ.lean: `Spec.glJ_glC`, `Spec.glJ_list`, `Spec.glJ_mca`.

Why: one word can be read at several sets of long positions: a member of a group is read at the
group's long positions. Cb/Gl/GlLd.lean carries `GlC` along `atPos` (`glC_atPos`); this file
carries `GlJ`.

Main names:
  `Spec.bld_card_atPos`: if every old position is read m times, there are m times as many new
    positions.
  `Spec.bld_listMax_mul`: the Johnson bound on the list does not change when length, distance and
    radius are multiplied by m > 0. `Spec.bld_john_mul`: nor does the Johnson condition.
  `Spec.bld_isGlJ_atPos`, `Spec.bld_isGlS_atPos`, `Spec.bld_isGlCpJ_atPos`: the three kinds of
    leaves, for 0 < m and every old position read m times: the multiplicities are multiplied by m,
    so each component's share of the radius, (m e) / (m mult), is the old one, and so is the
    count of the statement on codes; the list term is the old one by `bld_card_atPos` and
    `bld_listMax_mul`.
  `Spec.bld_glJ_atPos`: the closure: `GlJ C d t e bad`, 0 < m, every old position read m times ⇒
    `GlJ (C.atPos pos') (m d) t (m e) bad`.

Notation: `E`: the challenge field (Cb/Gl/GlField.lean).

Limits: this file says nothing on radii that are no multiples of m (at a leaf without a list any e'
with the same shares would do; at a leaf with a list the term is read at e' itself), and nothing on
readings that are not even.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlLdJ

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

namespace Spec

def bld_card_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (pos' : P' → P) (m : ℕ),
    (∀ y, cnt (fun x => pos' x = y) = m) → Fintype.card P' = m * Fintype.card P

def bld_listMax_mul : Prop := ∀ m n d e : ℕ, 0 < m → listMax (m * n) (m * d) (m * e) = listMax n d e

def bld_john_mul : Prop :=
  ∀ m n d e : ℕ, 0 < m → (InJohnson (m * n) (m * d) (m * e) ↔ InJohnson n d e)

def bld_isGlJ_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t e bad : ℕ) (pos' : P' → P) (m : ℕ),
    IsGlJ C d t e bad → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    IsGlJ (C.atPos pos') (m * d) t (m * e) bad

def bld_isGlS_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t e bad : ℕ) (pos' : P' → P) (m : ℕ),
    IsGlS C d t e bad → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    IsGlS (C.atPos pos') (m * d) t (m * e) bad

def bld_isGlCpJ_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t e bad : ℕ) (pos' : P' → P) (m : ℕ),
    IsGlCpJ C d t e bad → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    IsGlCpJ (C.atPos pos') (m * d) t (m * e) bad

/-- The closure, read at other long positions. -/
def bld_glJ_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t e bad : ℕ) (pos' : P' → P) (m : ℕ),
    GlJ C d t e bad → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) →
    GlJ (C.atPos pos') (m * d) t (m * e) bad

end Spec

end Cb.Gl.Bld
