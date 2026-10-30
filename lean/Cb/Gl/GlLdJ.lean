-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlJ` and `IsGlS`, and `IsGlCpJ` (Cb/Gl/GlCopy.lean), do not ask a radius within half the
distance. `Gl.AgreeJ` (Cb/Gl/GlFinalAg.lean) is proved nowhere in this library: it follows from the
statement on codes `Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, same file). This file's own
statements on agreement have the premise `Cb.BCHKS46F F`, which this file does not prove.
Cb/Gl/GlLdJ.lean: a predicate on codes built from interleaved Reed-Solomon codes with evaluation
points in the prime field of p = 2^64 - 2^32 + 1 and symbols in its cubic extension `E`, with a
radius and a count of exceptional values: list sizes by the Johnson bound, mutual correlated
agreement under a named hypothesis.

Exactly: below the Johnson radius: a predicate on codes read under a transformation, which says
"this code is built from families of plain Reed-Solomon codes whose message and randomness fill the
dimension, or lie within it, or of copied such codes"; for such codes, lists are bounded by the
proved Johnson bound, and agreement follows from the one hypothesis BCHKS46F F.

Definitions and statements (in `Cb.Gl.Spec`); the proofs are in Cb/Gl/GlLdJProofs.lean.
For radii beyond a third of the distance, where agreement does not follow from laws and
distance.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (each statement under the hypotheses of its statement):
  `IsGlJ C d t e bad`: C is T.ld E R for a finite family of plain Reed-Solomon codes on subgroups of
    orders 2^(a i) ≤ 2^32, of dimensions k i + 1 with 0 < k i < 2^(a i), msg i + r i = k i + 1, with
    rows R i, read evenly at the long positions P (every position of component i is read mult i
    times); d ≤ mult i · (2^(a i) - k i); t ≤ r i; mult i ≤ e (the share e / mult i of each
    component is at least 1: the statement on codes (`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean) speaks
    of positive radii); bad is at least the sum over i of that statement's count at (2^(a i), k i, e
    / mult i), each rounded down.
  `IsGlS C d t e bad`: the same with msg i + r i ≤ k i + 1 (a proper subcode is allowed), at the
    price of one more term: bad is at least that sum plus listMax |P| d e (the list of two rows of
    the whole codes).
  `GlJ C d t e bad`: the closure of both under interleaving (the same bad: rows cost nothing), pairs
    (b₁ + b₂) and complexes (the sum; there t = 0); a larger count is a count too (`up`). The codes
    at the joints of a tower, a fold's stage complexes, a group's complex are of this kind. The
    closure has three kinds of leaf (a constructor without a `GlJ` premise): `base` (`IsGlJ`), `sub`
    (`IsGlS`) and `copy`: families of copied plain Reed-Solomon codes (`IsGlCpJ`,
    Cb/Gl/GlCopy.lean). For copied families: bad is at least the sum of the assumed statement's
    (`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean) counts at the long lengths plus listMax |P| d e; their
    agreement comes through the lemma on subcodes (Cb/Gl/GlCopyJ.lean).
  `Spec.glJ_glC`: `GlJ C d t e bad` ⇒ `GlC C d t`: so laws, transparent, reads what it declares,
    distance d as read, zero knowledge of the encoding at t long positions (Cb/Gl/GlLd.lean:
    `glC_code`).
  `Spec.glJ_list`: nothing assumed beyond the hypotheses of its statement (no `Cb.BCHKS46F`): from
    `GlJ C d t e bad` and e below the Johnson radius as read (InJohnson |P| d e): C, and `C.il R`
    for every R, have lists of at most listMax |P| d e members.
  **Spec.glJ_mca** **UNDER BCHKS46F F, BY NAME** (Cb/Gen/CodeListRSF.lean: a statement of Cryptology
  ePrint Archive 2025/2055 (Theorem 4.6), which gives an outline of a proof; taken as a named
  hypothesis, for the finite extensions of F and points in F only; not an axiom): the same e:
  C.MCArows e bad (Cb/Ld/LdRelRows.lean): (C.il R).MCAat e bad FOR EVERY R; so C.MCAat e bad
    (The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
  `Spec.glJ_mono`: smaller t (a larger count: the constructor up. Not a smaller d: `IsGlS`'s term
    listMax |P| d e is read at d).
  `Spec.glJ_errOK`: under BCHKS46F F: a fold: lists and agreement at all its stages (`SumPar.ErrOK`)
    from `GlJ` of its three codes and InJohnson |P| d e: one lemma for Y.C.il, Y.Z.il, Y.Zw.il and
    the stage complexes.
  `Spec.glJ_base`: under BCHKS46F F: the base case's hypotheses (`LdJoint.BaseHyp`) from `GlJ` of
    its code, InJohnson |P| d e and e < d.
  `Spec.glJ_one`: the predicate is not empty: for a ≤ 32, 0 < k < 2^a, msg + r = k + 1: one code
    read as it stands, any rows, any radius e ≥ 1.

Why `IsGlS`: a code read under a transformation has as its codewords the encodings of (message,
randomness): for msg + r < k + 1 a proper subcode of the Reed-Solomon code (the top coefficients are
0). The statement on codes (`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean) speaks of the whole code, and
agreement does not pass to subcodes by itself. Cb/Ld/LdRelSub.lean (stated there, proved in
Cb/Ld/LdRelSubProofs.lean; generic; under the hypotheses of its statement): the subcode has at most
(the whole code's count) + (the list of two rows of the whole code) exceptional values; below the
Johnson radius that list is at most listMax |P| d e, whatever the rows. Hence `IsGlS`. Where message
and randomness fill the dimension (`IsGlJ`) the term listMax |P| d e does not appear; in a copied
family (`IsGlCpJ`, Cb/Gl/GlCopy.lean) it does.
The write-up's rule for a group with mask rows of both forms is "the repetition stands for
all its mask rows"; this closure lets a native member and a copied member stand side by side, each
with its own count (pair, fam): by reading, at most the write-up's number.

Limits:
Whether the source proves what it states (BCHKS46F F is a case of it): the heads of
Cb/Gen/CodeListRS.lean, Cb/Gen/CodeListRSF.lean; this file does not say it. Not said either: that
its count is below the size of a field of interest. This file says nothing on re-reading at other
long positions (atPos): the reading in `IsGlJ` is any even reading, so a member of a group can be
given at the group's positions; no lemma carries `GlJ` along atPos in this file;
`Cb.Gl.Bld.Spec.bld_glJ_atPos` (Cb/Ld/LdBldCodeAt.lean; proved in Cb/Ld/LdBldCodeAtProofs.lean)
does, for a map that takes each old position m > 0 times, at m d and m e. It says nothing on lengths
above 2^32. Dimension 1 is outside (0 < k i is asked: polynomials of degree at most k i, k i at
least 1). No leaf asks a radius within half the distance. Nothing is said between the Johnson radius
and capacity. Copied rows inside an object: not at a guard in this file.



Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlLd
import Cb.Gen.CodeListRSF
import Cb.Ld.LdRelRows
import Cb.Ld.LdRelSub
import Cb.Ld.LdRelJohnson
import Cb.Ld.LdSum
import Cb.Ld.LdTower

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

/-- C is a family of plain Reed-Solomon codes over the prime 2^64 - 2^32 + 1 whose message and
randomness fill the dimension, with rows, read evenly; the numbers of the statement on codes
(`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean). -/
def IsGlJ {P : Type} [Fintype P] (C : LdCode E P) (d t e bad : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (a k msg r : A → ℕ)
    (pos : ∀ i, P → Fin (2 ^ a i)) (mult : A → ℕ) (R : A → Type)
    (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i)),
    C = (⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R ∧ (∀ i, a i ≤ 32) ∧ (∀ i, 0 < k i) ∧
    (∀ i, k i < 2 ^ a i) ∧ (∀ i, msg i + r i = k i + 1) ∧
    (⟨P, pos, mult⟩ : Reading (grp a k msg r)).Even ∧ (∀ i, d ≤ mult i * (2 ^ a i - k i)) ∧ (∀ i, t ≤ r i) ∧ (∀ i, mult i ≤ e) ∧
    ∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / mult i)⌋₊ ≤ bad

/-- The same, message and randomness within the dimension: a proper subcode is allowed; one more
term. -/
def IsGlS {P : Type} [Fintype P] (C : LdCode E P) (d t e bad : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (a k msg r : A → ℕ)
      (pos : ∀ i, P → Fin (2 ^ a i)) (mult : A → ℕ) (R : A → Type)
      (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i)),
    C = (⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R ∧
    (∀ i, a i ≤ 32) ∧ (∀ i, 0 < k i) ∧
    (∀ i, k i < 2 ^ a i) ∧
    (∀ i, msg i + r i ≤ k i + 1) ∧
    (⟨P, pos, mult⟩ : Reading (grp a k msg r)).Even ∧
    (∀ i, d ≤ mult i * (2 ^ a i - k i)) ∧
    (∀ i, t ≤ r i) ∧
    (∀ i, mult i ≤ e) ∧
    ∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / mult i)⌋₊ + listMax (Fintype.card P) d e ≤ bad

/-- The codes built from such families by interleaving, by putting two side by side, and as
complexes; also from families of copied codes (`copy`); a larger count is a count (`up`). -/
inductive GlJ {P : Type} [Fintype P] : LdCode E P → ℕ → ℕ → ℕ → ℕ → Prop
  | base {C : LdCode E P} {d t e bad : ℕ} : IsGlJ C d t e bad → GlJ C d t e bad
  | sub {C : LdCode E P} {d t e bad : ℕ} : IsGlS C d t e bad → GlJ C d t e bad
  | copy {C : LdCode E P} {d t e bad : ℕ} : IsGlCpJ C d t e bad → GlJ C d t e bad
  | il {C : LdCode E P} {d t e bad : ℕ} (R : Type) [Fintype R] [DecidableEq R] :
      GlJ C d t e bad → GlJ (C.il R) d t e bad
  | pair {C₁ C₂ : LdCode E P} {d t e b₁ b₂ : ℕ} :
      GlJ C₁ d t e b₁ → GlJ C₂ d t e b₂ → GlJ (C₁.pair C₂) d t e (b₁ + b₂)
  | fam {A : Type} [Fintype A] [DecidableEq A] {C : A → LdCode E P} {d e : ℕ} {b : A → ℕ} :
      (∀ a, GlJ (C a) d 0 e (b a)) → GlJ (LdCode.fam C) d 0 e (∑ a, b a)
  | up {C : LdCode E P} {d t e b b' : ℕ} : GlJ C d t e b → b ≤ b' → GlJ C d t e b'

namespace Spec

def glJ_glC : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ), GlJ C d t e bad → GlC C d t

/-- Lists: stated here, proved in Cb/Gl/GlLdJProofs.lean. -/
def glJ_list : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ), GlJ C d t e bad →
    InJohnson (Fintype.card P) d e →
    C.ListAt e (listMax (Fintype.card P) d e) ∧
    ∀ (R : Type) [Fintype R] [DecidableEq R], (C.il R).ListAt e (listMax (Fintype.card P) d e)

/-- Agreement: under the statement on codes (`Cb.BCHKS46F`), by name. (not all hypotheses are named
here: see the statement below) -/
def glJ_mca : Prop :=
  Cb.BCHKS46F F →
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    GlJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad ∧ C.MCAat e bad

def glJ_mono : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad t' : ℕ),
    GlJ C d t e bad → t' ≤ t → GlJ C d t' e bad

/-- A fold: lists and agreement at all stages, under the premise `Cb.BCHKS46F F`. -/
def glJ_errOK : Prop :=
  Cb.BCHKS46F F →
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d t e bC bZ bW : ℕ), GlJ Y.C d 0 e bC →
    GlJ Y.Z d 0 e bZ → GlJ Y.Zw d t e bW → InJohnson (Fintype.card P) d e →
    Y.ErrOK e (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW)

/-- The base case, under the premise `Cb.BCHKS46F F`. -/
def glJ_base : Prop :=
  Cb.BCHKS46F F →
  ∀ (a : LdJoint E) (d bad : ℕ), GlJ a.C d 0 a.e bad → InJohnson (Fintype.card a.P) d a.e →
    a.e < d → a.BaseHyp d bad (listMax (Fintype.card a.P) d a.e)

/-- One code, read as it stands. -/
def glJ_one : Prop :=
  ∀ (a k msg r e : ℕ) (R : Type) [Fintype R] [DecidableEq R], a ≤ 32 → 0 < k → k < 2 ^ a →
    msg + r = k + 1 → 1 ≤ e  →
    IsGlJ ((Reading.one (rs a k msg r 0 0)).ld E fun _ => R) (2 ^ a - k)
      r e ⌊Cb.bchksBound (2 ^ a) k e⌋₊

end Spec
end Cb.Gl
