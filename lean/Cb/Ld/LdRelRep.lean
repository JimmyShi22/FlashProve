-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRep.lean: the codes of Code/Iface.lean, read at common positions (Cb/Gen/CodeRep.lean),
are codes read under a transformation (Cb/Ld/LdRel.lean).

This file instantiates the abstract code of the proximity tests (`LdCode`) with families of
interleaved linear codes, and states that its hypotheses follow from properties of these codes and
of the way they are read at common positions.
Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdRelRepProofs.lean.

Why: the blocks beyond unique decoding are stated for an abstract record (`LdCode`: native words,
encoder, transformation) and ask for its Laws, a distance, a list size, a count of mutual correlated
agreement, transparency, zero knowledge of the encoding. This file says that these hypotheses are
met by what this library has, under the conditions named in the rows below: a finite family of codes
with encoder C a, each with interleaved rows R a, over an extension field E, read through a reading
T (`Reading`, Cb/Gen/CodeRep.lean; repetition is one). So, for a family that meets them, these
hypotheses hold of `T.ld E R`, and the bounds of Cb/Gen/CodeList*.lean, Cb/Gen/JohnsonList*.lean,
Cb/Gen/CodeRep*.lean reach `T.ld E R`; what a fold asks of interleavings and pairs of its codes
(`SumPar.ErrOK`, Cb/Ld/LdSum.lean) needs more (agreement: `Spec.ld_rows_ld`, Cb/Ld/LdRelRows.lean,
from `T.MCAat E R e bad` for every family R of rows, where msg + r = k). This file gives no code
that meets these conditions.

Main names:
  `T.ld E R`: the record. A native position is (component, place), a native symbol a column; the
    long symbol at x holds the columns of all components at pos a x.
  `Spec.ldr_near`: within e long positions of an encoding = decodes under T, at e, to the full
    messages (`T.fms`).
  `Spec.ldr_onCode_of`, `Spec.ldr_onCode`: "on the code on S": ours implies that of
    Cb/Gen/CodeRep.lean; the converse where message and randomness fill the dimension (msg + r = k).
  `Spec.ldr_laws`: the laws, from msg + r ≤ k and a positive distance of each generator.
  `Spec.ldr_dist`: the distance under T, for an even reading (`Reading.Even`, Cb/Gen/CodeRep.lean:
    each position of the component a is read at exactly `T.mult a` > 0 long positions), from
    msg + r ≤ k and the distance d of each generator: `Dist D` for every D that is at most
    `T.mult a` · d in every component a.
  `Spec.ldr_list`: the list: `T.ListAt` gives ListAt, same radius and number (msg + r ≤ k).
  `Spec.ldr_mca`: agreement: `T.MCAat` gives MCAat, same radius and count, where msg + r = k.
  `Spec.ldr_transparent`, `Spec.ldr_local`: transparent; one native position of each component for a
    long position.
  `Spec.ldr_zk`: zero knowledge of the encoding at t long positions, if every code hides t positions
    (`Code.Enc.Core`, t ≤ b).

Why msg + r = k in two places: Cb/Gen/CodeRep.lean's "on the code" speaks of the whole code (images
of all vectors of length k), `LdCode`'s of the image of the encoder. Agreement of a subcode does not
follow from agreement of the code. For codes that do not have msg + r = k: Cb/Ld/LdRelSub.lean.

Limits: this file says nothing on oracles with symbols in the small field F. (A word over F is close
only to codewords over F, below the distance.) No bound is proved here: all are passed on.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel
import Cb.Gen.CodeRep

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Reading
variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] {C : A → Code.Enc F} (T : Reading C)
  (E : Type) [Field E] [Algebra F E] (R : A → Type) [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)]

/-- A family of codes with rows, under a reading, as one code read under a transformation. -/
@[reducible] def ld : LdCode E T.P :=
  LdCode.fam fun a => (LdCode.ofEnc (E := E) (C a) (T.pos a)).il (R a)

variable {E R}

/-- a native word as tables of rows -/
def tabs (f : (T.ld E R).Word) : ∀ a, R a → Fin (C a).n → E := fun a i j => f ⟨a, j⟩ (i, ())

/-- (message, randomness) as tables of full messages -/
def fms (m : (T.ld E R).J → E) (r : (T.ld E R).Q → E) : ∀ a, R a → Fin (C a).k → E :=
  fun a i => (C a).fm (fun j => m ⟨a, (i, j)⟩) (fun q => r ⟨a, (i, q)⟩)

end Reading

namespace Spec
section
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]

def ldr_near : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (e : ℕ) (f : (T.ld E R).Word)
      (m : (T.ld E R).J → E) (r : (T.ld E R).Q → E),
    (T.ld E R).Near e f ((T.ld E R).enc m r) ↔ T.DecodesTo E e (T.tabs f) (T.fms m r)

def ldr_onCode_of : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (f : (T.ld E R).Word) (S : Finset T.P),
    (T.ld E R).OnCode ((T.ld E R).T f) S → T.OnCode E (T.tabs f) S

def ldr_onCode : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)],
    (∀ a, (C a).msg + (C a).r = (C a).k) →
    ∀ (f : (T.ld E R).Word) (S : Finset T.P),
      (T.ld E R).OnCode ((T.ld E R).T f) S ↔ T.OnCode E (T.tabs f) S

def ldr_laws : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)],
    (∀ a, (C a).msg + (C a).r ≤ (C a).k) → (∀ a, Blocks.HasDist (C a).G (C a).d) →
    (∀ a, 0 < (C a).d) → (T.ld E R).Laws

def ldr_dist : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (D : ℕ),
    T.Even → (∀ a, (C a).msg + (C a).r ≤ (C a).k) → (∀ a, Blocks.HasDist (C a).G (C a).d) →
    (∀ a, D ≤ T.mult a * (C a).d) → (T.ld E R).Dist D

def ldr_transparent : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)],
    (T.ld E R).Transparent

def ldr_local : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)],
    (T.ld E R).LocalLE (Fintype.card A)

def ldr_list [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (e L : ℕ),
    (∀ a, (C a).msg + (C a).r ≤ (C a).k) → T.ListAt E R e L → (T.ld E R).ListAt e L

def ldr_mca [Finite E] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (e bad : ℕ),
    (∀ a, (C a).msg + (C a).r = (C a).k) → T.MCAat E R e bad → (T.ld E R).MCAat e bad

def ldr_zk [Fintype F] [Fintype E] : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (C : A → Code.Enc F) (T : Reading C) (R : A → Type)
      [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)] (t : ℕ),
    (∀ a, (C a).Core) → (∀ a, t ≤ (C a).b) → (T.ld E R).Zk t

end
end Spec
end Cb
