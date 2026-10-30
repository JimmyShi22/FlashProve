-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelJohnson.lean: the list of a code read under a transformation (`LdCode` of
Cb/Ld/LdRel.lean), from its distance alone: the Johnson bound, unique decoding, the list of
messages, and the lemma on collisions.

This file states list-decoding bounds for a linear code read under a linear map, from a lower bound
on the distance of the transformed code alone.
Definitions and statements (each a `Prop` in `Cb.Spec`); proofs in Cb/Ld/LdRelJohnsonProofs.lean.

Notions of Cb/Ld/LdRel.lean (`Dist`, `Near`, `ListAt` in the words of their doc comments). In the
statements below `Laws` and `Dist` stand as hypotheses, `ListAt` as a hypothesis or as the
conclusion; `Near` stands in the definition of `LdCode.Msgs`.
  The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
    `C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native
    words to long words, are linear over E; the encoder sends only the zero message with zero
    randomness to zero; and, for every long position x, any two native words that agree at the
    native positions `C.src x` have the same long symbol at x.
  `Dist d`: the transform of a non-zero codeword (the encoding of a pair (message, randomness) other
    than (0, 0)) is non-zero at d long positions or more.
  `Near e`: two native words are within e long positions of each other.
  `ListAt e L`: every native word has at most L pairs (message, randomness) whose encoding is within
    e long positions.

Why: some blocks work at a radius e beyond unique decoding (a block is one reduction of a chain,
with its honest side, extractor and numbers). Their errors depend on a list size L, and these blocks
take `LdCode.ListAt e L` as a hypothesis. The statements of this file give that hypothesis for any
code with the laws whose transform has distance d, at every radius below the Johnson radius for
(number of long positions, d). All radii and distances count long positions.

Main names:
  `Spec.ld_dist_ne`: under Laws and Dist d, two different pairs (message, randomness) have
    transforms that differ at d long positions or more.
  `Spec.ld_list_johnson`: the Johnson bound: Laws, Dist d, InJohnson |P| d e ⇒
    ListAt e (listMax |P| d e). (`InJohnson`, `listMax`: Cb/Gen/JohnsonList.lean)
  `Spec.ld_list_unique`: unique decoding (the guard): Laws, Dist d, 2 e < d ⇒ ListAt e 1.
  `Spec.ld_msgs_list`: ListAt e L bounds the list of messages (`LdCode.Msgs`) of every native word
    (two codewords may share a message).
  `Spec.ld_coll_johnson`: the lemma on collisions (Cb/Gen/OodDec.lean) for a sample map on the
    message coordinates, from the distance alone: under Laws, Dist d, InJohnson |P| d e and `Z.OK`,
    with L = listMax |P| d e: at no more than (L choose 2) · `Z.err` seeds do two different messages
    of the list have the same answers; twice the number of these seeds is at most L² · `Z.err`.
  `Spec.ld_coll`: the same for any L, under `C.ListAt e L` and `Z.OK`.
The number: with a = 1 - e/|P| (the agreement) and λ = 1 - d/|P|, listMax |P| d e is
(a - λ) / (a² - λ), rounded down; InJohnson says a² > λ. This reading holds for e ≤ |P| and d ≤ |P|,
and for listMax where InJohnson holds: the subtractions in Lean are those of natural numbers
(Cb/Gen/JohnsonList.lean, Limits).

Notation: `C`: a code read under a transformation (`LdCode E P`); |P|: the number of long positions;
`Z`: a sample map (`Sample`, Cb/Gen/OodDec.lean); `Z.val`: the answers of the vector u at the seed
ρ; `Z.err`: a number of seeds (ℕ; `Z.OK` speaks of it); `Z.OK`: every vector v other than 0 has
`Z.val ρ v` = 0 at no more than `Z.err` seeds ρ; `Clash`: the bad seeds: two different members of
the list have the same answer.

Limits: the bound is classical, and it is not tight. It does not see the structure of the code
(interleaving, pairs): the number of rows does not enter, because distance counts whole long
symbols. This file says nothing on mutual correlated agreement. At or beyond the Johnson radius no
list size is given.
The paper that this protocol builds on (lean/CREDITS.md) leaves the list size abstract; the bound
here is S. M. Johnson's, in the form of Cb/Gen/JohnsonList.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel
import Cb.Gen.JohnsonList
import Cb.Gen.OodDec

set_option autoImplicit false

namespace Cb
open Prob

/-- The messages represented in the list of a native word. -/
def LdCode.Msgs {E P : Type} [Field E] [Finite P] (C : LdCode E P) (e : ℕ)
    (f : C.Word) (m : C.J → E) : Prop :=
  ∃ r, C.Near e f (C.enc m r)

namespace Spec
open Cb.Ood

def ld_dist_ne : Prop :=
  ∀ (E P : Type) [Field E] [Finite P] (C : LdCode E P) (d : ℕ), C.Laws → C.Dist d →
    ∀ w w' : (C.J → E) × (C.Q → E),
      w ≠ w' → d ≤ cnt fun x => C.T (C.enc w.1 w.2) x ≠ C.T (C.enc w'.1 w'.2) x

/-- States the Johnson bound for a code read under a transformation. -/
def ld_list_johnson : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Fintype P] (C : LdCode E P) (d e : ℕ),
    C.Laws → C.Dist d → InJohnson (Fintype.card P) d e → C.ListAt e (listMax (Fintype.card P) d e)

/-- States the guard: unique decoding. -/
def ld_list_unique : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Fintype P] (C : LdCode E P) (d e : ℕ),
    C.Laws → C.Dist d → 2 * e < d → C.ListAt e 1

def ld_msgs_list : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Finite P] (C : LdCode E P) (e L : ℕ),
    C.ListAt e L → ∀ f : C.Word, ListLE (C.Msgs e f) L

/-- The lemma on collisions at a code read under a transformation. -/
def ld_coll : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Finite P] (C : LdCode E P) (Z : Sample E C.J) (e L : ℕ),
    C.ListAt e L → Z.OK →
    ∀ f : C.Word,
      cnt (Clash (C.Msgs e f) Z.val) ≤ L.choose 2 * Z.err ∧
      2 * cnt (Clash (C.Msgs e f) Z.val) ≤ L ^ 2 * Z.err

def ld_coll_johnson : Prop :=
  ∀ (E P : Type) [Field E] [Finite E] [Fintype P] (C : LdCode E P) (Z : Sample E C.J) (d e : ℕ),
    C.Laws → C.Dist d → InJohnson (Fintype.card P) d e → Z.OK →
    ∀ f : C.Word,
      cnt (Clash (C.Msgs e f) Z.val) ≤ (listMax (Fintype.card P) d e).choose 2 * Z.err ∧
      2 * cnt (Clash (C.Msgs e f) Z.val) ≤ listMax (Fintype.card P) d e ^ 2 * Z.err

end Spec
end Cb
