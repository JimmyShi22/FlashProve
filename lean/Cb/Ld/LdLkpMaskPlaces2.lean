-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPlaces2.lean: the conditions on the places of the masks of the assembled lookup
`LkAsm2` (Cb/Ld/LdLkpAsm2.lean) follow from four plain ones; the number of own masks in closed form.
This file is book-keeping on positions: where, among the entries of the oracle messages, the masks
of the lookup's sumchecks are, and how many there are.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskPlaces2Proofs.lean. The
analogue of Cb/Ld/LdLkpMaskPlaces.lean for `LkAsm2`, and the count.
This file uses Cb/Ld/LdLkpAsm2.lean (the data `A : LkAsm2 E`: twelve families of places among the
entries: where the bits of the multiplicities are, and eleven families of own masks) and
Cb/Ld/LdLkpMaskAsm2.lean (`A.MaskOK Dt`: what the item "masked messages" of the whole lookup asks of
the places, part by part).

Why: `A.MaskOK Dt` is a nest of conditions in the parameters of the parts (tie, keys' tree, table's
side), some of them on forms and products that the parts compute. Here it follows from conditions
that name the data A and the set Dt alone.

Main names:
  `A.Nm`: the names of all own masks that are played: s: step 0 of the tie (two hiding coefficients'
    names, two inner masks); t l, l < n: step l + 1 of the tie; k l, l ≤ v': level l of the keys'
    tree; f l, l < d: level l of the table's forest; e: the closing (hiding coefficients alone: no
    inner mask); b: the bit test.
  `A.plN`: where each is (the eleven fields of A).
  `A.PlacesOK Dt`: the four plain conditions below, on a set Dt of entries, "the data".
    `inj`: all own masks that are played are at pairwise different places.
    `out`: none of them in the data.
    `bits`: every bit of the multiplicities is in the data.
    `keys`: the keys read the data only.
  `Spec.ldLkpPlaces2_ok`: `A.PlacesOK Dt` ⇒ `A.MaskOK Dt`.
  `Spec.ldLkpPlaces2_sw`: the places of the own masks (`A.swAll`) are the places of the names:
    A.swAll j ↔ ∃ i, j = A.plN i.
  `Spec.ldLkpPlaces2_card`: the number of own masks (`Nat.card A.Nm`):
    6 W + 3 + v² + 4 v + d² + (2 w + 8) d + 4 w, W = n + 1, v = v' + 1: tie 4 + 6 (W - 1);
    keys: 2 l + 5 at level l; table: 2 (w + l) + 5 at level l; closing 2 (w + d) + 1;
    bit test 2 (w + d) + 4. The number of masks, not of scalars sent: in our format a round
    polynomial is sent with one coefficient more than it has masks (declared in Cb/Ld/LdPsc.lean).

What follows from the definitions, and is therefore not asked: the products of the tie read keys and
bits only; the incoming form of the keys' tree reads one inner mask of step 0 of the tie; the
incoming forms of the forest read at most one inner mask of a step of the tie each.
Limits: this file does not say "None is a pad, read by nothing else": these are conditions on what
stands around the lookup: a pad is kept out of view by the reading Rd of the chain
(Cb/Ld/LdLkpMaskAsm2.lean), which must hold the data and the own masks and may leave out all else;
that no other block reads these entries is a condition of the chain in which the lookup stands.
Places that the data A name but the protocol does not play (t l for l ≥ n, k l for l > v', f l for
l ≥ d) are free.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskAsm2

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- The names of all own masks that are played. -/
inductive Nm : Type
  | s (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) ⊕ Bool)
  | t (l : ℕ) (h : l < A.n) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) ⊕ Bool)
  | k (l : ℕ) (h : l ≤ A.v') (i : PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool)
  | f (l : ℕ) (h : l < A.d) (i : PIdx (List.replicate (A.w + l) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool)
  | e (i : PIdx (List.replicate (A.w + A.d) (pfCube E 2)))
  | b (i : PIdx (List.replicate (A.w + A.d) (pfCube E 2) ++ [pDummy E 2]) ⊕ Unit)

/-- Where each is. -/
def plN : A.Nm → A.J
  | .s i => Sum.elim A.wS A.cS i
  | .t l _ i => Sum.elim (A.wAt l) (A.cAt l) i
  | .k l _ i => Sum.elim (A.wK l) (A.cK l) i
  | .f l _ i => Sum.elim (A.wT l) (A.cT l) i
  | .e i => A.wE i
  | .b i => Sum.elim A.wB (fun _ => A.cB) i

/-- The four plain conditions. -/
structure PlacesOK (Dt : A.J → Prop) : Prop where
  inj  : Function.Injective A.plN
  out  : ∀ i, ¬ Dt (A.plN i)
  bits : ∀ u j, Dt (A.bAt u j)
  keys : ∀ st m m', (∀ j, Dt j → m j = m' j) → A.key st m = A.key st m'

end LkAsm2
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpPlaces2_sw : Prop := ∀ (A : LkAsm2 E) (j : A.J), A.swAll j ↔ ∃ i, j = A.plN i

/-- The conditions of the item, from the four plain ones. -/
def ldLkpPlaces2_ok : Prop := ∀ (A : LkAsm2 E) (Dt : A.J → Prop), A.PlacesOK Dt → A.MaskOK Dt

/-- The number of own masks. -/
def ldLkpPlaces2_card : Prop :=
  ∀ A : LkAsm2 E, Nat.card A.Nm =
    6 * (A.n + 1) + 3 + (A.v' + 1) ^ 2 + 4 * (A.v' + 1) + A.d ^ 2 + (2 * A.w + 8) * A.d + 4 * A.w

end
end Cb.Spec
