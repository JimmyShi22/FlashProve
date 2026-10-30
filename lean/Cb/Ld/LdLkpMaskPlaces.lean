-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPlaces.lean: the conditions on the places of the assembled lookup's masks follow from
four plain ones.
This file is book-keeping on positions: where, among the entries of the oracle messages, the masks
of the lookup's sumchecks are.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpMaskPlacesProofs.lean.
The assembled lookup here is `LkAsm` (Cb/Ld/LdLkpAsm.lean), superseded under all callers by `LkAsm2`
(Cb/Ld/LdLkpAsm2.lean): Cb/Ld/LdLkpMaskPlaces2.lean has the analogue of this file for `LkAsm2`, and
the number of own masks in closed form.
This file uses Cb/Ld/LdLkpAsm.lean (the data `A : LkAsm E`: thirteen families of places among the
entries: where the bits of the multiplicities are, and twelve families of own masks) and
Cb/Ld/LdLkpMaskAsm.lean (`A.MaskOK Dt`: what the item "masked messages" of the whole lookup asks of
the places, part by part).

Why: `A.MaskOK Dt` is a nest of conditions in the parameters of the parts (tie, keys' tree, table's
side), some of them on forms and products that the parts compute. Here it follows from conditions
that name the data A and the set Dt alone.

Main names:
  `A.Nm`: the names of all own masks that are played: s: step 0 of the tie (two hiding coefficients'
    names, two inner masks); t l, l < n: step l + 1 of the tie; k l, l ≤ v': level l of the keys'
    tree; f l, l < d: level l of the table's forest; e: the closing; b: the bit test.
  `A.plN`: where each is (the twelve fields of A).
  `A.PlacesOK Dt`: the four plain conditions below, on a set Dt of entries, "the data".
    `inj`: all own masks that are played are at pairwise different places.
    `out`: none of them in the data.
    `bits`: every bit of the multiplicities is in the data.
    `keys`: the keys read the data only.
  `Spec.ldLkpPlaces_ok`: `A.PlacesOK Dt` ⇒ `A.MaskOK Dt`.
  `Spec.ldLkpPlaces_sw`: the places of the own masks (`A.swAll`) are the places of the names:
    A.swAll j ↔ ∃ i, j = A.plN i.
  `Spec.ldLkpPlaces_tieOwn`, `Spec.ldLkpPlaces_treeOwn`: the own places of a step of a tie, of a
    level of a tree, in the data's own fields.

What follows from the definitions, and is therefore not asked: the products of the tie read keys and
bits only; the incoming form of the keys' tree reads one inner mask of step 0 of the tie; the
incoming forms of the forest read at most one inner mask of a step of the tie each.
Limits: this file does not say "None is a pad, read by nothing else": these are conditions on what
stands around the lookup: a pad is kept out of view by the reading Rd of the chain
(Cb/Ld/LdLkpMaskAsm.lean), which must hold the data and the own masks and may leave out all else;
that no other block reads these entries is a condition of the chain in which the lookup stands.
Places that the data A name but the protocol does not play (t l for l ≥ n, k l for l > v', f l for
l ≥ d) are free.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskAsm

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

/-- The names of all own masks that are played. -/
inductive Nm : Type
  | s (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) ⊕ Bool)
  | t (l : ℕ) (h : l < A.n) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) ⊕ Bool)
  | k (l : ℕ) (h : l ≤ A.v') (i : PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool)
  | f (l : ℕ) (h : l < A.d) (i : PIdx (List.replicate (A.w + l) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool)
  | e (i : PIdx (List.replicate (A.w + A.d) (pfCube E 2) ++ [pDummy E 1]) ⊕ Unit)
  | b (i : PIdx (List.replicate (A.w + A.d) (pfCube E 2) ++ [pDummy E 2]) ⊕ Unit)

/-- Where each is. -/
def plN : A.Nm → A.J
  | .s i => Sum.elim A.wS A.cS i
  | .t l _ i => Sum.elim (A.wAt l) (A.cAt l) i
  | .k l _ i => Sum.elim (A.wK l) (A.cK l) i
  | .f l _ i => Sum.elim (A.wT l) (A.cT l) i
  | .e i => Sum.elim A.wE (fun _ => A.cE) i
  | .b i => Sum.elim A.wB (fun _ => A.cB) i

/-- The four plain conditions. -/
structure PlacesOK (Dt : A.J → Prop) : Prop where
  inj  : Function.Injective A.plN
  out  : ∀ i, ¬ Dt (A.plN i)
  bits : ∀ u j, Dt (A.bAt u j)
  keys : ∀ st m m', (∀ j, Dt j → m j = m' j) → A.key st m = A.key st m'

end LkAsm
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The own places of a step of a tie. -/
def ldLkpPlaces_tieOwn : Prop :=
  ∀ (D : TieP E) (j : D.J),
    (D.ownAt 0 j ↔ ∃ i, j = Sum.elim D.wS D.cS i) ∧
    ∀ l, D.ownAt (l + 1) j ↔ ∃ i, j = Sum.elim (D.wAt l) (D.cAt l) i

/-- The own places of a level of a tree. -/
def ldLkpPlaces_treeOwn : Prop :=
  ∀ (D : TreeP E) (l : ℕ) (j : D.J), D.ownAt l j ↔ ∃ i, j = Sum.elim (D.wAt l) (D.cAt l) i

def ldLkpPlaces_sw : Prop := ∀ (A : LkAsm E) (j : A.J), A.swAll j ↔ ∃ i, j = A.plN i

/-- The conditions of the item, from the four plain ones. -/
def ldLkpPlaces_ok : Prop := ∀ (A : LkAsm E) (Dt : A.J → Prop), A.PlacesOK Dt → A.MaskOK Dt

end
end Cb.Spec
