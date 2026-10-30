-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPscFam.lean: from a family of conditions (or the inner sum of terms of a sum atom) to
the sumcheck on its sum predicate: the four conditions, what the input claim says, what the output
rows say, and that, under the hypotheses of its statement, the row on a sum atom is the next
sumcheck's input claim.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartPscFamProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
A family of conditions f : `Fam X E` (Cb/Req/ReqSpec.lean) is a sum of terms over numbered atoms,
on f.v variables; its polynomial is `Fam.ext` (Cb/Part/LdPart.lean). The sumcheck is `S.our M` of
Cb/Part/LdPartPsc.lean, for S the sum of terms below. Its sum predicate is its input claim: a
weighted sum of the summand over the cube, plus the incoming form, equals a target τ.

One constructor. No variable is fixed.
  `f.partSm h k ve rx rp rd : LdPartSm E St J` (Cb/Part/LdPartPsc.lean):
    variables: the f.v variables of the family; the first ve under the equality form at the
      coordinates of a point that the state holds (rp st), the others plain. Which variables are
      plain does not depend on the state.
    maps: the numbered atoms j < f.na, all revealed, each at its extension `Atom.ext` (multilinear,
      all three kinds, where the atom is well formed for a format Φ and h = Φ.h, k = Φ.hi + Φ.lo:
      `ldPart_atom_deg`, Cb/Part/LdPartPscFamProofs.lean).
    terms: the family's: the multilinear extension of the coefficient table on all f.v variables,
      times the product of the atoms that the term names (numbers ≥ f.na are dropped: there are
      none in a well-formed family).
    parameters: h, k: the index matrix has h rows and 2^k columns; rx : St → X the instance; rd :
      `LdPartRd E J` the one reading of the block's entries as (index matrix over E, matrices of
      cells).
  The three uses. ve = f.v: the sum predicate on a key map at a lookup's end point, and the one
    that a zerocheck on the identities leaves at its point. `P.toFam` at ve = v, where P.v = v + w:
    a claim on the value of the sum atom (w, P) at a point (`Spec.ldPartFam_atom`).




Main names ("the terms name atoms" means: every number in a term's list is below the number of
atoms):
  `Spec.ldPartFam_val`: see its docstring.
  `Spec.ldPartFam_ok`: f well formed for a format Φ, h = Φ.h, k = Φ.hi + Φ.lo, f.deg + 1 ≤ n i for
    every variable, f.deg ≤ DY ⇒ `S.OK M` (every map of degree 1 in every variable); so
    (`Cb.ldPartPsc_ok`) `VarsOK`, `ValInj`, `DegX`, `DegY`. f.deg: the most atoms in a term, with
    repeats (Cb/Req/ReqSumFmt.lean).
  `Spec.ldPartFam_sum`: if f's terms name atoms and ve ≤ f.v, the input claim (τ, st) says: (the
    multilinear extension, on ve variables, of b ↦ Σ_{j < 2^(f.v - ve)} f.ext at the vertex (b, j))
    at rp st + incoming form = τ.
  `Spec.ldPartFam_allV`: for a family that is well formed for a format Φ over a field F, at ve =
    f.v, h = Φ.h, k = Φ.hi + Φ.lo, where the index matrix that is read lies over F: (the extension
    of the family's values `Fam.val` of Cb/Req/ReqSpec.lean) at rp st + incoming form = τ.
  `Spec.ldPartFam_atom`: for `P.toFam` at ve = v, if P's terms name atoms and P.v = v + w:
    (Atom.sum w P).ext at rp st + incoming form = τ. No condition on degrees in the outer
    variables.
  `Spec.ldPartFam_row`: the output row on the atom a says: (f.atom a).ext at the verifier's point +
    (its inner mask entry) · (the dummy's challenge) = v_a.
  `Spec.ldPartFam_next`: if f.atom a is the sum atom (w, P), P's terms name atoms, P.v = f.v + w,
    and a state st' of the sumcheck on `P.toFam` (ve = f.v) holds the same instance and the
    verifier's point, and its incoming form's value is (inner mask entry of a) · (the dummy's
    challenge): the output row on a is that sumcheck's input claim with the target v_a.

Notation:
  `M : LdPartMk S`: what the sumcheck adds: degrees, the incoming form, the places of its own masks
    (Cb/Part/LdPartPsc.lean);
  `M.n i`, `M.DY`: its degrees, n i and DY above;
  `∑ j, M.slS st j * m j`: the incoming form's value;
  `m (M.cAt a)`: the inner mask entry of a;
  `S.outPt M o`, `S.outB M o`: the verifier's point, the dummy's challenge;
  `St`: the states;
  `m : J → E`: the block's entries.

Limits: on where masks lie the file has this: `M`'s type `LdPartMk` (Cb/Part/LdPartPsc.lean) has the
fields `slS`, `wAt`, `cAt`; `Spec.ldPartFam_row` and `Spec.ldPartFam_next` have the term
`m (M.cAt a)`; `Spec.ldPartFam_sum`, `Spec.ldPartFam_all`, `Spec.ldPartFam_allV`,
`Spec.ldPartFam_atom` name `M.slS`, `Spec.ldPartFam_next` names `M'.slS`; none names `wAt`. On the
reading rd and on the states: `Spec.ldPartFam_allV` alone has a premise on `rd.W m`,
`Spec.ldPartFam_next` alone has premises on a state (`st'`). `M`, `M'`, `rd`, `St`, `St'` are given
no value. This file does not say that the row on a cell atom is a linear row on messages, and the
row on an index atom a tensor row: other files.
Degrees are counted coarsely here. `ldPartFam_ok` counts every atom of a term, and the coefficient,
in every variable. This protocol's technical report (lean/CREDITS.md) counts, for one variable, only
the maps (and the coefficient) in which that variable occurs; so its bound can be lower than
f.deg + 1. `S.OK` takes the finer count (degrees da a i, dc i by variable); no theorem here derives
it from a family's data.
The report's option to replace an outer variable by the point's coordinate (where the inner
summand has degree at most 1 in it): not rendered. Unrevealed maps; a sumcheck that reveals nothing
(no dummy variable, no last round); a leading variable that runs over a domain of E: the form of
Cb/Part/LdPartPsc.lean has none of them.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPart
import Cb.Part.LdPartPsc
import Cb.Req.ReqSumFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-- numbers below na, as names -/
def ldPartNames (na : ℕ) (l : List ℕ) : List (Fin na) :=
  l.filterMap fun j => if h : j < na then some ⟨j, h⟩ else none

/-- The sum of terms of a family. -/
@[reducible] def Fam.partSm {X E : Type} [Field E] (f : Fam X E) (h k ve : ℕ) {St J : Type}
    (rx : St → X) (rp : St → ℕ → E) (rd : LdPartRd E J) : LdPartSm E St J where
  k := f.v
  A := Fin f.na
  F := fun st m a z => (f.atom a).ext h k f.v (rx st) (rd.W m) (rd.A m) (Blocks.nat z)
  terms := f.terms.map fun t =>
    ⟨fun st z => Blocks.ext f.v (t.coef (rx st)) (Blocks.nat z), ldPartNames f.na t.atoms⟩
  w := fun st i => if i.val < ve then some (rp st i) else none

namespace Spec
section
variable (X E : Type) [Field E] [Fintype E]

/-- States: if the terms name atoms of f, the summand is the family's polynomial. -/
def ldPartFam_val : Prop :=
  ∀ (f : Fam X E) (h k ve : ℕ) (St J : Type) (rx : St → X) (rp : St → ℕ → E) (rd : LdPartRd E J)
      (st : St) (m : J → E) (z : Fin f.v → E),
    (∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) →
    (f.partSm h k ve rx rp rd).val st m z = f.ext h k (rx st) (rd.W m) (rd.A m) (Blocks.nat z)

/-- The conditions of the sumcheck, by the coarse count. -/
def ldPartFam_ok : Prop :=
  ∀ (F : Type) [Field F] [Algebra F E] (Φ : IdxFmt F) (f : Fam X E) (ve : ℕ) (St J : Type)
      (rx : St → X) (rp : St → ℕ → E) (rd : LdPartRd E J)
      (M : LdPartMk (f.partSm Φ.h (Φ.hi + Φ.lo) ve rx rp rd)),
    f.WF Φ → (∀ i, f.deg + 1 ≤ M.n i) → f.deg ≤ M.DY →
    (f.partSm Φ.h (Φ.hi + Φ.lo) ve rx rp rd).OK M fun _ _ => 1

/-- What the input claim says. -/
def ldPartFam_sum : Prop :=
  ∀ (f : Fam X E) (h k ve : ℕ) (St J : Type) [Fintype J] (rx : St → X) (rp : St → ℕ → E)
      (rd : LdPartRd E J) (M : LdPartMk (f.partSm h k ve rx rp rd)) (τ : E) (st : St) (m : J → E),
    (∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) → ve ≤ f.v →
    (((f.partSm h k ve rx rp rd).our M).SumHolds (τ, st) m ↔
      Blocks.ext ve (fun b =>
              ∑ j ∈ Finset.range (2 ^ (f.v - ve)),
                f.ext h k (rx st) (rd.W m) (rd.A m) (vtx f.v (b * 2 ^ (f.v - ve) + j))) (rp st) +
          ∑ j, M.slS st j * m j = τ)

/-- All variables under equality forms. -/
def ldPartFam_all : Prop :=
  ∀ (f : Fam X E) (h k : ℕ) (St J : Type) [Fintype J] (rx : St → X) (rp : St → ℕ → E)
      (rd : LdPartRd E J) (M : LdPartMk (f.partSm h k f.v rx rp rd)) (τ : E) (st : St) (m : J → E),
    (∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) →
    (((f.partSm h k f.v rx rp rd).our M).SumHolds (τ, st) m ↔
      Blocks.ext f.v (fun b => f.ext h k (rx st) (rd.W m) (rd.A m) (vtx f.v b)) (rp st) +
          ∑ j, M.slS st j * m j = τ)

/-- The claim on the extension of the family's values. -/
def ldPartFam_allV : Prop :=
  ∀ (F : Type) [Field F] [Algebra F E] (Φ : IdxFmt F) (f : Fam X E) (St J : Type)
      [Fintype J] (rx : St → X) (rp : St → ℕ → E) (rd : LdPartRd E J)
      (M : LdPartMk (f.partSm Φ.h (Φ.hi + Φ.lo) f.v rx rp rd)) (τ : E) (st : St)
      (m : J → E) (W : ℕ → ℕ → F),
    f.WF Φ → (rd.W m = fun y c => algebraMap F E (W y c)) →
    (((f.partSm Φ.h (Φ.hi + Φ.lo) f.v rx rp rd).our M).SumHolds (τ, st) m ↔
      Blocks.ext f.v (f.val Φ (rx st) W (rd.A m)) (rp st) + ∑ j, M.slS st j * m j = τ)

/-- The claim on a sum atom's value. -/
def ldPartFam_atom : Prop :=
  ∀ (P : Poly0 X E) (h k v w : ℕ) (St J : Type) [Fintype J] (rx : St → X)
      (rp : St → ℕ → E) (rd : LdPartRd E J) (M : LdPartMk (P.toFam.partSm h k v rx rp rd))
      (τ : E) (st : St) (m : J → E),
    (∀ t ∈ P.terms, ∀ j ∈ t.atoms, j < P.na) → P.v = v + w →
    (((P.toFam.partSm h k v rx rp rd).our M).SumHolds (τ, st) m ↔
      (Atom.sum w P).ext h k v (rx st) (rd.W m) (rd.A m) (rp st) + ∑ j, M.slS st j * m j = τ)

/-- What the output row on an atom says. -/
def ldPartFam_row : Prop :=
  ∀ (f : Fam X E) (h k ve : ℕ) (St J : Type) [Fintype J] (rx : St → X) (rp : St → ℕ → E)
      (rd : LdPartRd E J) (M : LdPartMk (f.partSm h k ve rx rp rd))
      (o : ((f.partSm h k ve rx rp rd).our M).par.Out) (m : J → E) (a : Fin f.na),
    ((f.partSm h k ve rx rp rd).our M).par.EHolds o m a ↔
    (f.atom a).ext h k f.v (rx o.st) (rd.W m) (rd.A m)
          (Blocks.nat ((f.partSm h k ve rx rp rd).outPt M o)) +
        m (M.cAt a) * (f.partSm h k ve rx rp rd).outB M o = o.vals a

/-- States: under the hypotheses below, the row on a sum atom is the next sumcheck's input claim.
-/
def ldPartFam_next : Prop :=
  ∀ (f : Fam X E) (h k ve : ℕ) (St St' J : Type) [Fintype J] (rx : St → X) (rp : St → ℕ → E)
      (rx' : St' → X) (rp' : St' → ℕ → E) (rd : LdPartRd E J)
      (M : LdPartMk (f.partSm h k ve rx rp rd)) (a : Fin f.na) (w : ℕ) (P : Poly0 X E)
      (M' : LdPartMk (P.toFam.partSm h k f.v rx' rp' rd))
      (o : ((f.partSm h k ve rx rp rd).our M).par.Out) (st' : St') (m : J → E),
    f.atom a = .sum w P → (∀ t ∈ P.terms, ∀ j ∈ t.atoms, j < P.na) → P.v = f.v + w →
    rx' st' = rx o.st → rp' st' = Blocks.nat ((f.partSm h k ve rx rp rd).outPt M o) →
    ∑ j, M'.slS st' j * m j = m (M.cAt a) * (f.partSm h k ve rx rp rd).outB M o →
    (((f.partSm h k ve rx rp rd).our M).par.EHolds o m a ↔
      ((P.toFam.partSm h k f.v rx' rp' rd).our M').SumHolds (o.vals a, st') m)

end
end Spec
end
end Cb
