-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Readings.lean: rows and claims over the field with their mask forms
as lists, and how they are read as rows and claims of the typed lookup with parts
(Cb/Pv/KeyLookup/): functions on a type of entries.

Main names:
  RowF: a row: a mask form, terms on the table of bits (a coefficient and a vector of product form),
    a target.
  pairsAt: an entry of a vector of product form.
  onCell: what such a vector on the table of bits gives to a typed entry.
  ordDown, ordFirst: two orders of a level's variables.
  rdRow: a row, read. rdCl: a claim on a part's leaves alpha - key, read as a claim on the keys.

Limits. Definitions alone.

-/
import OnBytes.Tie.Pv.KeyLookup.PortSim
import Cb.Pv.KeyLookup.LamRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice Flat Finset Cb.LdLkp

/-- A row: the mask form, plus the sum over the terms of the coefficient times the table of bits
under the vector of product form, equals the target. -/
structure RowF where
  masks : PscF.MaskForm
  maps : List (GE × List (GE × GE))
  target : GE

/-- From the highest variable down. -/
def ordDown (n : ℕ) : List ℕ := (List.range n).reverse

/-- The named variables first, the others from the highest down. -/
def ordFirst (first : List ℕ) (n : ℕ) : List ℕ :=
  first ++ (ordDown n).filter fun j => !first.contains j

variable (A : Dat GE) (sl : Slot → A.J)

/-- The entry at the number n of a vector of product form: bit t of n picks the half of pair t. -/
def pairsAt : List (GE × GE) → ℕ → GE
  | [], _ => 1
  | p :: ps, n => (if n % 2 = 1 then p.2 else p.1) * pairsAt ps (n / 2)

/-- What a vector of product form on the table of bits gives to an entry: the plane is in the low mu
bits of a place's number; planes that are not real have no entry. -/
def onCell (ps : List (GE × GE)) (j : A.J) : GE :=
  ∑ u ∈ range (2 ^ A.d), ∑ p ∈ range A.pl,
    if A.bAt u p = j then pairsAt ps (p + 2 ^ A.mu * u) else 0

/-- A row, read. -/
def rdRow (r : RowF) : Row GE A.J :=
  ⟨fun j => rdMF sl r.masks j + (r.maps.map fun a => a.1 * onCell A a.2 j).sum, r.target⟩

/-- A claim on the leaves alpha - key of a part of 2^v keys, read as a claim on the keys. -/
def rdCl (al : GE) (v : ℕ) (c : PscF.PointClaim) : MCl GE A.J :=
  ⟨Lev.ptTop v c.point, fun j => - rdMF sl c.masks j, al - c.value⟩

end Lk6.Mid

#print axioms Lk6.Mid.rdRow
#print axioms Lk6.Mid.rdCl
