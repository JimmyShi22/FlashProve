-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/SingleForms.lean: THE SMALLNESS TEST's SINGLE EQUATIONS AS FORMS WITH CODE, over
the arrays' OWN rows: one form (Aff) for each tie (matrix, row of symbols, combination) and each read's
equation (read, combination). Definitions with code; no theorem; no Mathlib: it imports
the program `verify-on-bytes`'s OnBytes/Model/Tail.lean alone, for its records and plain functions.

Why. The list of single equations (rowsTail, OnBytes/Tie/Pv/Tail/EndRows.lean) gives each equation as a
function of a table of cells over any field: no code. A reader of a run's forms (the table of joints' item
"forms") wants forms that a run can evaluate. That these forms are that list's equations is
SingleFormsLaw.lean's.
USED OF `verify-on-bytes`'s FILES, ON RECORDS AND PLAIN DATA ALONE: HTailF2 and its fields; zzCol, tabAt; HFun;
Aff, Ent; the field's operations on E.
Main names:
  twoTo n: 2 ^ n in E. signE x: the sign of a drawn entry in E.
  thE tl mu p u: the drawn entry of matrix mu, column p, combination u, by its sign.
  tieAff tl mu i u: the tie of matrix mu, row i of symbols, combination u: right side less left side.
  readAff tl x u: the equation of the read x, combination u.
  readsP tl funs: the reads in the list's order (the text of readsList).
  rowsAff tl funs: all of them, in rowsTail's order.
IN A FORM AN ENTRY (tree, row, idx) NAMES CELL (row, idx) OF THE ARRAY ITSELF: its own row, no virtual row.
Limits: definitions alone. No slot is named: the single equations hold no masking value.

-/
import OnBytes.Model.Tail

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model

/-- 2 ^ n in E. -/
def twoTo (n : Nat) : E := powE (addE oneE oneE) n

/-- The sign of a drawn entry. -/
def signE (x : Int) : E := if x = 0 then zeroE else if x < 0 then subE zeroE oneE else oneE

/-- The drawn entry of matrix mu, column p, combination u, by its sign. -/
def thE (tl : HTailF2) (mu p u : Nat) : E :=
  signE (tl.cfF.getD ((tl.cfFirst.getD mu 0 + p) * tl.tau + u) 0)

/-- The two digits of one cell, under the weight w: the low digit, 2 ^ 10 times the high digit. c0, c1: the
cell's columns in the two planes of the digits' array. -/
def digitEnts (tl : HTailF2) (u c0 c1 : Nat) (w : E) : List Ent :=
  [{ tree := tl.ix.ZZ, row := u, idx := c0, coef := w },
   { tree := tl.ix.ZZ, row := u, idx := c1, coef := mulE w (twoTo 10) }]

/-- The tie of matrix mu, row i of symbols, combination u. -/
def tieAff (tl : HTailF2) (mu i u : Nat) : Aff :=
  let s := tl.shp.getD mu {}
  let lanes := (List.range 3).filter fun l => decide (3 * i + l < s.m)
  let z0 := (tl.zzCol mu 0 0).getD 0
  let z1 := (tl.zzCol mu 1 0).getD 0
  { ents := ((lanes.flatMap fun l =>
        digitEnts tl u (z0 + (3 * i + l)) (z1 + (3 * i + l)) (powE (twoTo 20) l)) ++
      (List.range s.k).map fun c =>
        ({ tree := tl.gtTree.getD mu 0, row := i, idx := c, coef := subE zeroE (thE tl mu c u) } : Ent)).toArray
    const := subE zeroE (mulE (twoTo 17) (lanes.foldl (fun a l => addE a (powE (twoTo 20) l)) zeroE)) }

/-- The equation of the read x, combination u. -/
def readAff (tl : HTailF2) (x : HFun × Nat) (u : Nat) : Aff :=
  let z0 := (tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0
  let z1 := (tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0
  let tU := (tl.ix.U.getD x.1.tree none).getD 0
  { ents := (((List.range x.1.len).flatMap fun j =>
        digitEnts tl u (z0 + j) (z1 + j) (x.1.phi.getD j zeroE)) ++
      (List.range (tl.mats.getD x.1.mat {}).k).map fun d =>
        ({ tree := tU, row := 0, idx := (tl.tabAt x.1 d x.2).getD 0,
           coef := subE zeroE (thE tl x.1.mat d u) } : Ent)).toArray
    const := subE zeroE (mulE (twoTo 17)
      ((List.range x.1.len).foldl (fun a j => addE a (x.1.phi.getD j zeroE)) zeroE)) }

/-- The reads in the list's order: the text of readsList. -/
def readsP (tl : HTailF2) (funs : Array HFun) : List (HFun × Nat) :=
  (List.range tl.NM).flatMap fun mu =>
    [0, 2].flatMap fun un => funs.toList.flatMap fun Fn =>
      if (Fn.mat == mu && Fn.tree == un) = true then
        (List.range ((tl.mats.getD mu {}).m / Fn.len)).map fun sg => (Fn, sg)
      else []

/-- All single equations as forms, in rowsTail's order. -/
def rowsAff (tl : HTailF2) (funs : Array HFun) : List Aff :=
  ((List.range tl.NM).flatMap fun mu =>
    (List.range (((tl.shp.getD mu {}).m + 2) / 3)).flatMap fun i =>
      (List.range tl.tau).map fun u => tieAff tl mu i u) ++
  (readsP tl funs).flatMap fun x => (List.range tl.tau).map fun u => readAff tl x u

end VerifiableInference.Desc.First.TailClaims
