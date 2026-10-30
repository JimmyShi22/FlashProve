-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.NzOk
/-
Johnson/Desc/K12/Law/CanonOk.lean: TWO TESTS WITH CODE FOR «A ROUND AS SHOWN FITS ITS WRITTEN ROUND's DATA» (RoundIs, H2K/TrOnto.lean): what Block.step's own first test does not ask. DEFINITIONS WITH CODE ALONE, NO THEOREM, NO Mathlib: so that they can be compiled and run. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  canonE x · canonOk rs   ON THE VIEW: every element of the extension field that a round drew has its three words below the field's size
  logOn ds · logOk p      ON THE PLAN: every declared round of the proximity test draws positions of at most 64 bits (logN ≤ 64); false where the numbers give no rounds
  canonLines              the lines that a run prints, with two controls, each due false: the first drawn element's first word is laid at the field's size · the last declared round's logN is laid at 65
EVALUATED (a run's word; the print is not in this library): at the four proximity tests of both stored example proofs and at the tiny place: canonOk and logOk true at each, both controls false at each.
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

def canonE (x : Fmt.Ext) : Bool :=
  decide (x.1.toNat < Fmt.Fld.two.p) && decide (x.2.1.toNat < Fmt.Fld.two.p) &&
    decide (x.2.2.toNat < Fmt.Fld.two.p)

/-- The test on the view: every drawn element is canonical. -/
def canonOk (rs : List Fmt.RoundView) : Bool := rs.all fun r => r.drawn.elems.all canonE

def logOn (ds : List Fmt.DeclaredRound) : Clauses :=
  ds.zipIdx.map fun x => (toString x.2 ++ ":" ++ x.1.entry.name, decide (x.1.entry.logN ≤ 64))

/-- The test on the plan: the numbers give rounds, and every clause says yes. -/
def logOk (p : P12) : Bool := (H2U.roundsOfNums p.nums).any fun ds => ok (logOn ds)

/-- The first round that drew an element, with that element's first word laid at the field's size. -/
def spoilCanon : List Fmt.RoundView → List Fmt.RoundView
  | [] => []
  | r :: rs =>
    match r.drawn.elems with
    | x :: xs =>
      { r with drawn := { r.drawn with
          elems := (UInt64.ofNat Fmt.Fld.two.p, x.2.1, x.2.2) :: xs } } :: rs
    | [] => r :: spoilCanon rs

def spoilLog (ds : List Fmt.DeclaredRound) : List Fmt.DeclaredRound :=
  match ds.reverse with
  | d :: r => ({ d with entry := { d.entry with logN := 65 } } :: r).reverse
  | [] => []

def canonLines (tagS : String) (p : P12) (rs : List Fmt.RoundView) : List String :=
  let ds := (H2U.roundsOfNums p.nums).getD []
  let n := (rs.map fun r => r.drawn.elems.length).sum
  [s!"{tagS}.CANON\tcanonOk {canonOk rs}\trounds {rs.length}\tdrawn elements {n}",
   s!"{tagS}.CANON.control\tthe first drawn element's first word at the field's size\t" ++
     s!"{canonOk (spoilCanon rs)}",
   s!"{tagS}.LOG\tlogOk {logOk p}\tclauses {(logOn ds).length}\t" ++
     s!"refusing: {((logOn ds).filter (!·.2)).map (·.1)}\t" ++
     s!"the greatest logN: {(ds.map (·.entry.logN)).foldl max 0}",
   s!"{tagS}.LOG.control\tthe last round's logN at 65\t{ok (logOn (spoilLog ds))}"]

end H2K.First
