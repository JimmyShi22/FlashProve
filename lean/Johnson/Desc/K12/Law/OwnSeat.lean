-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnSeat.lean: a test on the record: where the first fold of the proximity test
(the kind K12) sends its own mask, that mask's tree is the last of the trees that the first switch
opens.

The trees' places D.ts (Johnson/Desc/K12/Law/FirstOk.lean) rise, each once. The own mask's tree is
the newest in the book, so it should stand last; this test asks it of the plain data that gpOf
makes. With ownTieOk (Johnson/Desc/K12/Law/OwnTie.lean), which ties the first written round to the
first switch's last declared opening, it brings that round to the mask's tree in the book
(Johnson/Desc/K12/Law/OwnSeatLaw.lean). Definitions with code alone and no theorem, so that the test
can be compiled and run.
The clauses: data: the plain data can be made. f:last (where the record names no mask): the last of
D.ts is D.fresh.t.
Main names:
  `lastOn`, `lastL`, `lastOk`: the clauses at given plain data; at a place and the record behind the
    batching; the test.
  `lastLines`: the lines that a run prints, with one control, due false where the record names no
    mask: the mask's tree is taken to stand one place further on. Elsewhere there is no control.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.FirstOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

def lastOn (own : Bool) (D : Plain) : Clauses :=
  ("data", true) :: (if own then [("f:last", D.ts.getLast? == some D.fresh.t)] else [])

def lastL (p : P12) (t : T12) : Clauses :=
  match p.nums.stages, t.pass with
  | a :: _, .claim _ L =>
    match gpOf p t a L with
    | some D => lastOn t.mask.isNone D
    | none => [("data", false)]
  | _, _ => [("data", false)]

/-- The test: every clause says yes. -/
def lastOk (p : P12) (t : T12) : Bool := ok (lastL p t)

def lastLines (tagS : String) (p : P12) (t : T12) : List String :=
  let ctl : String := match p.nums.stages, t.pass with
    | a :: _, .claim _ L =>
      match gpOf p t a L with
      | some D =>
        if t.mask.isNone then
          toString (ok (lastOn true { D with fresh := { D.fresh with t := D.fresh.t + 1 } }))
        else "no control: the record names the mask"
      | none => "no plain data"
    | _, _ => "no stage, or no claim"
  [tagS ++ ".LAST\tlastOk " ++ toString (lastOk p t) ++ "\tclauses " ++
      toString ((lastL p t).map (·.1)) ++ "\trefusing: " ++
      toString (((lastL p t).filter (!·.2)).map (·.1)),
   tagS ++ ".LAST.control\tthe mask's tree one place further on\t" ++ ctl]

end H2K.First
