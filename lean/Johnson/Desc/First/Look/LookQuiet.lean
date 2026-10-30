-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookQuiet.lean: what the verifier does right behind a lookup's rounds,
hearing nothing: three plain functions. Definitions with code. No theorem.

At four of the six sorts of place of this kind (a layers' link's calls; the digits at all three
sorts of link) the verifier program has a step without a round behind the lookup's messages: at 7 of
the small stored proof's 10 places, at 37 of the full-size one's 50. Each is written here as a
function of public numbers and of what is carried.

Main names:
  `sameShape a b`: behind the lookup on a layers' link's calls: seven numbers of the shape that was
    heard with are the layout's (OnBytes/Model/Layer.lean:127-133).
  `slotsTaken used claims F`: behind the lookup on the digits at a layers' or an attention link: the
    messages have taken just the planned slots of the ledger; the plan's number of claims is laid
    into the ledger (Layer.lean:597-599; OnBytes/Model/Attention.lean:224-225).
  `weightsClaim R wsLay`: behind the lookup on the digits at the head's link: the one claim on the
    committed weights (OnBytes/Model/Head.lean:61-83).

Limits: the three are texts of steps, held against the program's steps by runs alone. `weightsClaim`
calls the program's pure functions and plain records by name (`Head.Run`, `callNo`, `zjOf`, `wxOf`,
`onSum`, `eqTab`, `eqLow`). What the claim means, and that it is the right claim, is not looked at.
The refusals bear the program's own names. "header-y" is refused outright: this is a decision on
views; the program's dry run, in which every value is 0, skips that test.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- Seven numbers of two shapes are the same. -/
def sameShape (a b : Forest.Shape) : Bool :=
  a.dT == b.dT && a.kT == b.kT && a.NT == b.NT && a.rK == b.rK && a.first == b.first &&
    a.iota == b.iota && a.callOf == b.callOf

/-- The ledger's next free slot is the plan's number; then the plan's number of claims is laid. -/
def slotsTaken (used claims : Nat) (F : Fork) : Option Fork :=
  if F.next == used then some { F with planClaimsF := claims } else none

/-- **The one claim on the committed weights**, on the head's unit. Refused, among others, where a
checked token at a covered position is no entry of the vocabulary ("header-y"; asked where the unit
has a group "x"). -/
def weightsClaim (R : Head.Run) (wsLay : WsLay) : Except String WsClaim := do
  let q ← match Head.callNo R.L "HD0" with
    | some q => pure q
    | none => throw "internal-segment"
  let g ← match (R.L.calls.getD q default).seg? "HD0" with
    | some g => pure g
    | none => throw "internal-segment"
  let e := eqTab (Head.zjOf R.L R.x.g1 q)
  let ew0 := g.pos.map fun p => e.getD p zeroE
  let wx0 := Head.wxOf R ew0
  let ui := wsLay.U.size - 1
  if (wsLay.U.back?.map (·.X)) != some 13 then throw "internal-claim-unit"
  let eH := eqTab R.x.tH.r
  let sR := Head.onSum R R.x.tH.r
  let mut f : List WsFac := []
  for G in (wsLay.U.getD ui default).g do
    if G.name == "x" then
      let mut AV := (Array.range R.h.V).map fun v => subE zeroE (mulE sR (ew0.getD v zeroE))
      for t in [0:R.h.T] do
        if R.cov.hOn.getD t false then
          let v := R.x.win.getD t 0
          if !decide (v < R.h.V) then throw "header-y"
          AV := AV.modify v fun a => addE a (mulE wx0 (eH.getD t zeroE))
      f := f ++ [{ AV := AV }]
    else if G.name == "kk" then
      let pt := (Array.range G.z).map fun i => R.x.rs.getD (G.z - 1 - i) zeroE
      let e := eqLow R.x.rs G.z R.hp.lamS
      f := f ++ [{ pt := pt, HV := e.extract 0 G.o }]
    else throw "internal-claim-factors"
  pure { ui := ui, f := f }

end VerifiableInference.Desc.First.Look
