-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Whole.lean: the places of the kind "lookup" on the proof file's first
chain, whole: the kind's block, and behind it what the verifier does at that place without hearing
anything. Definitions with code. No theorem.

A place of the chain can hold more than the kind's rounds. Behind the lookup on a layers' link's
calls the verifier compares seven numbers; behind the lookup on the digits at a layers' or an
attention link it counts the ledger's slots and lays the plan's number of claims; at the head's link
it makes the one claim on the committed weights. These lines belong to the link rather than to the
lookup. They stand here so that no text of `verify-on-bytes` is needed at these places.

Main names:
  `quietLook fs`, `quietDigits used claims`, `quietHead X`: the three, as functions on the carried
    state (Johnson/Desc/First/State.lean), over the plain functions of
    Johnson/Desc/First/Look/LookQuiet.lean. Each refusal bears the name of its test.
  `quietAt X i digits`: which of them stands behind link i's lookup; nothing where none does.
  `theWhole claim runs X codes shape a`: **the block at the address a, whole**: `theOwn`'s block,
    then a block without a round (`Block.andThen`).

Limits: runs alone have held these lines against `verify-on-bytes`'s steps. At the head's link the
covered positions are made of the request's words and THE HEARD REPLY (`S.covered`); that
text makes them of the asked reply, in front of the chain: on a file that the last test lets by
the two are one. `quietLook` reads what the hearing laid (`S.lookHeard?`); by the kind's text that
shape is the place's own, so the test reads public numbers alone and no view can trip it. The number
of claims on the weights (1) is a public number, asked behind the claim as that text asks it.
`X.y` is the layout in the layers' public record (`X.layers.y`). The kind's block and the block
behind it bear one place: `Block.andThen` makes one block of the two.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Own
import Johnson.Desc.First.Look.LookQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.Model

/-- Behind the lookup on a layers' link's calls. fs: the layout's shape. -/
def quietLook (fs : Forest.Shape) (s : First.S) : Except String First.S := do
  let g ← named "K3 quiet: nothing was heard" s.lookHeard?
  need "K3 quiet: the shape is the layout's" (First.Look.sameShape g.shape fs)
  pure s

/-- Behind the lookup on the digits, at a layers' or an attention link. -/
def quietDigits (used claims : Nat) (s : First.S) : Except String First.S := do
  let F ← named "K3 quiet: no sub-proof is open" s.fork?
  let G ← named "K3 quiet: the planned slots are taken" (First.Look.slotsTaken used claims F)
  pure (s.putFork G)

/-- Behind the lookup on the digits, at the head's link. -/
def quietHead (X : Verify.Public) (s : First.S) : Except String First.S :=
  match s.here with
  | .head a => do
    need "K3 quiet: the head's link is open" a.opened
    let cov ← s.covered X.T X.P.h.V
    let x ← named "K3 quiet: what the head heard is laid" a.x
    let t ← named "K3 quiet: the head's tables are laid" a.t
    let R : Head.Run :=
      { h := X.hS, L := X.HLy, b := Verify.borderOf X.y, hp := X.H, cov := cov, x := x, t := t
        iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 }
    let claim ← First.Look.weightsClaim R X.layers.wsLay
    need "K3 quiet: one claim on the weights" (X.H.NCL == 1)
    pure { s with here := .head { a with claim := some claim } }
  | _ => .error "K3 quiet: the head's link is open"

/-- What stands behind link i's lookup without a round; nothing where the place ends with the
lookup, or there is no such link. -/
def quietAt (X : Verify.Public) (i : Nat) (digits : Bool) :
    Option (First.S → Except String First.S) :=
  let step := if X.p4 then 2 else 1
  if isHead X i then (if digits then some (quietHead X) else none)
  else if i % step == 0 then
    if digits then X.G[i / step]?.map fun hp => quietDigits hp.used hp.nLin
    else some (quietLook X.y.fo)
  else if digits then X.A[i / step]?.map fun a => quietDigits a.nMsg a.nLin
  else none

/-- **The block at an address, whole.** The letters are `theOwn`'s. -/
def theWhole {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) : Option (Block First.S Cl) :=
  (theOwn claim runs X codes shape a).map fun b =>
    match a.link.bind fun i => quietAt X i (a.piece == pieceAt X i true) with
    | some f => b.andThen b.name (roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f)
    | none => b

end VerifiableInference.Desc.K3
