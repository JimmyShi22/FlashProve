-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameSeat.lean: the link's frame's letters, read off the built records of the
model of the program `verify-on-bytes` (Stages.LinkH: the links' records, taken without their
routines; Verify.Public, OnBytes/Model/VerifyPublic.lean: the layers' and attention's plans).

  pubOf     a link's record without its routine
  Par       a link's letters: an attention link's, with attention's number of claims, or a layers'
  frameAt   the letters of link l, at every attention link and every layers' link behind link 0

No test lives here.

-/
import Johnson.Desc.First.Walk.Frame
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Seat
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- The record without its routine. -/
def pubOf (X : Stages.LinkH) : LinkPub := ⟨X.name, X.kind, X.Fp, X.Tp, X.fv, X.NCL, X.arrayOf⟩

/-- A link's letters, where the frame is brought; with attention's number of claims. -/
inductive Par where
  | att (P : AttPar) (nLin : Nat)
  | lay (P : LayPar)

/-- The letters of link l. -/
def frameAt (built : Array Stages.LinkH) (W : Verify.Public) (l : Nat) : Option Par := do
  let X ← built[l]?
  if l == 0 then none
  else if X.kind == 1 then
    let p ← W.A[X.g]?
    pure (.att ⟨pubOf X, l, p.ns, p.seam.tl⟩ p.nLin)
  else if X.kind == 0 then
    let hp ← W.G[X.g]?
    pure (.lay ⟨pubOf X, l, W.layers.y.h.p4, X.g, hp.Tp, hp.Fp, hp.ns, hp.tl⟩)
  else none

end Johnson.Desc.First.Walk.Seat
