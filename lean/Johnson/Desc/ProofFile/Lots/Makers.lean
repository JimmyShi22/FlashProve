-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lots/Makers.lean: small functions with which several lots make their blocks.
Definitions with code; no theorem.

  `spotsAt`             the places of one kind
  `rootsInFront`        how many roots the declared rounds send before a place
  `refuser`, `orLoud`   a block that refuses, for a place whose block could not be made
  `stretched`           the places, each with its declared rounds and the roots sent before it
  `readsQuietAt`        a block without a round, after the commitment before the smallness test

Why `refuser`: a function that returns `none` for a block can be dropped in silence by a `filterMap`
or a `bind`, and the place would stay empty. A lot puts `refuser` there instead.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.ProofFile.Places
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.First.Att.ReadsO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

section
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First

/-- The places of one kind; the empty list where `spotsOf` returns `none`. -/
def spotsAt (Z : Pub) (k : KindName) : List Spot :=
  ((spotsOf Z.cuts).getD []).filter fun p => p.place.kind == k

/-- The roots that the first chain's declared rounds send before a place; `none` if no place has
that name. -/
def rootsInFront (Z : Pub) (name : String) : Option Nat :=
  (spotsOf Z.cuts).bind fun ps =>
    if ps.any (·.name == name) then
      let k := (ps.takeWhile (·.name != name)).foldl
        (fun n p => n + p.cuts.foldl (fun a c => a + c.take) 0) 0
      some ((Z.D.1.take k).foldl (fun n d => n + d.entry.roots) 0)
    else none

end

section
open VerifiableInference.Desc (Block Place roundlessBlock)
open VerifiableInference.Desc.First

/-- A block that fails its test on the plan and refuses every file. `what` goes into the refusal's
words. -/
def refuser (name : String) (a : Place) (what : String) : Block S Unit :=
  { (roundlessBlock name a.chain a.link a.piece
      (fun _ => .error ("no block could be made for this place: " ++ what)) : Block S Unit) with
    place := a, planOk := false }

/-- The block, or `refuser` where there is none. -/
def orLoud (name : String) (a : Place) (what : String) : Option (Block S Unit) → Block S Unit
  | some b => b
  | none => refuser name a what

end

section
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First

/-- The places, each with its stretch of the declared rounds and the number of roots sent before
it. `n`: the roots sent before the first place. -/
def stretched : List Spot → List Fmt.DeclaredRound → Nat → List (Spot × List Fmt.DeclaredRound × Nat)
  | [], _, _ => []
  | p :: ps, ds, n =>
    let k := p.cuts.foldl (fun a c => a + c.take) 0
    (p, ds.take k, n) ::
      stretched ps (ds.drop k) (n + (ds.take k).foldl (fun a d => a + d.entry.roots) 0)

end

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First

/-- The block without a round for segment `l` that is joined after the commitment that comes before
the smallness test: at piece 4 of a segment for feed-forward or attention layers, at piece 5 of the
head's. `none` at another piece. -/
def readsQuietAt (G : Ground) (l : Nat) (X : OnBytes.Model.Stages.LinkH) (piece : Nat) :
    Option (Block S Unit) :=
  if X.kind == 1 then (if piece == 4 then Att.readsAtO G.W l X.g else none)
  else if piece == (if X.kind == 0 then 4 else 5) then
    VerifiableInference.Desc.K8.ReadsQuiet.blockAt G.W.G G.W.hS G.W.HLy G.W.H
      (G.built.toList.map fun Y => (Y.kind, Y.g)) l
  else none

end

end ProofFile
