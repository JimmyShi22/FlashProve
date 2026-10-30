-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K1.lean: the kind K1's lot for a proof file's description: its own blocks
at its places inside the links of the first chain, made of public values
(Johnson/Desc/ProofFile/LotCore.lean: Lot).

This file holds definitions only; no theorem is stated.

The places: link 0's first place (firstSegmentOpening, by itself: the quiet step that enters link 0 is the
link's frame's); each link's reads; each link's digits. W's place, behind the links, is not in this
lot: Johnson/Desc/ProofFile/Lot/K13At4.lean holds both its steps (K1's wAt, by import, and K13's
rowsB).

The quiet step behind the reads is handed in: quiet G l X is the block without a round that stands
behind the reads' sending at link l (at a layers' link and at the head's:
Johnson/Desc/K8/ReadsQuiet.lean; at an attention link: Johnson/Desc/First/Att/ReadsBlock.lean). It
is laid behind K1's block by Block.andThen, under K1's block's name and place. Where none is handed
in, K1's block stands by itself. A seat that joins the quiet steps itself calls
lotWith (fun _ _ _ => none).

letters := false: no block of this lot reads a token of the request.

Two arguments serve a harness's controls and are the identity by default: tw turns the kind's own
block at one place; tq turns the chain's parameters of which one place's block is made.

What it imports: of the description's maker LotCore alone; no stand-in for a step of
`verify-on-bytes`, no control, no other kind's text.

Main names: B, Quiet, linkNumbers, blocks, gpOf, lotWith.

What is not claimed. That the places are all of the kind's places on a plan. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

abbrev B : Type := Block S Unit

/-- The quiet step behind the reads, as it is handed in: the letters, the link's number, the link as
built. -/
abbrev Quiet : Type := ProofFile.Ground → Nat → Stages.LinkH → Option B

/-- A link's two places: the pieces, and the arrays that the plan names at the reads and at the
digits. -/
def linkNumbers (G : ProofFile.Ground) (X : Stages.LinkH) :
    Option (Nat × Nat × Option (List Nat) × Option (List Nat)) :=
  if X.kind == 0 then
    (G.W.G[X.g]?).map fun hp =>
      (4, 6, (hp.tl.ix.U.getD 2 none).map ([·]), some [hp.tl.ix.ZZ, hp.tl.ix.BZ])
  else if X.kind == 1 then
    (G.W.A[X.g]?).map fun p => (4, 6, some [p.iU3], some [p.seam.tl.ix.ZZ, p.seam.tl.ix.BZ])
  else
    some (5, 7, (G.W.H.tl.ix.U.getD 2 none).map ([·]), some [G.W.H.tl.ix.ZZ, G.W.H.tl.ix.BZ])

/-- **The lot's blocks.** -/
def blocks (gp : GPar) (quiet : Quiet) (G : ProofFile.Ground) (tw : Place → B → B := fun _ b => b)
    (tq : Place → Params.First → Params.First := fun _ q => q) : List B :=
  let q := fun (link : Option Nat) (piece : Nat) => tq ⟨1, link, piece, .K1⟩ G.first
  let own := fun (b : B) => tw b.place b
  let links := G.built.toList.zipIdx.flatMap fun (X, l) =>
    match linkNumbers G X with
    | none => []
    | some (pr, pd, reads, digits) =>
      let k := own (laterAt (q (some l) pr) gp l pr 1 reads)
      let r := match quiet G l X with
        | some z => k.andThen k.name z
        | none => k
      [r, own (laterAt (q (some l) pd) gp l pd 2 digits)]
  [own (firstSegmentOpening (q (some 0) 1) gp)] ++ links

/-- The two numbers of the plan that the ground's functions take. -/
def gpOf (Z : ProofFile.Pub) : GPar := { samples := Z.P.samples, firstTree := Z.P.firstTree }

/-- **K1's lot**, with the quiet step behind the reads handed in. -/
def lotWith (quiet : Quiet) (Z : ProofFile.Pub) : ProofFile.Lot :=
  { name := "K1: the first segment's opening, each link's reads and digits"
    letters := false
    own := fun G => blocks (gpOf Z) quiet G }

end VerifiableInference.Desc.K1
