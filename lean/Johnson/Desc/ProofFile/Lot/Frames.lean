-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/Frames.lean: the links' frames as a lot of blocks for the proof file's
description: the blocks alone. It imports the record of a lot (LotCore.lean) and the frame's value
(Johnson/Top/H0/Walk/FrameLot.lean), and nothing that is weakened, planted or a run.

  blocksOf Z   for each row of framesOf (every link of the first chain, the head's among them):
               frameBlocks f.link f.plan f.lay f.opened f.clear 1 f.last: three blocks without a
               round, of the kind "frame"
  lot Z        the lot; letters := false: THE LETTERS COME OUT OF THE PUBLIC PART Z ALONE
               (Z.p.built.links, Z.first, Z.p.X): no token of a request can reach a block

At the head's link (pieces 1 and 15): lay is layFront, the front test alone; "opened" hands the
record on; clear is tailHead (Johnson/Desc/First/Close/TailHead.lean; `verify-on-bytes`'s step
"H.10.quiet"). THE STEP THAT ENTERS THAT LINK, "H.1.quiet", IS NOT THE FRAME's: it is the code
switch's headOpened, inside its block at H:2. By reading Frames1.lean (filledLinks: the fold counts
a block at "link l: laid" as the link's entering): with this lot seated "H.1.quiet" is cut out of
H:2's stand-in and told under "link (head): laid" as this lot's. SO THIS LOT WANTS THE CODE SWITCH's
LOT AT H:2 BESIDE IT; and that line of a print names the wrong lot.

Where framesOf refuses (a link's letters are not there) the lot gives one block at the place of
"link 0: laid" (its own name: "link 0: lay") that refuses under framesOf's own words: a missing
letter says no: it does not pass in silence.

Whence the letters: Z.p.built.links and Z.p.X are the built records of the program
`verify-on-bytes`'s model (Stages.LinkH; Verify.Public, OnBytes/Model/VerifyPublic.lean), Z.first is
Params.First: see FrameLot.lean and FrameSeat.lean.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Top.H0.Walk.FrameLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20
open ProofFile
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame)

/-- The frames' blocks. -/
def blocksOf (Z : Pub) : List (Block S Unit) :=
  match framesOf Z.p.built.links Z.first Z.p.X with
  | .ok fs => fs.flatMap fun f => frameBlocks f.link f.plan f.lay f.opened f.clear 1 f.last
  | .error e => [roundlessBlock "link 0: lay" 1 (some 0) 0 fun _ => .error e]

/-- The lot: the blocks alone. -/
def lot (Z : Pub) : Lot :=
  { name := "the links' frames"
    letters := false
    own := fun _ => blocksOf Z }

end P1L20
