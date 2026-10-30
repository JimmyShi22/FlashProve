-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileOfAnySize.lean: THE PILE's FILLER AS A FUNCTION OF THE PUBLIC
PART AND THE GROUND ALONE, AT ANY NUMBER OF SEGMENTS, in the type in which K13's lot (`k13Lot`,
Part.lean of this folder) takes it; the same held as a field; and a lot that reads that field where
its halves are made. NINE DEFINITIONS, WITH CODE, AND ONE STRUCTURE; no theorem. What is shown of
them: PileOfAnySizeAll.lean (at every size) and PileOfAnySizeAt.lean (under the library's one
hypothesis at the full size) of this folder; and DefaultsIdle.lean there (`q0Idle`).

FIRST. THIS FILE DEFINES PART OF WHAT THE HONEST PROVER READS: `pileOfAnySize` is a filler for the
field of the small input that makes the pile's rows. OF A ROW's FOUR FIELDS IT MAKES TWO: the
weights g and the column point psi. THE MASK FORM AND THE TARGET ARE PLACEHOLDERS, the empty form
and 0 (`pileRowAt`, Johnson/Desc/K13/Honest/PileDefs.lean): as rows these are not the verifier's
pending rows; the kind's part reads g and psi alone (Part.lean). By its type the filler reads no
weight, no coin and no witness: it is handed the public part, the ground, the instance, which is
public, and a list of challenges; that these are the challenges in front is the caller's doing
(`k13Job`, Part.lean, hands it those heard). NO FILE UNDER lean/Johnson/Goal/ IS IMPORTED, directly
or through another file: so nothing that is declared there can be named. No file of the tree
evaluates the filler.

NO NUMBER OF THE FULL SIZE IS WRITTEN HERE: not the twelve groups of layers, not the head's segment
24, not a sub-protocol's number in the flat list. Which segments have a site, which of them is the
head's, and each segment's group are read off the public part (`mergeSitesOf`, `headSegOf`,
`groupOfSeg`: SitesOfDefs.lean of this folder). A sub-protocol's number in the flat list is the
library's `IM.flatIx c l i` (Johnson/IMR/FlatIx.lean), at its segment l and at its number i in front
of the segment's batching.

WHAT `IM.flatIx` IS, AND WHAT IS WRITTEN. NOTHING IS SEARCHED, AND NOTHING CAN BE "NOT FOUND":
`IM.flatIx` is a sum of lengths: past the chain's segments, or past a segment's list, it is still a
number, and `roundsAhead` past the list's end is the count of all rounds. NO DEFINITION HERE TESTS
THAT A SUB-PROTOCOL OF THE KIND K3, K4, K6 OR K11 STANDS AT THE NUMBER. Written, here and in
SitesOfDefs.lean, are the numbers in front of the batching: 1 and 2 at a layers' segment; 2, 3 and 8
at the head's: they follow the order of the kinds in a segment (`kindsBeforeBatching`,
Johnson/Desc/First/Driver/Chain.lean), which is the library's at every size.

A SITE GOES BY THE SEGMENT's SORT; THE VERIFIER's ROW BY ANOTHER FIELD. `mergeSitesOf` lays a site
at each layers' segment and at the head's. The verifier's text lays a pending row where the built
segment's field fv says so (OnBytes/Model/StagesLinks.lean). The two agree where the plan's own test
holds (`planFlag`, Johnson/Desc/First/Walk/Frame.lean), and at every plan that `listLinksH`
(StagesLinks.lean) builds. THE FILLER ASKS NO TEST ON THE PLAN: at a layers' or a head's segment
whose fv is false the site either has 0 claims, and then there is no row at all; or, where every
site's row can be made, the pile holds a row that the verifier does not lay.

THE CHAIN. The filler is written over a first chain of the IOP as written in Lean; here that chain
is what the library's `onlineFirstChainAt` makes of the public part. Two cautions of that definition's own
head hold here. It does not ask the two tests (`faultsAt`, `lackingAt`) that the maker of the IOP as
written in Lean asks before: SO IT CAN YIELD A CHAIN WHERE THAT MAKER REJECTS. And the chain does
not hang on the format's second hash function.

HOW HEAVY, AND THE FIELD. Of the chain the body reads counts alone: of rounds, and of sub-protocols
(`IM.flatIx`). For these the whole chain is made. BY A TEST OUTSIDE THE TREE, IN LEAN's EVALUATOR:
`pileOfAnySize … Z G` makes nothing until the instance and the challenges come, AND THE CHAIN IS
MADE ANEW AT EACH CALL; the kind's part calls the filler in every round of its sumcheck. `PileBox`
holds a filler as a field. By the same test, where a value of it is held before the calls,
`pileBoxOfAnySize … Z G` makes the chain then, and the calls of its field do not make it again;
where the holder is inlined into the calls, nothing is spared. `k13LotOnce` asks for the field at
each making of its halves, in front of the list, and lays the kind's half at the filler in it; by
that test the chain is made there. It is `k13Lot` at that filler by definition
(PileOfAnySizeAll.lean). Beside the chain, each call makes each site's claims and row anew: that
work is spared by nothing here. In native code nothing has been timed.

WHERE IT YIELDS NO ROW OR A DEFAULT, IN SILENCE.
  No row at all: where `onlineFirstChainAt` rejects (the name under which it rejected is dropped); ALL OR
    NOTHING (`pileBySites`): where one site's row cannot be made: among the causes: too few
    challenges from a site's batching round on (`mergeDraws`), other claims than the plan's number,
    no claim, a layout that does not fit the shape (`rowReadsOf`).
  A default for a thing that is lacking: the default shape where the list of the lookups' sites has
    none on the calls of a segment (`callsShapeAt`): that there is one is shown at no general public
    part · the number of segments where none is the head's (`headSegOf`) · 0 where there is no such
    segment (`groupOfSeg`, `nclOfSeg`) · the blank plan, and 0 added to the batching round's number,
    where the public data have no plan of the group (`k4PubOfSeg`, `sigOfSeg`) · the empty array,
    not nothing, where the head's claim cannot be made (`headArmOfSeg`).
  Taken over from what is called: every sort of segment but the layers' and the attention's counts
    as the head's (the library's) · the request's tokens are read off `ProofFile.startS`, which is the
    blank, failed state where the request's own tests fail · a round not heard, or with fewer
    samples than are read, counts as zeros in the key points (`keyPtsAt`, Honest/K3/Heard.lean) ·
    the reply's first word, and the number of the vector U3 in the head's list of arrays, count as 0
    where they are lacking (`headRunAt`, Honest/K11/Claims.lean; the claim does not read the second:
    `weightsClaim_reads` there) · no site at all where the table of places cannot be made
    (`lookSites`, Honest/K3/Lot.lean).
  THE ORDER OF THE ROWS: `mergeSitesOf` lists the sites in the segments' order; `pileBySites` wants
    the order in which the segments are cleared along the chain: NOTHING TESTS IT.
  TWO SOURCES OF ONE LAYOUT: the rows are made at the layout of the public part, the head's claim at
    that of the ground: NOTHING IN THE FILLER's TYPE TIES THE GROUND TO THE PUBLIC PART.

THE HEAD's CLAIMS ARE A PARAMETER. `pileAtChain` takes them as headArm, `pileOfAnySize` as armOf.
`headArmOfSeg` lays them by the kind K11's own text "at two numbers" (`headClaimsN`,
Honest/K11/ClaimsN.lean); the closed terms `pileAnyK3`, `pileBoxAnyK3` stand at it.
`headClaimsByPlace` of that file finds the three numbers otherwise: the segment off the ground, the
counts by the places of the kinds K3 and K6. THAT THE TWO WAYS GIVE THE SAME NUMBERS AT A GENERAL
PUBLIC PART IS SHOWN NOWHERE.

ON `q0Idle`. That Q₀ is idle in `claimsTextOf` at every size is `claimsTextOf_any_q0`
(DefaultsIdle.lean of this folder), under no premise; so the filler is one function at every value
in that place (`pileOfAnySize_any_q0`, there).

ON WHAT IT LEANS. Part.lean (`PileOf`, `proverSideOfClaimCombination`), SitesOfDefs.lean, LightLook.lean (`lookZkAt`) of
this folder; Johnson/Desc/K13/Honest/PileDefs.lean (`pileBySites`), FoldCut.lean (`roundsAhead`);
Honest/K11/ClaimsN.lean, KeysAtLink.lean; `onlineFirstChainAt`, `IM.flatIx`. THROUGH SitesOfDefs.lean:
ClaimsIsLayers.lean (`layersClaims`), and so kind K4's laws on the claims and files of
Honest/SumLaw/ lie beneath this file. It imports, directly or through another file, no file of
Honest/Thread/ or Honest/K3/Law/Thread/ (the walk along the first chain, and the laws on it).
Main names:
  `pileOfAnySize`, `pileAnyK3`: **the filler; a closed term.** `pileAtChain`: over a chain.
  `PileBox`, `pileBoxOfAnySize`, `pileBoxAnyK3`, `k13LotOnce`: **the filler held as a field, and the
    lot that reads it where its halves are made.**
  `lookOfSeg`, `headArmOfSeg`, `q0Idle`: its parts.

IN THE LIBRARY, under the one hypothesis at the full size: PileOfAnySizeAt.lean of this folder
(`pileOfAnySize_at`).

What is not claimed. Anything: no theorem. That the filler yields a row at any data. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.LinkAt
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.K13.SitesOfDefs
import Johnson.Desc.ProofFile.Honest.K13.LightLook
import Johnson.Desc.ProofFile.Honest.K11.ClaimsN

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (roundsAhead pileBySites)

/-! ## What the claims read of the lookups and of the head, by the segment -/

/-- What the lookup on the calls of a layers' segment l returns, as far as the claims read it: each
call's key point alone (`lookZkAt`, LightLook.lean of this folder), at the shape of that lookup
(`callsShapeAt`, Honest/K11/KeysAtLink.lean) and at the count of the rounds in front of it. That
lookup is the second sub-protocol in front of the segment's batching. The instance is not read. -/
def lookOfSeg (Z : ProofFile.Pub) (c : Chain S ProofFile.Cl) :
    Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard :=
  fun l _ hd => lookZkAt (K11.callsShapeAt Z l) (roundsAhead c.blocksInOrder (IM.flatIx c l 1)) hd

/-- **The claims at the head's segment**: the text of the claims that the head's merge merges, "at
two numbers" (`headClaimsN`, Honest/K11/ClaimsN.lean), as an array: at the head's segment
(`headSegOf`), at the count of the rounds in front of the lookup on its calls and at that in front
of the output head's own sub-protocol: the third and the fourth sub-protocol in front of the
segment's batching. WHERE THAT TEXT YIELDS NO CLAIM THIS IS THE EMPTY ARRAY, NOT NOTHING. -/
def headArmOfSeg (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim) :=
  fun x hd =>
    some (K11.headClaimsN (headSegOf Z) (roundsAhead c.blocksInOrder (IM.flatIx c (headSegOf Z) 2))
      (roundsAhead c.blocksInOrder (IM.flatIx c (headSegOf Z) 3)) Z G x hd).toArray

/-! ## The filler -/

/-- A written value for the parameter Q₀ of `claimsTextOf`: the layers' public data of the public
part, the blank plan, and 0 in every number. -/
def q0Idle (Z : ProofFile.Pub) : Nat → K4Pub :=
  fun _ => { P := Z.p.X.layers, hp := blankHPlan, g := 0, link := 0, piece := 0, r0 := 0, seg := 0 }

/-- **THE PILE's FILLER OVER A FIRST CHAIN, AT ANY NUMBER OF SEGMENTS**: one row for each segment
that merges claims on the weights (`mergeSitesOf`), over the text of the claims (`claimsTextOf`):
SitesOfDefs.lean of this folder. headArm: the claims at the head's segment: a parameter. Q₀: a
parameter. ALL OR NOTHING: where one site's row cannot be made there is no row. -/
def pileAtChain (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    PileOf ProofFile.Inst :=
  pileBySites Z.p.X.layers.wsLay Z.first.lin (mergeSitesOf c Z)
    (claimsTextOf c Z (lookOfSeg Z c) headArm Q₀)

/-- A filler, held as a field. Why: the head, under "How heavy, and the field". -/
structure PileBox where
  run : PileOf ProofFile.Inst

/-- **The filler of the public part and the ground, held as a field**: `pileAtChain` at the chain
that the library's `onlineFirstChainAt` (Johnson/Desc/ProofFile/LinkAt.lean) makes of the public part.
WHERE `onlineFirstChainAt` REJECTS IT YIELDS NO ROW. -/
def pileBoxOfAnySize
    (armOf : Chain S ProofFile.Cl → ProofFile.Pub → ProofFile.Ground →
      ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim))
    (Q₀ : ProofFile.Pub → Nat → K4Pub) (Z : ProofFile.Pub) (G : ProofFile.Ground) : PileBox :=
  match ProofFile.onlineFirstChainAt Z with
  | .ok c => ⟨pileAtChain c Z (armOf c Z G) (Q₀ Z)⟩
  | .error _ => ⟨fun _ _ => []⟩

/-- **THE PILE's FILLER, OF THE PUBLIC PART AND THE GROUND ALONE, AT ANY NUMBER OF SEGMENTS**, in
the type in which `k13Lot` takes it. -/
def pileOfAnySize
    (armOf : Chain S ProofFile.Cl → ProofFile.Pub → ProofFile.Ground →
      ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim))
    (Q₀ : ProofFile.Pub → Nat → K4Pub) : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst :=
  fun Z G => (pileBoxOfAnySize armOf Q₀ Z G).run

/-- A closed term, held as a field. -/
def pileBoxAnyK3 : ProofFile.Pub → ProofFile.Ground → PileBox := pileBoxOfAnySize headArmOfSeg q0Idle

/-- **A CLOSED TERM.** -/
def pileAnyK3 : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst := pileOfAnySize headArmOfSeg q0Idle

/-- **K13's lot over a filler that is held as a field**: the field is read at each making of the
halves, in front of the list. It is `k13Lot` at that filler (PileOfAnySizeAll.lean of this folder:
by definition). -/
def k13LotOnce {W₀ Rc Tr X : Type} (weights : W₀ → Weights)
    (box : ProofFile.Pub → ProofFile.Ground → PileBox) :
    HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X :=
  { name := "K13: the members' batching"
    halves := fun Z G =>
      let b := box Z G
      [proverSideOfClaimCombination weights b.run (VerifiableInference.Desc.K13.whereOf Z)] }

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.lookOfSeg
#print axioms ProofFile.Honest.K13.headArmOfSeg
#print axioms ProofFile.Honest.K13.q0Idle
#print axioms ProofFile.Honest.K13.pileAtChain
#print axioms ProofFile.Honest.K13.pileBoxOfAnySize
#print axioms ProofFile.Honest.K13.pileOfAnySize
#print axioms ProofFile.Honest.K13.pileBoxAnyK3
#print axioms ProofFile.Honest.K13.pileAnyK3
#print axioms ProofFile.Honest.K13.k13LotOnce
#print axioms ProofFile.Honest.K13.PileBox
