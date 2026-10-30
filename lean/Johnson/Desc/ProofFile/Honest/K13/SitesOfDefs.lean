-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/SitesOfDefs.lean: THE SITES AND THE CLAIMS' TEXT OF THE PILE's
FILLER AT ANY SIZE: DEFINITIONS ALONE. `mergeSitesOf`: the public numbers of `sitesAt`
(SitesAtFlat.lean of this folder); `claimsTextOf`: `claimsText` (ClaimsText.lean of this folder):
BOTH WITH NO WRITTEN NUMBER OF SEGMENTS OR SUB-PROTOCOLS IN THEM. Ten definitions; no statement.
That in the goals' scope they are the written ones: SitesOfLaws.lean of this folder.

Why. The two written texts are made for the full size: twelve groups of layers at the numbers 28 g
+ 4, the head at segment 24 and the number 346. At public files of another size they name
sub-protocols that are not there. Here each number is reckoned from its place on the chain.
Why a file of its own. A caller that only wants to RUN the filler is spared the files on the scope
and on the sites: this file imports neither SitesAtFlat.lean nor ClaimsText.lean, nor a file under
Johnson/Goal/. NOT SPARED: through ClaimsIsLayers.lean (`layersClaims`) kind K4's laws on the claims
(Honest/K4/Law/ClaimsAre.lean and what lies beneath it) and files of Honest/SumLaw/ lie beneath.
Whence each is read. Which segments there are, and of which sort: `ProofFile.subsOf Z`
(Johnson/Desc/ProofFile/Frames1.lean): off the built plan. A segment's group of layers and its
number of claims on the weights: the fields g and NCL of the built segment (`Stages.LinkH`,
OnBytes/Model/StagesLinks.lean); K4's own lot reads the same field, of the records that it is handed
(Johnson/Desc/ProofFile/Lot/K4.lean).
A sub-protocol's number: the library's `IM.flatIx c l i` (Johnson/IMR/FlatIx.lean): the number, in
the chain's flat list, of sub-protocol number i in front of the batching of segment l. By
`kindsBeforeBatching` (Johnson/Desc/First/Driver/Chain.lean) K4 is number 2 there and, in the head's segment,
K11 number 8.
`groupOfSeg Z l`, `nclOfSeg Z l`: the group, and the number of claims, of segment l; 0 where the
plan has no such segment.
`headSegOf Z`: **the number of the head's segment**: the first place of the sort head in `ProofFile.subsOf
Z`; the list's length where there is none.
`sigOfSeg`, `mergeSiteOfSeg`: a segment's batching round; its public numbers, by its sort; an
attention segment has none.
`mergeSitesOf c Z`: **THE SITES' PUBLIC NUMBERS**, in the segments' order.
`k4PubOfSeg`, `claimsTextOf`: **THE CLAIMS' TEXT**: at the head's segment headArm; at every other
segment l the list of claims that the honest parts' function makes at that segment's group. lookAt
and Q₀ go BY THE SEGMENT's number, not by the group's.
WHERE THESE DEFINITIONS FALL SILENT. None of them tests anything; each has a value at every input.
(1) NOTHING IS SEARCHED. `IM.flatIx` is a sum of lengths: past the chain's segments, or past a
segment's sub-protocols, it is still a number, and `roundsAhead` past the list's end is the count of
all rounds. No definition here tests that a sub-protocol of the kind K4 or K11 stands at the number
named.
(2) A SITE IS DECIDED BY THE SEGMENT's SORT. The verifier lays a row by another field of the same
built segment: fv. The two agree where the plan's test `planFlag` holds
(Johnson/Desc/First/Walk/Frame.lean), and at every plan that `listLinksH` builds
(OnBytes/Model/StagesLinks.lean); nothing here asks a test. At a layers' or a head's segment whose
fv is false the site either has 0 claims: then `rowReadsOf` (Johnson/Desc/K13/Honest/PileDefs.lean)
rejects it, and the filler, which is all or nothing, yields no row at all; or, where every site's
row can be made, the pile holds a row that the verifier does not lay.
(3) By the library's `ProofFile.subOf` (Johnson/Desc/ProofFile/FillCore.lean) every kind but 0 and 1 is
the head's.
(4) `sigOfSeg` adds 0, and `k4PubOfSeg` lays the blank plan, where the public data have no plan of
the segment's group.
(5) `smallInOf` reads the tokens off `ProofFile.startS` (Johnson/Desc/ProofFile/Pub.lean), which is the
blank state, marked as failed, where the tests on the request fail.
(6) `mergeSitesOf` lists the sites in the segments' order. `pileBySites` (PileDefs.lean) wants the
order in which the segments are cleared along the chain, and nothing tests it. By `Chain.blocksInOrder` and
`Link.blocksInOrder` (Johnson/Desc/Block.lean) the chain's own segments stand in the flat list in the order
of c.links, each with its clearing last. The chain c is a parameter of these definitions: nothing in
them ties the order of c.links to that of the built plan's segments.
(7) ONE HEAD IS TAKEN FOR GRANTED. By (3) a plan may have two segments that count as the head's:
`mergeSiteOfSeg` then lays a head's site at each, while `claimsTextOf` hands headArm at the first
alone (`headSegOf`) and at the other K4's list, at a group read off a head's record: a site's
numbers of one sort with a text of the other, with no mark. The library's test that there is one
head and that it is last (`headLast`, OnBytes/Model/StagesLinks.lean) is asked by nothing here.
THREE DEFINITIONS HAVE THE TEXT OF AN EARLIER ONE, TYPED ANEW SO THAT THIS FILE NEED NOT IMPORT THE
FILES THAT HOLD THESE: `nclOfSeg` is `nclAt` (SitesAtFlat.lean); `blankHPlan` is `blankPlan`
(K4PubsTerm.lean); `smallInOf` is `smallIn` (ClaimsText.lean). Each pair is shown to be one in
SitesOfLaws.lean.
`nclOfSeg`'s text also stands in the library, as the field ncl of `d1At`
(Johnson/Top/H0/Fill/D1At.lean).

What is not claimed. Anything: this file states nothing. At an attention segment `claimsTextOf` has
a value and no meaning. lookAt, headArm, Q₀: free parameters. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ClaimsIsLayers
import Johnson.Desc.K13.Honest.MergeLayers
import Johnson.IMR.FlatIx
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub K4In)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.K13.Honest (MergeSite SiteClaims roundsAhead layersSigmaAt)
open ProofFile (Cl)

/-! ## The sites -/

/-- The group of layers of segment l, off the built plan; 0 where the plan has no such segment. -/
def groupOfSeg (Z : ProofFile.Pub) (l : Nat) : Nat := ((Z.p.built.links[l]?).map (·.g)).getD 0

/-- Segment l's public number of claims on the weights, off the built plan; 0 where the plan has no
such segment. It has the text of `nclAt` (SitesAtFlat.lean of this folder); the same text is the
field ncl of the library's `d1At` (Johnson/Top/H0/Fill/D1At.lean). -/
def nclOfSeg (Z : ProofFile.Pub) (l : Nat) : Nat := ((Z.p.built.links[l]?).map (·.NCL)).getD 0

/-- **The number of the head's segment**: the first place of the sort head in the row of sorts; the
row's length where there is none. -/
def headSegOf (Z : ProofFile.Pub) : Nat := (ProofFile.subsOf Z).idxOf ModelPart.head

/-- The number, on the chain, of the batching round of segment l's merge. head: the segment is the
head's. At a layers' segment whose group has no plan in the public data, 0 stands for
`layersSigmaAt`. -/
def sigOfSeg (c : Chain S Cl) (Z : ProofFile.Pub) (head : Bool) (l : Nat) : Nat :=
  if head then roundsAhead c.blocksInOrder (IM.flatIx c l 8)
  else roundsAhead c.blocksInOrder (IM.flatIx c l 2) +
    ((Z.p.X.G[groupOfSeg Z l]?).map fun hp =>
      layersSigmaAt Z.p.X.layers hp (groupOfSeg Z l)).getD 0

/-- A segment's public numbers, by its sort, not by the built segment's flag fv. An attention
segment has none. -/
def mergeSiteOfSeg (c : Chain S Cl) (Z : ProofFile.Pub) : ModelPart → Nat → Option MergeSite
  | .layers, l => some ⟨l, nclOfSeg Z l, sigOfSeg c Z false l⟩
  | .attention, _ => none
  | .head, l => some ⟨l, nclOfSeg Z l, sigOfSeg c Z true l⟩

/-- **THE SITES' PUBLIC NUMBERS, AT ANY SIZE**, in the segments' order. -/
def mergeSitesOf (c : Chain S Cl) (Z : ProofFile.Pub) : List MergeSite :=
  (ProofFile.subsOf Z).zipIdx.filterMap fun x => mergeSiteOfSeg c Z x.1 x.2

/-! ## The claims' text -/

/-- A plan of a layers' sub-proof with every field empty or 0. It has the text of `blankPlan`
(K4PubsTerm.lean of this folder). -/
def blankHPlan : Layer.HPlan2 :=
  { tl := {}, Fp := {}, Tp := {}, nU := #[], ns := 0, used := 0, NCL := 0, nLin := 0, nBatched := 0
    lamS := 0 }

/-- **The public data of K4's honest parts at a layers' segment l, off the chain and what is
public.** Q₀: whence the fields link, piece and seg are taken, by the segment. -/
def k4PubOfSeg (c : Chain S Cl) (Z : ProofFile.Pub) (Q₀ : Nat → K4Pub) (l : Nat) : K4Pub :=
  { Q₀ l with
    P := Z.p.X.layers, hp := (Z.p.X.G[groupOfSeg Z l]?).getD blankHPlan, g := groupOfSeg Z l
    r0 := roundsAhead c.blocksInOrder (IM.flatIx c l 2) }

/-- The small input of K4's parts, as far as the claims read it: the tokens of the IOP's own first
state at the instance's public part (the blank state where the tests on the request fail); look: a
parameter; the cells and the weights' digits are laid 0: no claim reads them (`layersClaims_reads`,
ClaimsText.lean of this folder). It has the text of `smallIn` (the same file). -/
def smallInOf (Z : ProofFile.Pub) (look : ProofFile.Inst → List Fmt.Drawn → Forest.Heard) (x : ProofFile.Inst) :
    K4In :=
  { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := (ProofFile.startS Z x.pub).tokv, look := look x }

/-- **THE CLAIMS' TEXT, AT ANY SIZE.** At the head's segment: headArm. At every other segment l: the
list of claims that the honest parts' function makes at that segment's group. lookAt, Q₀: by the
segment. -/
def claimsTextOf (c : Chain S Cl) (Z : ProofFile.Pub)
    (lookAt : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (headArm : ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim)) (Q₀ : Nat → K4Pub) :
    SiteClaims ProofFile.Inst := fun l x hd =>
  if l = headSegOf Z then headArm x hd
  else layersClaims (k4PubOfSeg c Z Q₀ l) (smallInOf Z (lookAt l)) x hd

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.groupOfSeg
#print axioms ProofFile.Honest.K13.nclOfSeg
#print axioms ProofFile.Honest.K13.headSegOf
#print axioms ProofFile.Honest.K13.sigOfSeg
#print axioms ProofFile.Honest.K13.mergeSiteOfSeg
#print axioms ProofFile.Honest.K13.mergeSitesOf
#print axioms ProofFile.Honest.K13.blankHPlan
#print axioms ProofFile.Honest.K13.k4PubOfSeg
#print axioms ProofFile.Honest.K13.smallInOf
#print axioms ProofFile.Honest.K13.claimsTextOf
