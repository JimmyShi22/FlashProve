-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/PackList.lean: for every sending of oracle messages in the seven plans of the verifier on
bytes, the sampled messages' shapes, each with a decoding radius, computed from the three public
files.

For the hypothesis on numbers in Johnson/Top/H/Packing.lean [not in this library]. Definitions, one
lemma, and tests by
evaluation.
Main names:
  `packListOf`: one element for each sending, in the order key 0, 1, 2, entry 0, proof 0, 1, 2 and,
    within a chain, of sending: the chain's codes, and the shapes of the sampled messages
    (answers > 0) in the order of sending, each with one radius, in positions out of
    2 ^ (Johnson.Pack.aOf codes shape).
  `packSmall`: that list at the small example whose three public files the library already holds as
    values (OnBytes/Model/TestRecordWork.lean, OnBytes/Params/SmallFiles.lean).
The radius: the planner prices a message's sample by one or several groups of rows. For each such
group `Params.analysis` gives the distance delta of its main and of its mask code as an interval.
The radius is `Params.upperRadius` (OnBytes/Params/JohnsonLaws.lean) of that distance at the code's
length: the upper end times the length, rounded down; for the main code if the shape has main rows,
else for the mask code (`radiusIn`); with several groups, the largest. For a shape with main rows
and a group under the rule of the Johnson radius it is the radius that Johnson/Top/H/StageJ.lean
gives the group (`radiusIn_main`).
The map from a message to its groups: the k-th sending of a chain (Johnson/G/Sends.lean) goes with
the k-th sending among the chain's calls (Johnson/G/Calls.lean); within a sending the sampled
messages, in order, go with the samples, in order; one sample for several messages serves each.
`packListOf` refuses unless, besides equal counts: (p1) each group's code is the shape's code in
length, message length and random entries: the main code if the shape has main rows, else the mask
code; (p2) `Johnson.Pack.bitsZ codes shape` is the sample's number of cube bits; (p3) the entry
behind "SEND seed" takes in as many answers as there are sampled messages times the setting's
samples; (p4) the entry "SEND seed" draws samples times (the largest cube's bits + 1) elements;
(p5) where the shape has both kinds of rows, the group's mask code is the shape's too.
Whence the numbers of the tests: Lean's evaluator, at the library's own copies of the three shipped
public files of prover/examples/target_small_f2_roomy (the two files named above). No other file is
read.
Limits: no theorem on the list is stated; the tests are evidence by evaluation at one example. The
map is a reading of the planner's and the verifier's text, held by (p1) to (p5). A group's distance
hangs on its main code, its mask code, its rule and its integer m; (p1) and (p5) compare codes only.
So what the five leave open is: which of several groups that agree in the compared codes a message
goes with (for a shape with rows of one kind only the other code is not compared; rule and m never
are: `Planned.oneDistance` makes the rounds of one plan that say the same two codes say the same
rule and m, but by its own docstring it does not reach the lists that a sample reads); and the order
among messages that agree in codes, cube and answers. At the frame's sendings (p2) compares two
lists that are both written here (`frameSends`, `nFrame`); what ties them to the planner is (k1) and
(k2) of Johnson/G/Calls.lean, through the error and the draws of "SEND seed". A shape with both
kinds of rows gets the main code's radius: a group has one joint distance (`Analysis.maskAt` is the
mask code at the same distance). Messages that are not sampled are left out.
-/
import Johnson.Pack.Check
import Johnson.Pack.PortS
import Johnson.G.Sends
import OnBytes.Model.TestRecordWork
import OnBytes.Params.JohnsonLaws
import Johnson.Top.H.StageJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params

/-- The samples of the sendings that a call makes, one list for each sending. -/
def Call.sendSamples : Call → List (List SampleSize)
  | .send o _ _ => [o]
  | .cs _ y cube _ _ _ => [[⟨cube, [y]⟩]]
  | .linFirst x => [x.w :: x.besideW]
  | .linShared _ x => [[x.u], x.omega :: x.besideOmega]
  | .link _ u => [[u]]
  | _ => []

/-- A code of a chain's list and a code as the planner sizes it agree in their three numbers. -/
def sameCode (c : Option Code) (x : CodeSize) : Bool := c == some ⟨x.logN, x.ell, x.r⟩

/-- The radius of a shape in a group, in positions. -/
def radiusIn (s : Setting) (sh : OracleShape) (g : GroupSize) : Nat :=
  let a := analysis s g
  if sh.mainRows != 0 then upperRadius a.mainAt.delta (2 ^ g.main.logN)
  else upperRadius a.maskAt.delta (2 ^ g.mask.logN)

/-- For a shape with main rows, in a group under the rule of the Johnson radius. -/
theorem radiusIn_main (s : Setting) (sh : OracleShape) (g : GroupSize) (h : g.rule = .johnson)
    (hm : sh.mainRows ≠ 0) : radiusIn s sh g = Johnson.Top.H.radiusOf s g := by
  unfold radiusIn Johnson.Top.H.radiusOf upperRadius analysis
  simp [h, hm, wordOf, Word.n]

/-- The radius of one sampled message, from the groups that price its sample. -/
def radiusFor (s : Setting) (codes : Codes) (at_ : String) (sh : OracleShape) (sm : SampleSize) :
    Except String Nat := do
  if sm.groups.isEmpty then throw s!"{at_}: a sampled message whose sample has no group"
  unless Johnson.Pack.bitsZ codes sh == sm.cubeBits do
    throw s!"{at_}: (p2) the shape's cube has not the sample's bits"
  sm.groups.foldlM (fun r g => do
    let main := sh.mainRows != 0
    unless (if main then sameCode codes.base[sh.code]? g.main
        else sameCode codes.mask[sh.maskCode]? g.mask) do
      throw s!"{at_}: (p1) the group's code is not the shape's"
    unless !(main && sh.maskRows != 0) || sameCode codes.mask[sh.maskCode]? g.mask do
      throw s!"{at_}: (p5) the group's mask code is not the shape's"
    let logN := if main then g.main.logN else g.mask.logN
    unless Johnson.Pack.aOf codes sh == logN do
      throw s!"{at_}: the length at which the radius counts is not the code's own"
    pure (max r (radiusIn s sh g))) 0

/-- For every sending: its chain's codes and its sampled messages' shapes, each with a radius. -/
def packListOf (pol lay KL : ByteArray) :
    Except String (List (Codes × List (OracleShape × Nat))) := do
  let (s, chains) ← callsOf pol lay KL
  let sends ← sendsOf pol lay KL
  let per ← (chains.zip sends).mapM fun (c, d) => do
    let smp := c.calls.flatMap Call.sendSamples
    unless smp.length == d.sends.length do
      throw s!"{c.file} {c.chain}: the calls and the list have not as many sendings"
    (smp.zip d.sends).mapM fun (o, x) => do
      let at_ := s!"{c.file} {c.chain}, entry {x.entry} ({x.label})"
      let sampled := (x.sent.filter fun m => 0 < m.shape.answers).map (·.shape)
      let o' :=
        if o.length == sampled.length then o
        else if o.length == 1 then List.replicate sampled.length (o.headD ⟨0, []⟩) else []
      unless o'.length == sampled.length do
        throw s!"{at_}: the sampled messages and the samples are not as many"
      let l ← (sampled.zip o').mapM fun (sh, sm) => do
        pure (sh, ← radiusFor s d.codes at_ sh sm)
      unless x.behind.answers == l.length * s.samples do
        throw s!"{at_}: (p3) the entry behind takes in another number of answers"
      unless x.seed.drawE == s.samples * (Johnson.Pack.bMax d.codes l + 1) do
        throw s!"{at_}: (p4) the entry draws another number of elements"
      pure (d.codes, l)
  pure per.flatten

open OnBytes.Model.Verify OnBytes.Params in
/-- The list at the small example that the library holds; empty if the making refuses. -/
def packSmall : List (Codes × List (OracleShape × Nat)) :=
  (packListOf (TestRecordWork.policyOf TestRecordWork.smallHead) SmallFiles.layout
    SmallFiles.scales).toOption.getD []

-- 46 sendings, none without a sampled message, 64 sampled messages
#guard packSmall.length == 46
#guard packSmall.all fun x => !x.2.isEmpty
#guard (packSmall.map (·.2.length)).sum == 64
-- the test of Johnson/Pack/Check.lean holds at each; with each radius raised to the whole length
-- it fails at each
#guard packSmall.all fun x => Johnson.Pack.allMeet x.1 x.2
#guard packSmall.all fun x => x.2.all fun y =>
  !Johnson.Pack.meetsB x.1 y.1 (2 ^ Johnson.Pack.aOf x.1 y.1)

end Johnson.G
