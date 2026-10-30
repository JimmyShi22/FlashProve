-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardN.lean: tests on public data at an attention segment of the first chain.

The law on the segment's own rounds (K05_law_one, Johnson/Desc/First/Att/K05LawOne.lean) takes
thirteen facts on public data as premises (its record K5Public). Three of them (att, planOk, held)
are, in part or whole, given by no theorem over all public files and were asked by no text that
runs. This file holds what is left of them as tests with code, so that a verifier can ask them. The
tests can only make a verifier refuse more. No file is known at which one of them says no. No
Mathlib is below this file.

  `guardListN`: the tests, one to a line, each with its name. A name is a short mark and the words
    under which a verifier may refuse. The comment above a test says what it tests and which field
    of K5Public takes it.
  `k5ListN W l g`: the tests at link l and group g of the public record W.
  `k5GuardN W l g`: all of them say yes.
  `k5AsksN W`: the tests of every attention segment of W; a name begins with its link's number.

How it works. It takes the group's plan a := W.A[g] and the place of the segment's lookup, x :=
lookAt W l false, and tests these two. The tests are meant for a public record whose stored plans
are what the planner returns, but for one field that no test and no law on the segment reads
(PlanIs, Johnson/Desc/First/Att/GuardPublic.lean), and for the link l = 2 g + 1 of a proof that
covers attention. At another record or link the tests say nothing of the planner or of the place.

Which fields. Seven tests: att's part masksIn; planOk's five parts; held. All else of the thirteen
is given by theorems there, so it is no test: att's shape and planes, fs, mats and planes
(Johnson/Desc/First/Att/GuardPlan.lean); att's four and fits (GuardNLaw.lean); plan and own
(GuardPublic.lean). The fields plain, entries and kinds speak of a description's data and are not
tested here. The fields claims and pair follow from the block's own test on the plan.

Twins. usualN, callsFitN, numsN, posN, unitsN, heldN and what they call repeat tests whose own texts
lie in files over Mathlib (the five parts of planOkAll; k5Held).
Johnson/Desc/First/Att/GuardNLaw.lean shows that a twin's yes gives its test's yes, and what the
tests give the law.

Limits. k5AsksN walks the attention links by a formula of its own (attLinksN). Where the public
record has no attention segment the list is empty: it asks nothing and refuses nothing. That the
walk meets the description's own blocks is a further test, in a file of its own
(Johnson/Desc/First/Att/GuardWalkN.lean): the lists of this file do not hold it. The test held may
follow, by a theorem, from bounds that the planner's ranges give; so may masksIn and three parts of
planOk (the shape's numbers, the six positive numbers, the units) from the planner's text; these
theorems are not written. A yes of these tests is no proof of soundness: the law has further
premises, on the statement in front of the segment's rounds and on the relation behind them.
Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K5AttentionKind
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Look.LookAt
import OnBytes.Model.AttentionPlan
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-! ## The field held

At each of the segment's rounds the proved count of bad challenges is a share of at most 2^-k of the
round's challenges, the bits of work counted. -/

/-- The number of values of a list of draws. -/
def nValsN : List Fmt.Draw → Nat
  | [] => 1
  | .elem :: ds => Fmt.Fld.two.p ^ 3 * nValsN ds
  | .elemNZ :: ds => (Fmt.Fld.two.p ^ 3 - 1) * nValsN ds
  | .pos k :: ds => 2 ^ k * nValsN ds
  | .trits n :: ds => 4 ^ n * nValsN ds
  | .sealed :: ds => (2 ^ 64) ^ 4 * nValsN ds

/-- The proved count at a round, from the round's entry. z: the count at the draw of the point. -/
def errOfN (z : Nat) (e : Fmt.Entry) : Nat :=
  if e.name = "PSC epsilon" then 1
  else if e.name = "PSC round" ∨ e.name = "PSC Y" then e.msg / 24
  else if e.name = "BAT-sigma" then e.rows - 1
  else if e.name = "ZERO" then z
  else 0

/-- The count at the draw of the point. -/
def zOfN (x : Params.AttentionRounds) : Nat :=
  (2 * x.lgk + 2 * x.lt + 4) * (Fmt.Fld.two.p ^ 3) ^ (2 * x.lgk + 2 * x.lt + 4 - 1)

/-- Four conjuncts at one round: two bounds (logN is at most 64; D is not 0) and two comparisons.
The count e is at most the share n / D of the round's typed
values. That share, carried over the hash's blocks, is at most 2^work / 2^k. -/
def rowOkN (k e : Nat) (en : Fmt.Entry) (kd : Fmt.Kind) (n D : Nat) : Bool :=
  Decidable.decide (en.logN ≤ 64) && Decidable.decide (0 < D) &&
    Decidable.decide (e * D ≤ n * nValsN (Fmt.dsOf en kd)) &&
    Decidable.decide ((2 ^ 128 + 1) ^ Fmt.blocksFor (Fmt.wordsAtMost en kd) * n * 2 ^ k ≤
      (2 ^ 128) ^ Fmt.blocksFor (Fmt.wordsAtMost en kd) * D * 2 ^ en.work)

/-- The share that is tried. -/
def pickN (e : Nat) (en : Fmt.Entry) (kd : Fmt.Kind) : Nat × Nat :=
  if en.name = "ZERO" then (en.drawE, Fmt.Fld.two.p ^ 3) else (e, nValsN (Fmt.dsOf en kd))

/-- The test at all rounds of the segment, at the block's numbers p. A round whose name is none of
errOfN's five has the count 0, and a name that the format does not know has the kind "nothing": so
the test leans on the names that rounds p itself lays. -/
def heldN (k : Nat) (p : Par) : Bool :=
  ((rounds p).map fun r => (r.entry, (Fmt.kindOf r.entry.name).getD .nothing)).all fun r =>
    rowOkN k (errOfN (zOfN p.own) r.1) r.1 r.2 (pickN (errOfN (zOfN p.own) r.1) r.1 r.2).1
      (pickN (errOfN (zOfN p.own) r.1) r.1 r.2).2

/-! ## The segment's sizes and the lookup's numbers, as the description of the segment reads them -/

/-- The segment's sizes: 2^lg key/value heads; 2^lP rows of tiles below the diagonal; 2^lB positions
in a block; 2^ln channels of a head; na query heads for each key/value head; nl layers. -/
structure DimN where
  lg : Nat
  lP : Nat
  lB : Nat
  ln : Nat
  na : Nat
  nl : Nat

/-- The sizes, from the shape. -/
def dimN (S : Attention.Shape) : DimN := ⟨S.cf.lgk, S.lnT - 1, S.cf.lB, S.cf.ldh, S.HA, S.Lam⟩

namespace DimN
variable (D : DimN)
def nG : Nat := 2 ^ D.lg
def hP : Nat := 2 ^ D.lP
def nBlk : Nat := 2 * D.hP
def B : Nat := 2 ^ D.lB
def T : Nat := D.nBlk * D.B
def ch : Nat := 2 ^ D.ln
/-- pairs of a layer and a query head's number -/
def nb : Nat := D.nl * D.na
/-- bits of a position -/
def lT : Nat := D.lP + 1 + D.lB
/-- bits of a piece's inner index, family by family -/
def lM : Nat := D.lg + D.lP + (D.lP + 1) + D.lB + D.lB
def lD : Nat := D.lg + (D.lP + 1) + D.lB + D.lB
def lW : Nat := 1 + D.lg + D.lT + D.ln
def lX : Nat := D.lg + D.lT
def l4 : Nat := D.lg + D.lT + D.ln
/-- how many indices of call c are in pieces -/
def used : Nat → Nat
  | 0 => D.nb * 2 ^ D.lM + D.nb * 2 ^ D.lD
  | 1 => D.nb * 2 ^ D.lM + D.nb * 2 ^ D.lD
  | 2 => D.nb * 2 ^ D.lW + D.nb * 2 ^ D.lX
  | _ => D.nb * 2 ^ D.l4
end DimN

/-- Call c of the lookup has 2^(aN fs c) keys. -/
def aN (fs : Forest.Shape) (c : Nat) : Nat := ((fs.calls[c]?).map fun k => k.n).getD 0
/-- The number of trees of call c. -/
def treesN (fs : Forest.Shape) (c : Nat) : Nat := 2 ^ (aN fs c - fs.dT)
/-- The first tree of call c. -/
def firstN (fs : Forest.Shape) : Nat → Nat
  | 0 => 0
  | 1 => treesN fs 0
  | 2 => treesN fs 0 + treesN fs 1
  | _ => treesN fs 0 + treesN fs 1 + treesN fs 2

/-! ## The field planOk, in five parts -/

/-- The configuration's lines are the usual four calls with their segments, and all layers of the
group have one shift. Where the list of shifts is empty every shift reads as 0 and this part says
yes; callsFitN then refuses, for expOkN takes no shift below 4. -/
def usualN (cf : Attention.Cfg) : Bool :=
  Decidable.decide ((cf.lines.map fun l => (l.kind, l.segs)) =
    [(.kr, [.rm, .rd]), (.kfd, [.fm, .fd]), (.r16, [.wl, .ix]), (.wh, [.wh])]) &&
  (List.range (2 ^ cf.ll)).all fun l => Decidable.decide (cf.sh.getD l 0 = cf.sh.getD 0 0)

/-- The valid shifts and numbers of live rows of the table of exponentials. -/
def expOkN (sh u0 : Nat) : Bool :=
  let nd : Nat := (4 * (128 * 2047 ^ 2 : Int) / ((2 : Int) ^ 16 - 2 ^ sh)).toNat + 1
  Decidable.decide (4 ≤ sh) && Decidable.decide (sh ≤ 12) && Decidable.decide (0 < u0) &&
    Decidable.decide (u0 + nd ≤ 2 ^ 16) && Decidable.decide (2 ^ 16 ≤ u0 + 2 * nd) &&
    Decidable.decide (((2 : Int) ^ sh * (u0 : Int)) + 2 ^ 16 ≤ 2 ^ 24)

/-- The lookup's numbers fit the segment's sizes. -/
def callsFitN (S : Attention.Shape) (fs : Forest.Shape) : Bool :=
  -- the pieces of each call fit into it
  (List.range 4).all (fun c => Decidable.decide ((dimN S).used c ≤ 2 ^ aN fs c)) &&
  -- a call consists of whole trees
  (List.range 4).all (fun c => Decidable.decide (fs.dT ≤ aN fs c)) &&
  -- the trees fit into the tree numbers
  Decidable.decide (treesN fs 0 + treesN fs 1 + treesN fs 2 + treesN fs 3 ≤ 2 ^ fs.rK) &&
  -- each call starts at a multiple of its number of trees
  (List.range 4).all (fun c => Decidable.decide (firstN fs c % treesN fs c = 0)) &&
  Decidable.decide (10 ≤ fs.dT) && expOkN (S.cf.sh.getD 0 0) S.u0 &&
  -- a piece lies in one tree
  Decidable.decide ((dimN S).lM ≤ fs.dT) && Decidable.decide ((dimN S).lD ≤ fs.dT) &&
  Decidable.decide ((dimN S).lW ≤ fs.dT) && Decidable.decide ((dimN S).lX ≤ fs.dT) &&
  Decidable.decide ((dimN S).l4 ≤ fs.dT) &&
  Decidable.decide (aN fs 0 = aN fs 1) &&
  -- the record's own first trees and numbers of trees are these
  (List.range 4).all (fun c => Decidable.decide (firstN fs c = fs.first.getD c 0)) &&
  (List.range 4).all (fun c => Decidable.decide (fs.iota.getD c 0 = aN fs c - fs.dT) &&
    Decidable.decide (aN fs c - fs.dT ≤ fs.rK))

/-- The shape's numbers are those of its sizes. -/
def numsN (S : Attention.Shape) : Bool :=
  S.B == (dimN S).B && S.nT == (dimN S).nBlk && S.hP == (dimN S).hP && S.G == (dimN S).nG &&
    S.T == (dimN S).T && S.dh == (dimN S).ch && S.cf.lt == (dimN S).lT && S.atQ.nl == 2 &&
    S.atK.nl == 2 && S.atV.nl == 2 && S.atO.nl == 2 && S.Smax == 128 * 2047 ^ 2

/-- Six numbers of the place are positive. -/
def posN (g : Geo) : Bool :=
  Decidable.decide (0 < g.NAs) && Decidable.decide (0 < g.kAs / g.NAs) &&
    Decidable.decide (0 < g.fillH) && Decidable.decide (0 < g.fillO * g.T / 2 ^ g.la) &&
    Decidable.decide (0 < g.fillQ * g.T / 2 ^ g.la) && Decidable.decide (0 < g.kbA)

/-- A unit's pieces, by layer, then by head. -/
def pcsSortedN (u : UnitG) : List Pc :=
  u.pcs.mergeSort fun x y =>
    Decidable.decide (x.lam < y.lam) || (x.lam == y.lam && Decidable.decide (x.a ≤ y.a))

/-- One unit of the place is one family of pieces of the description. q: the call; fc: the family's
call; fl: the bits of a piece; nu: the number of the family's first piece. -/
def unitN (S : Attention.Shape) (fs : Forest.Shape) (fc fl nu q : Nat) (u : UnitG) : Bool :=
  u.call == q && aN fs q == aN fs fc && u.bits == fl && Decidable.decide (fl ≤ aN fs q) &&
    ((pcsSortedN u).map fun pc => (u.n - pc.b, pc.off >>> pc.b)) ==
      (List.range (dimN S).nb).map fun b => (aN fs q - fl, nu + b)

/-- The place's seven units are the description's seven families of pieces. -/
def unitsN (S : Attention.Shape) (fs : Forest.Shape) : Bool :=
  let D := dimN S
  match ((geoOf S).units .kr [.rm, .rd]).map (fun u => (geoOf S).unitAt u.1 u.2.1 u.2.2),
      (geoOf S).scores, (geoOf S).single .wl, (geoOf S).single .ix, (geoOf S).single .wh with
  | [r1, r2], [u1, u2], some wl, some ix, some wh =>
    u1.below && !u2.below &&
      unitN S fs 0 D.lM 0 0 r1 && unitN S fs 0 D.lD (D.nb * 2 ^ (D.lM - D.lD)) 0 r2 &&
      unitN S fs 1 D.lM 0 1 u1 && unitN S fs 1 D.lD (D.nb * 2 ^ (D.lM - D.lD)) 1 u2 &&
      unitN S fs 2 D.lW 0 2 wl && unitN S fs 2 D.lX (D.nb * 2 ^ (D.lW - D.lX)) 2 ix &&
      unitN S fs 3 D.l4 0 3 wh
  | _, _, _, _, _ => false

/-! ## The tests -/

/-- The block's numbers at link l, as the segment's block has them. No test reads the field
before. -/
def parN (W : Verify.Public) (l : Nat) (a : Attention.Plan) : Par :=
  { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request
    own := a.own, before := [] }

/-- The tests, one to a line. a: the group's plan; x: the place of the lookup; p: the block's
numbers. -/
def guardListN (a : Attention.Plan)
    (x : VerifiableInference.Desc.First.Look.Place) (p : Par) : List (String × Bool) :=
  [
    -- The lookup's own scalars lie among the link's slots.
    -- Taken by K05_law_one (K5Public.att, masksIn).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-att-masks: the lookup's scalars do not fit into the link's slots",
      Decidable.decide (x.F.next + FoNums.nMasks x.fs ≤ x.ns)),
    -- The configuration has the usual four calls and one shift.
    -- Taken by K05_law_one (K5Public.planOk, part 1 of 5).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-plan-usual: the attention calls are not the usual four with one shift",
      usualN a.S.cf),
    -- The lookup's numbers fit the segment's sizes.
    -- Taken by K05_law_one (K5Public.planOk, part 2 of 5).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-plan-calls: the lookup's numbers do not fit the segment's sizes",
      callsFitN a.S a.fs),
    -- The shape's numbers are those of its sizes.
    -- Taken by K05_law_one (K5Public.planOk, part 3 of 5).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-plan-nums: the shape's numbers are not those of its sizes",
      numsN a.S),
    -- Six numbers of the place are positive.
    -- Taken by K05_law_one (K5Public.planOk, part 4 of 5).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-plan-pos: one of six sizes of the segment's tables is 0",
      posN (geoOf a.S)),
    -- The place's seven units are the description's seven families of pieces.
    -- Taken by K05_law_one (K5Public.planOk, part 5 of 5).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-plan-units: the segment's pieces do not lie in the lookup's calls as described",
      unitsN a.S a.fs),
    -- At each round of the segment the proved count is a share of at most 2^-128, the bits of
    -- work counted.
    -- Taken by K05_law_one (K5Public.held).
    -- No file is known at which it says no; it is there for the proof.
    ("k5-held: at a round of the segment the count of bad challenges is above its share",
      heldN 128 p) ]

/-- The tests at link l, group g of the public record W. One failed test where W has no plan of the
group or no place of the link. -/
def k5ListN (W : Verify.Public) (l g : Nat) : List (String × Bool) :=
  match W.A[g]?, VerifiableInference.Desc.First.Look.lookAt W l false with
  | some a, some x => guardListN a x (parN W l a)
  | _, _ => [("k5-plan-or-place: no plan of the group or no place of the link", false)]

/-- All tests at link l, group g say yes. -/
def k5GuardN (W : Verify.Public) (l g : Nat) : Bool := (k5ListN W l g).all (·.2)

/-- The attention segments of the first chain: (link, group). -/
def attLinksN (W : Verify.Public) : List (Nat × Nat) :=
  if W.p4 then (List.range W.NGr).map fun g => (2 * g + 1, g) else []

/-- The tests at every attention segment; a name begins with its link's number. -/
def k5AsksN (W : Verify.Public) : List (String × Bool) :=
  (attLinksN W).flatMap fun y => (k5ListN W y.1 y.2).map fun t => (s!"link {y.1}: {t.1}", t.2)

end VerifiableInference.Desc.First.Att.P
