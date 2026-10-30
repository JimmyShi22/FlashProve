-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15.lean: THE ENTRY's TIE: TWO TABLES UNDER ONE DRAWN gamma. The kind K15.
Definitions with code alone; no theorem.

An entry file holds a further stored copy Pi' of the encoded index Pi, under fresh coins. The claim:
the copy's rows agree with
the first table's in every entry before the cut, where the pads of a row's message begin. Both
tables have one shape; the root
and the record of each are public (the chain's statement's items 0 and 1). The verifier tests no
equation in these rounds: it
hands linear constraints on one committed message to one proximity test.

Letters. gamma: ONE fold point for both tables; w_r = eq(r, gamma). o_0, o_1: the two tenants of the
one message that is sent:
the folds (u_0, r_0), (u_1, r_1) of the two tables' rows at gamma. G: the one group {o_0, o_1}. Q_0,
Q_1: the locations: the
first draws are Q_0, the others Q_1. phi: a point on the entries of a row's message.

Four headings, as on the page of K14 (Johnson/Desc/K14/Text.lean): ROUNDS (as
data), READS (as data), DECIDES, SENDS (not
written here). WHAT A ROUND HOLDS AND DRAWS IS SAID ONCE, UNDER ROUNDS, AND ASKED ONCE, BY THE
FORMAT's GENERAL FUNCTION
(Block.step): the functions under DECIDES do not ask it again, and are no decision without it.
CALLED BY NAME, AND NOT ON THIS PAGE: K14's two constraints, AS THEY LIE, general in the shape:
(rec_gamma) `Desc.K14.recGamma`
and (loc_x) `Desc.K14.locX`: each at either table · the effects on the statement (newGroupP, joinP,
addRowP, addRowsP) ·
constraints, tensors and codes as such. THE SENDING OF o_0 AND o_1 IS ANOTHER KIND's BLOCK (K1's
own: Johnson/Desc/K1/Own.lean), laid at the
link's record in Johnson/Desc/Link/LinkDesc.lean (sendK1); of it this page holds only what K15 notes
behind it (`behind`). THE CONDITIONS ON THE
PUBLIC SHAPE (`linkOk`, `Codes.lengthsOk`) ARE NOT ASKED ON THIS PAGE: the link's front asks them,
on the plan alone (LinkDesc.lean: frontBlock).
THIS PAGE's OWN: the steps' few lines at the entry's own record, and (eq_phi), the equality row.

THE TWO KEYS ARE THE INSTANCE's: they ride in the carried record from the start. THE CONDITION ON A
KEY that K14's page names
(the record's seeds follow from the table's name; record and root are the chain's statement's) IS
OWED HERE TWICE, BY WHOEVER
CALLS THIS PAGE, AND TESTED NOWHERE ON IT.
What is not claimed. That these constraints are the right ones. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K14.Text
import Johnson.Desc.Own.KeyTests
import OnBytes.Iop.Link

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params Desc.Plain
open Desc.K14 (Round Says recGamma locX drawn)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowP addRowsP Clauses ok)

/-- **The small record handed on.** -/
structure Tie where
  /-- gamma: one coordinate for each bit of a table's row number -/
  gamma : List E := []
  /-- the group G -/
  g : Nat := noId
  /-- o_0 and o_1, and how each fold is laid out -/
  o0 : FoldedRow := {}
  o1 : FoldedRow := {}
  /-- the first mask of the test on G, if it went out with the folds -/
  firstMask : Option Nat := none
  /-- the two tables' keys: THE INSTANCE's: laid in front of the first round, turned by no round -/
  key0 : TableKey := {}
  key1 : TableKey := {}

/-- The carried state. -/
abbrev St : Type := DState Tie

/-- The place's public parameters, as far as this page reads them. -/
structure Par15 where
  samples : Nat
  S : LinkShape

def Par15.gp (p : Par15) : GPar := { samples := p.samples, firstTree := 0 }

/-- The weights w_r = eq(r, gamma) of a table's rows. -/
def weights (l : Tie) : Array E := eqTable l.gamma

/-! ## ROUNDS: who sends what; what is drawn -/

/-- **The kind's own rounds in front of the test**, in order. Between the first and the second stand
the two rounds of the sending of o_0 and o_1: a sending is another kind's (K1), with its own
ROUNDS (Johnson/Desc/K1/Send.lean). In none of the three does the prover send anything. -/
def rounds (p : Par15) : List Round :=
  [{ name := "LINK point", elems := p.S.table.v },
   { name := "LINK", locations := p.S.columnsFirst + p.S.columnsFurther, logN := p.S.table.code.logN
       },
   { name := "LINK phi", elems := p.S.entryBits }]

/-! ## READS: which oracle at which locations -/

/-- Pi is read at Q_0, the first draws of "LINK"; Pi' at Q_1, the others. No other oracle is read in
these rounds. -/
def readsAtLink (S : LinkShape) : List Fmt.Stored :=
  [⟨S.table.tree, S.table.saltBytes, 0, 0, S.columnsFirst⟩,
   ⟨S.table.tree, S.table.saltBytes, 1, S.columnsFirst, S.columnsFurther⟩]

/-! ## DECIDES: the one constraint of this page, then the rounds' functions -/

/-- (eq_phi): the two folds agree before the cut: < eq(phi, .) on the entries before the cut, u_0 -
u_1 > = 0. It stops at
the cut: pads and random tails of two tables are drawn independently. -/
def eqPhi (S : LinkShape) (phi : List E) (o0 o1 : FoldedRow) : Option Row := do
  guard (phi.length == S.entryBits)
  let plus ← tensorBelow (Tensor.eq phi oneE) 0 S.entryBits S.cut
  let minus ← tensorBelow (Tensor.eq phi (negE oneE)) 0 S.entryBits S.cut
  pure (o1.addAll (o0.addAll {} plus) minus)

/-- The tests in front of (rec_gamma), at one key. -/
def keyL (which : String) (p : Par15) (l : Tie) (key : TableKey) : Clauses :=
  [(which ++ ": the key fits the shape", VerifiableInference.Desc.Own.keyFits key p.S.table),
   -- isZeroE compares words with 0: it speaks of the field's zero only where every word is below
   -- the prime: the test on the instance (okKey: seedsOk) asks that of the keys' words in front of
   -- every block
   (which ++ ": no seed of the record has the factor 0", key.seeds.all (!isZeroE ·.beta)),
   ("gamma has a coordinate for each bit of a row's number", l.gamma.length == p.S.table.v)]

def laysRecL (p : Par15) (l : Tie) : Clauses :=
  keyL "the first table" p l l.key0 ++ keyL "the copy" p l l.key1

/-- "LINK point": the verifier sends gamma. The group is opened. THE PUBLIC SHAPE's CONDITIONS ARE
ASKED ON THE PLAN ALONE, at the plan's own codes, by the link's front's test on the plan
(Johnson/Desc/Link/LinkDesc.lean: frontBlock), and not here of the carried record's (a
test on the record is one more «a block lays, another trusts»). -/
def point (p : Par15) (d : St) : List Fmt.RoundView → Option St
  | [r] => do
    let (g, d) ← newGroupP d p.S.code p.S.maskCode
    some { d with loc := { d.loc with gamma := drawn r, g := g } }
  | _ => none

/-- What this kind notes behind the sending, of the new messages' numbers: o_0, o_1, how each fold
is laid out, and the first mask of the test on G if it went out with them. -/
def behind (p : Par15) (d : St) (ids : Array Nat) : Option St := do
  let mask ← if p.S.masksAhead then (ids[2]?).map some else some none
  let lay := vectorLay d.st.codes (p.S.side false p.samples).u p.S.rowsHigh
  some
      { d with loc :=
        { d.loc with o0 := ⟨← ids[0]?, lay⟩, o1 := ⟨← ids[1]?, lay⟩, firstMask := mask } }

/-- One table's share of the step without a round: its fold joins G; (rec_gamma) goes there, once
for each answer. -/
def laysOne (p : Par15) (d : St) (key : TableKey) (o : FoldedRow) : Option St := do
  let d ← joinP d d.loc.g o.oracle false
  addRowsP d d.loc.g (← key.seeds.zipIdx.mapM fun x =>
    recGamma p.S.table x.1 x.2 (weights d.loc) key.record o)

/-- No round: the first table's share, then the copy's. -/
def laysRec (p : Par15) (d : St) (_ : List Fmt.RoundView) : Option St := do
  guard (ok (laysRecL p d.loc))
  let d ← laysOne p d d.loc.key0 d.loc.o0
  laysOne p d d.loc.key1 d.loc.o1

/-- One table's share of "LINK": one (loc_x) for each of its locations DRAWN goes to G. -/
def locOne (p : Par15) (d : St) (further : Bool) (draws : List Nat)
    (cols : List (Nat × List UInt64))
    (o : FoldedRow) : Option St := do
  addRowsP d d.loc.g (← draws.mapM fun x => do
    locX (p.S.side further p.samples) x (weights d.loc) ((← cols.lookup x).toArray) o)

/-- "LINK": the verifier sends the locations; the prover sends nothing. The two tables' columns come
as they are handed: two
groups, each column with its location. -/
def link (p : Par15) (d : St) : List Fmt.RoundView → List (List (Nat × List UInt64)) → Option St
  | [r], [cols0, cols1] => do
    let q := r.drawn.poss.map (· % 2 ^ p.S.table.code.logN)
    let d ← locOne p d false (q.take p.S.columnsFirst) cols0 d.loc.o0
    locOne p d true ((q.drop p.S.columnsFirst).take p.S.columnsFurther) cols1 d.loc.o1
  | _, _ => none

/-- "LINK phi": the verifier sends phi; (eq_phi) goes to G. -/
def phi (p : Par15) (d : St) : List Fmt.RoundView → Option St
  | [r] => do addRowP d d.loc.g (← eqPhi p.S (drawn r) d.loc.o0 d.loc.o1)
  | _ => none

/-! ## SENDS: what an honest prover sends: written in Lean, Johnson/Prover/Link/ (lean/GAPS.md) -/

end Desc.K15
