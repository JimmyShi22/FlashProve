-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Text.lean: the IOPP for linear constraints on the encoded index: the rounds that a
batch of instances shares.

This file holds definitions only; no theorem is stated.

The encoded index Pi_M has 2^vHi rows under one code; the root of a tree over its columns is public,
and so is its record: for each row an answer y[r] to a sample out of the domain, under a seed
(z, beta). It holds the index M: entry (y, j + 2^vLo r) of M lies at place j + 2^vLo y of row r.
Each instance has claimed a value of a tensor form on M. Here, once for all instances, at a shared
point psi_sh = (psi_lo, gamma) that is drawn after these claims, M is brought down to one vector
omega_col = M eq(psi_sh, .), one entry for each row of M. The verifier tests no equation in these
rounds: it hands linear constraints on committed messages to two proximity tests.

Letters. o_u: the message that encodes (u, r_u), the fold of Pi_M's rows at gamma. o_omega: encodes
omega_col. o_sp: one mask row; kappa is an entry of it. The two groups: G_u = {o_u, o_sp} and
G_omega = {o_omega, o_sp}. Q: the locations. z_fd: a point on the rows of M. mu: the masked value
that the prover says at the split. w_r = eq(r, gamma).

Four headings: ROUNDS (as data), READS (as data), DECIDES, SENDS. SENDS is not written in this file.
WHAT A ROUND HOLDS AND DRAWS IS SAID ONCE, UNDER ROUNDS, AND ASKED ONCE, BY THE FORMAT's GENERAL
FUNCTION (Block.step: roundsFit holds a view's rounds against them; the columns that are owed by
READS are matched there too): the functions under DECIDES do not ask it again, and are no decision
without it. NOT ON THIS PAGE: THE SENDING OF AN ENCODING WITH ITS SAMPLE: another kind's (K1): its
own block stands at the two places; this page says what goes out (withU, withOmega) and what it
notes of the new messages' numbers behind each sending (behindU, behindOmega). Called by name: the
effects on the statement (newGroupP, joinP, addRowP, addRowsP, takeMaskP); constraints, tensors and
codes as such (Row, Tensor, generatorAt). THE PLACES' NAMED CLAUSES CALL THE DESCRIPTION's OWN
TEXTS: on the codes and the public shape: lengthsFit, linFits (Johnson/Desc/Own/Lin.lean: the
program's tests taken over token for token, but that "n ≤ the room of a message" is asked by roomOf,
Johnson/Desc/Own/Room.lean, whose three hidden cases are a named test; what each checks:
LinMeans.lean, RoomMeans.lean; that each says what the program's says: LinAgree.lean); on the key:
keyFits (Johnson/Desc/Own/KeyTests.lean); "a factor is not 0": allZero (Johnson/Desc/Own/Rows.lean):
it compares an element's three words with 0, and speaks of the field's zero only where every word is
below the prime (okKey asks that of the key); o_omega has a tree to itself: aloneIn
(Johnson/Desc/Own/Alone.lean; AloneMeans.lean): the tree at the number which o_omega's place names
has o_omega as its one part; the hand-written program asks only that the tree has one part.
WHAT THESE OWN TEXTS CALL OF THE PROGRAM's AND THE FORMAT's FILES STANDS IN THEIR HEADS.
CALLED HERE OF THE PROGRAM, AND ABLE TO RETURN NOTHING, AT WHICH A PLACE REFUSES: tensorBelow (in
recGamma, locX, fold) and linWithU (in withU).

THE KEY IS THE INSTANCE's: it is in the carried record from the start, and is no parameter.
A CONDITION ON THE KEY, OWED BY WHOEVER CALLS THIS PAGE AND TESTED NOWHERE ON IT: the record's seeds
are those that follow from the encoded index's name (its root, the public files' digest and its six
sizes), and the record's answers and the root are those of the chain's statement. With seeds that a
prover could choose (rec_gamma) binds nothing.

What is not claimed. That these constraints are the right ones. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Ground.Calls
import Johnson.Desc.Own.Lin
import Johnson.Desc.Own.Alone
import Johnson.Desc.Own.Rows
import Johnson.Desc.Own.KeyTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Ground (newGroupP joinP addRowP addRowsP takeMaskP Clauses ok)

/-- **The small record handed on.** -/
structure Lin where
  /-- psi_sh = (psi_lo, gamma): vLo + vHi coordinates -/
  psiSh : List E := []
  /-- the groups G_u and G_omega (one group if o_u and o_omega have one code) -/
  gU : Nat := noId
  gOmega : Nat := noId
  /-- o_u, and how (u, r_u) is laid out in it -/
  oU : FoldedRow := {}
  /-- the first mask of the test on G_u, if it went out with o_u -/
  firstMask : Option Nat := none
  oOmega : Nat := noId
  oSp : Nat := noId
  /-- z_fd: one coordinate for each bit of a row of M -/
  zFd : List E := []
  /-- the encoded index's key (the record's seeds and answers; which item of the chain's statement
  holds the root): THE INSTANCE's: laid in front of the first round, turned by no round -/
  key : TableKey := {}

/-- The carried state: the statement and the book of trees (coarse: a common page's), and Lin. -/
abbrev St : Type := DState Lin

/-- gamma, and the weights w_r = eq(r, gamma) of Pi_M's rows. -/
def gamma (S : LinShape) (l : Lin) : List E := l.psiSh.drop S.kLo

@[inherit_doc gamma]
def weights (S : LinShape) (l : Lin) : Array E := eqTable (gamma S l)

/-! ## ROUNDS: who sends what; what is drawn -/

/-- What the prover sends in a round of this kind's own. -/
inductive Says where
  | nothing
  | scalars (n : Nat)

/-- A round: its name in the plan; what the prover sends; then what the verifier draws: elements of
E, how many of these from the elements other than 0, and locations below 2 ^ logN. -/
structure Round where
  name : String
  prover : Says := .nothing
  elems : Nat := 0
  nonzero : Nat := 0
  locations : Nat := 0
  logN : Nat := 0

/-- What goes out with o_u (the first mask of the test on G_u), and with o_omega (o_sp). -/
def withU (S : LinShape) : Option (Array OracleNotice) :=
  (linWithU S).map (#[(⟨S.fold.u, S.fold.leafClass⟩ : OracleNotice)] ++ ·)

@[inherit_doc withU]
def withOmega (S : LinShape) : Array OracleNotice := linMessageOmega S

/-- **The kind's own rounds in front of the two tests**, in order. Between the first and the second
stand the two rounds of the sending of o_u, between the second and the third those of the sending
of o_omega: a sending is another kind's (K1), with its own ROUNDS. -/
def rounds (S : LinShape) : List Round :=
  [{ name := "LIN point", elems := S.kCol },
   { name := "LOC", locations := S.fold.columns, logN := S.fold.index.code.logN },
   { name := "LIN zeta", elems := S.kRow }] ++
    if S.sharedSplitNeeded then [{ name := "SPLIT", prover := .scalars 1 }] else []

/-! ## READS: which oracle at which locations -/

/-- Pi_M is read at Q, the locations drawn in "LOC": all of them, from the first on; each location
once, in increasing order (the format's general function makes that list). No other oracle is read
in these rounds. item: the number of the item of the chain's statement that holds Pi_M's root. -/
def readsAtLoc (S : FoldeqShape) (item : Nat) : Fmt.Stored :=
  ⟨S.index.tree, S.index.saltBytes, item, 0, S.columns⟩

/-! ## DECIDES: the constraints, then the rounds' functions -/

/-- (rec_gamma), for answer i of the record: the rows' answers fold as the rows do. On o_u:
eq(z, .) in front of the pads, beta (1, X, X^2) on the pads of answer i and 0 on the other pads give
the sum of w_r y[r, i]. -/
def recGamma (s : IndexShape) (seed : SampleSeed) (i : Nat) (w y : Array E) (u : FoldedRow) :
    Option Row := do
  let e := Tensor.eq seed.z
  let pads := (List.range s.answers).flatMap fun a => (List.range 3).map fun t => (a, t)
  let row := pads.foldl (fun (r : Row) (a, t) =>
      r.addUnit u.oracle .main (u.lay.index (s.padPlace a t))
        (subE (if a == i then mulE seed.beta (thetaE t) else zeroE) (e.entry (s.padPlace a t))))
    (u.addAll {} (← tensorBelow e 0 s.cubeBits s.code.ell))
  let sum ← (List.range s.rows).foldlM
    (fun t r => do pure (maddE t (← w[r]?) (← y[r * s.answers + i]?))) zeroE
  pure { row with target := sum }

/-- (loc_x): what o_u holds, encoded under Pi_M's code (row x of its generator matrix, on the
message and on the randomness), is the fold of Pi_M's column at x: the sum of w_r Pi_M(r, x). -/
def locX (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow) :
    Option Row := do
  let c := S.index.code
  let g := generatorAt c x
  let message ←
    tensorBelow (Tensor.product (g.f.take c.logEll) (ofF g.messageScale)) 0 c.logEll c.ell
  let tail ← if c.r == 0 then pure []
    else tensorBelow (Tensor.product (g.f.take c.logR) (ofF g.tailScale)) 0 c.logR c.r
  let placed := tail.map (·.insertChoice c.logR (u.lay.bits - c.logR) (S.tailFirst / 2 ^ c.logR))
  let sum ← (List.range w.size).foldlM
    (fun s r => do pure (maddS s (← column[r]?) (← w[r]?))) zeroE
  pure { u.addAll (u.addAll {} message) placed with kind := .generator, target := sum }

/-- The tests in front of (fold), as named clauses. -/
def foldL (S : LinShape) (l : Lin) : Clauses :=
  [("the point drawn at LIN point has the planned number of coordinates",
     l.psiSh.length == S.kCol),
   ("the point drawn at LIN zeta has the planned number of coordinates",
     l.zFd.length == S.kRow)]

/-- (fold): omega_col at z_fd is what u gives at (psi_lo, z_fd), over the real rows of M alone:
< eq(z_fd, .), omega_col > - < eq((psi_lo, z_fd), .), u > = 0. -/
def fold (S : LinShape) (l : Lin) (layOmega : VectorLay) : Option Row := do
  guard (ok (foldL S l))
  let onOmega ← tensorBelow (Tensor.eq l.zFd) 0 S.kRow S.matrixRows
  let onU ← tensorBelow (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)) S.kLo S.kRow
    S.matrixRows
  pure (l.oU.addAll (addLaid {} l.oOmega layOmega onOmega) onU)

/-- The part of a constraint on these messages (mine = true), or on the others. -/
def part (row : Row) (members : Array Nat) (mine : Bool) : Row :=
  { terms := row.terms.filter (members.contains ·.oracle == mine)
    units := row.units.filter (members.contains ·.oracle == mine)
    runs := row.runs.filter (members.contains ·.oracle == mine)
    forms := row.forms.filter (members.contains ·.oracle == mine) }

/-- The elements that a round draws. -/
def drawn (r : Fmt.RoundView) : List E := r.drawn.elems.map E.ofTriple

/-! Each place's own tests on values are a list of named clauses (…L), so that a refusal bears a
name; the place's function goes on only if all hold. -/

/-- The tests at "LIN point". -/
def linPointL (p : Par) (d : St) : Clauses :=
  [("every code's message length is a power of two",
     VerifiableInference.Desc.Own.lengthsFit d.st.codes),
   ("the public sizes of the linear claim meet their conditions",
     VerifiableInference.Desc.Own.linFits d.st.codes p.S)]

/-- The tests in front of (rec_gamma). -/
def laysRecL (p : Par) (l : Lin) : Clauses :=
  [("the key's record and seeds have the planned sizes",
     VerifiableInference.Desc.Own.keyFits l.key p.S.fold.index),
   ("no seed of the record has the factor 0",
     l.key.seeds.all (!VerifiableInference.Desc.Own.allZero ·.beta)),
   ("the point that folds the table's rows has the planned number of coordinates",
     (gamma p.S l).length == p.S.fold.index.v)]

/-- The test in front of the joinings. -/
def joinsL (d : St) : Clauses :=
  [("the first message of send o_omega has a tree to itself",
     VerifiableInference.Desc.Own.aloneIn d.book d.loc.oOmega)]

/-- The tests at "SPLIT", behind "just one scalar is sent". -/
def splitL (d : St) (row : Row) : Clauses :=
  let l := d.loc
  let inOmega := ((d.st.groups[l.gOmega]?).map (·.members)).getD #[]
  let inU := ((d.st.groups[l.gU]?).map (·.members)).getD #[]
  [("the two groups of messages are distinct", l.gOmega != l.gU),
   ("the mask message of the split has mask rows alone",
     ((d.st.oracles[l.oSp]?).map (·.shape.mainRows == 0)).getD false),
   ("the mask message of the split is in the group of send o_omega", inOmega.contains l.oSp),
   ("the mask message of the split is in the group of send o_u", inU.contains l.oSp),
   ("each message that the split constraint reads is in just one of the two groups",
     row.oracles.all fun o => inOmega.contains o != inU.contains o)]

/-- "LIN point": the verifier sends psi_sh. The two groups are opened. -/
def linPoint (p : Par) (d : St) : List Fmt.RoundView → Option St
  | [r] => do
    guard (ok (linPointL p d))
    let (gU, d) ← newGroupP d p.S.fold.u.code p.S.sharedMaskCode
    let (gO, d) ← if p.S.sharedSplitNeeded then newGroupP d p.S.omega.code p.S.sharedMaskCode
      else some (gU, d)
    some { d with loc := { d.loc with psiSh := drawn r, gU := gU, gOmega := gO } }
  | _ => none

/-- o_u has gone out by a sending (K1). ids: the new messages' numbers, as the sending hands them
on, in the order of sending. What this kind notes: o_u with its layout; the first mask. -/
def behindU (p : Par) (d : St) (ids : Array Nat) : Option St := do
  let mask ← if p.S.masksAhead then (ids[1]?).map some else some none
  let u := ⟨← ids[0]?, vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh⟩
  some { d with loc := { d.loc with oU := u, firstMask := mask } }

/-- No round: o_u joins G_u; (rec_gamma) goes there, once for each answer of the record. -/
def laysRec (p : Par) (d : St) (_ : List Fmt.RoundView) : Option St := do
  let s := p.S.fold.index
  let l := d.loc
  guard (ok (laysRecL p l))
  let d ← joinP d l.gU l.oU.oracle false
  addRowsP d l.gU (← l.key.seeds.zipIdx.mapM fun x =>
    recGamma s x.1 x.2 (weights p.S l) l.key.record l.oU)

/-- "LOC": the verifier sends the locations Q; the prover sends nothing. Pi_M's columns at Q come as
they are handed: one group, each column with its location. One (loc_x) for each location DRAWN goes
to G_u. -/
def loc (p : Par) (d : St) : List Fmt.RoundView → List (List (Nat × List UInt64)) → Option St
  | [r], [cols] => do
    let S := p.S.fold
    let l := d.loc
    addRowsP d l.gU (← (r.drawn.poss.map (· % 2 ^ S.index.code.logN)).mapM fun x => do
      locX S x (weights p.S l) ((← cols.lookup x).toArray) l.oU)
  | _, _ => none

/-- o_omega and o_sp have gone out in one prover's message by a sending (K1). What this kind notes:
their numbers. -/
def behindOmega (p : Par) (d : St) (ids : Array Nat) : Option St := do
  let sp ← if p.S.sharedSplitNeeded then ids[1]? else some noId
  some { d with loc := { d.loc with oOmega := ← ids[0]?, oSp := sp } }

/-- No round: o_omega has a tree to itself (each instance's own test opens it again) and joins
G_omega; o_sp joins both groups. -/
def joins (p : Par) (d : St) (_ : List Fmt.RoundView) : Option St := do
  let l := d.loc
  guard (ok (joinsL d))
  let d ← joinP d l.gOmega l.oOmega false
  if p.S.sharedSplitNeeded then joinP (← joinP d l.gOmega l.oSp false) l.gU l.oSp false else some d

/-- "LIN zeta": the verifier sends z_fd. -/
def linZeta (d : St) : List Fmt.RoundView → Option St
  | [r] => some { d with loc := { d.loc with zFd := drawn r } }
  | _ => none

/-- "SPLIT": (fold) reads messages of two groups, and a test reads one. The prover sends mu; the
verifier says nothing. With kappa, the next free entry of o_sp, (fold) becomes
  (fold_omega), on G_omega: (its part) + kappa = mu;   (fold_u), on G_u: (its part) - kappa = - mu.
With one group there is no round, and (fold) goes there whole. -/
def split (p : Par) (d : St) (rs : List Fmt.RoundView) : Option St := do
  let l := d.loc
  let row ← fold p.S l (linLayOmega d.st.codes p.S)
  match p.S.sharedSplitNeeded, rs with
  | false, [] => addRowP d l.gU row
  | true, [r] =>
    let mu ← match r.vals with
      | [.e x] => some (E.ofTriple x)
      | _ => none
    let inOmega := (← d.st.groups[l.gOmega]?).members
    guard (ok (splitL d row))
    let (kappa, d) ← takeMaskP d l.oSp
    let d ← addRowP d l.gOmega
      { (part row inOmega true).addUnit l.oSp .mask kappa oneE with target := mu }
    addRowP d l.gU { (part row inOmega false).addUnit l.oSp .mask kappa (negE oneE) with
      target := subE row.target mu }
  | _, _ => none

/-! ## SENDS: what an honest prover sends. SENDS is not written in this file. -/

end Desc.K14
