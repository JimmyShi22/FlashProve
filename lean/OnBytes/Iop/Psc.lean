-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Psc.lean: the verifier's part in the zero-knowledge sumcheck.
C++ counterparts, all in blocks/iop/: psc.h (psc_verify, psc_rows), hp.h (Weight, hp_form),
summand.h (PointClaim, SumClaim, Summand), psc_rows.h (MapAt, psc_row_u, point_row), line.h, mask.h
(MaskSlot).

The claim. A public polynomial S in variables X_1 .. X_k and in the values of some maps of the
witness is summed over each variable in a stated way. That sum, plus a public linear form in mask
entries, is claimed to equal a public target. A mask entry is a random element that the prover
committed to beforehand.

The protocol. The prover sends the sum of a hiding polynomial, whose coefficients are mask entries.
The verifier draws eps. A sumcheck runs on the hiding polynomial plus eps times S. If the claim's
mask form has the value sigma, S gets one more term: sigma times the product of psi_t(X_t), where
psi_t is a polynomial whose sum over variable t is 1, so that the term's sum is sigma. If S shows
the value of some map at the end, there is one more variable Y, which is summed by reading at 0, and
its challenge is never 0. Each shown value comes with its own mask entry times that challenge.

The sumcheck tests nothing. In each round the equation that a sumcheck would test fixes one
coefficient of the round's polynomial. That coefficient is not sent, and the verifier computes it
from the equation. So no failure of Psc.verify depends on a value: it fails if the rounds do not
have the plan's shape or if the sizes do not fit. The protocol's argument is that a false claim
shows up later: the row or one of the claims that this block hands on is then false, except with the
rounds' errors, and the blocks that follow test the rows against the committed vectors.

What is handed on. One row on mask entries and on the maps that S keeps, and one claim for each
shown map: the map at the point of challenges, plus its masked term, equals the shown value.

The block is written once, in Blk (OnBytes/Iop/Ground.lean): a dry run of that text gives its
rounds, and a run on a view (what was read and drawn, round by round) gives its part of the
decision. Psc.roundsOf states the rounds once more, as a function of the sizes and of one number of
bits of work. Only tests use it, directly or through Lkp.roundsOf: it gives them the entries of a
plan.

Main definitions: Slot, MaskForm, PointClaim, Psc.Weight, Psc.Claim, Psc.Summand, Psc.Size,
Psc.roundsOf, Psc.hear (reads the rounds), Psc.run (computes what is handed on), Psc.verify (both),
Psc.rowU, pointRow, MapAt, takeSlots, hearDraw, line.

Not claimed here: soundness or hiding. That a challenge for Y is not 0 and that every element read
is in canonical form are rules of the strict reader: the stage before the blocks, which cuts the
file, recomputes the hash chain from which the challenges are drawn and tests the proofs of work.

Order. eps must be drawn after the sum of the hiding polynomial is sent, after the answer to the
sample of every oracle message that holds a mask entry used here, and after everything that enters
the weights, the summand or the target. A prover that knows eps when it chooses that sum proves any
target: it sets the sum so that the first equation fits and is honest from there on, and no later
equation reads the sum. So Psc.verify takes the claim complete and closes the round of the sum
itself. What it cannot see is the caller's duty: that the weights, the summand and the target were
fixed by messages that the chain had taken in before.
-/
import OnBytes.Iop.Ground

namespace OnBytes

/-- One entry of the mask rows of an oracle message. -/
structure Slot where
  /-- the number of the oracle message -/
  oracle : Nat
  /-- the number of the entry in that message's mask rows -/
  index : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A linear form in mask entries: each entry with its coefficient. An entry may occur twice; its
coefficients then add. -/
abbrev MaskForm : Type := List (Slot × E)

/-- A claim on a map V of the witness: V(point) plus the mask form equals the value. -/
structure PointClaim where
  /-- the point -/
  point : List E
  /-- the mask form -/
  masks : MaskForm
  /-- the value -/
  value : E
  deriving Inhabited

namespace Psc

/-- The value at x of the polynomial with coefficients g, lowest degree first. -/
def polyAt (g : List E) (x : E) : E :=
  g.foldr (fun c r => addE (mulE r x) c) zeroE

/-- The sum of the products of the members of two lists, as far as the shorter list goes. -/
def dot (a b : List E) : E :=
  (a.zip b).foldl (fun r p => addE r (mulE p.1 p.2)) zeroE

/-- The loop of powers: so many more powers from c on; done: those so far, the last one first. -/
def powersLoop (x : E) : Nat → E → List E → List E
  | 0, _, done => done.reverse
  | n + 1, c, done => powersLoop x n (mulE c x) (c :: done)

/-- The n elements c, c x, c x^2 and so on. -/
def powers (c x : E) (n : Nat) : List E := powersLoop x n c []

/-- Every coefficient of a mask form times c. -/
def scaleForm (c : E) (m : MaskForm) : MaskForm :=
  m.map fun t => (t.1, mulE c t.2)

/-! ## One variable of a sumcheck -/

/-- How polynomials in one variable are summed: a linear functional, given by its values on 1, X,
X^2 and so on. A round's equation (the sum of the round's polynomial is the running claim) fixes one
coefficient once the others are known, and that one is not sent. -/
structure Weight where
  /-- a polynomial in this variable has d coefficients -/
  d : Nat
  /-- the sums of 1, X, X^2 and so on: d members -/
  moment : List E
  /-- the coefficients, at most d, of a polynomial psi whose sum is 1; the head and the section on
  the hiding polynomial say what it is for -/
  psi : List E
  /-- the number of the coefficient that is not sent -/
  fixed : Nat
  /-- the inverse of the sum of X^fixed -/
  fixedInv : E
  deriving Inhabited

/-- The plain sum g(0) + g(1). The linear coefficient is the one that is not sent: the sum of X is
1, so nothing is divided. -/
def Weight.plain (d : Nat) : Weight where
  d := d
  moment := addE oneE oneE :: List.replicate (d - 1) oneE
  psi := [zeroE, oneE]
  fixed := 1
  fixedInv := oneE

/-- The sum (1 - z) g(0) + z g(1): a sum over 0 and 1 under one factor of the equality polynomial
at z. The constant coefficient is not sent. -/
def Weight.equality (z : E) (d : Nat) : Weight where
  d := d
  moment := oneE :: List.replicate (d - 1) z
  psi := [oneE]
  fixed := 0
  fixedInv := oneE

/-- The sum g(0). -/
def Weight.atZero (d : Nat) : Weight := Weight.equality zeroE d

/-- The sizes of a weight fit each other. Not tested here: that fixedInv is the inverse of
moment[fixed], and that the sum of psi is 1. The C++ makers see to both (Weight::checked,
blocks/iop/hp.h). Both hold for plain, equality and atZero, the makers in this file. -/
def Weight.fits (w : Weight) : Bool :=
  decide (2 ≤ w.d) && w.moment.length == w.d && decide (w.psi.length ≤ w.d) &&
  decide (w.fixed < w.d)

/-- The whole polynomial of a round, from the coefficients that were sent and the claim that the
polynomial must sum to. -/
def Weight.complete (w : Weight) (sent : List E) (claim : E) : List E :=
  let low := sent.take w.fixed
  let high := sent.drop w.fixed
  let rest := dot w.moment (low ++ zeroE :: high)
  low ++ mulE (subE claim rest) w.fixedInv :: high

/-! ## The hiding polynomial

It has the form U(X_1 .. X_k) = the sum over l of w_l(X_l) times the product of psi_j(X_j) over all
j above l. The w_l are polynomials in one variable, and their coefficients are mask entries. A
constant of w_l with l below k could be moved into w_(l+1), so it is fixed to 0; the last variable
keeps its constant. -/

/-- The number of coefficients of the hiding polynomial. Every variable has one for each degree
from 1 up, and the last variable also has a constant. -/
def hidingEntries (vars : List Weight) : Nat := 1 + (vars.map fun w => w.d - 1).sum

/-- The value of the hiding polynomial at the challenges as a linear form in its coefficients,
together with the product of all psi at their challenges. The coefficients are ordered by variable,
then by degree upwards. The coefficient of X_l^t is multiplied by gamma_l^t times the psi of all
later variables at their challenges. -/
def hidingWalk : List (Weight × E) → List E × E
  | [] => ([], oneE)
  | [(w, g)] => (powers oneE g w.d, polyAt w.psi g)
  | (w, g) :: rest =>
    let later := hidingWalk rest
    (powers (mulE later.2 g) g (w.d - 1) ++ later.1, mulE later.2 (polyAt w.psi g))

/-- Only the linear form of hidingWalk. -/
def hidingForm (vars : List Weight) (challenges : List E) : List E :=
  (hidingWalk (vars.zip challenges)).1

/-! ## Claim and summand -/

/-- The claim: the sum of the summand under these weights, plus the mask form, is the target. -/
structure Claim where
  /-- one weight for each variable; the list may be empty -/
  vars : List Weight
  /-- the mask form -/
  masks : MaskForm
  /-- the target -/
  target : E
  deriving Inhabited

/-- A claim on a multilinear map at a point, read as a sum under equality weights. ds: for each
variable the number of coefficients of a round's polynomial. Nothing unless ds has exactly one
number for each coordinate of the point. -/
def Claim.atPoint (c : PointClaim) (ds : List Nat) : Option Claim :=
  if ds.length == c.point.length then
    some
      { vars := (c.point.zip ds).map fun p => Weight.equality p.1 p.2
        masks := c.masks
        target := c.value }
  else none

/-- The public polynomial S. -/
structure Summand where
  /-- the number of maps whose value at the last point is shown -/
  shown : Nat
  /-- the number of maps in which S is affine and whose values are not shown -/
  kept : Nat
  /-- at least the total degree of S in its shown maps; 0 exactly if there are none. Nothing here
  compares it with coeffs. -/
  degree : Nat
  /-- S at a point and at values of the shown maps, as an affine form in the kept maps: the
  constant, then one coefficient for each kept map -/
  coeffs : List E → List E → List E

/-- The variables of the masked sumcheck: those of the claim and, if a map is shown, Y. -/
def varsOf (c : Claim) (S : Summand) : List Weight :=
  if S.shown == 0 then c.vars else c.vars ++ [Weight.atZero (S.degree + 1)]

/-- The number of mask entries that one run uses. It is also the number of elements sent. -/
def masksOf (c : Claim) (S : Summand) : Nat := hidingEntries (varsOf c S) + S.shown

/-- Claim and summand have an allowed form: the degree is 0 exactly if no map is shown; there is
something to sum over or to show; every weight's sizes fit. -/
def formOK (c : Claim) (S : Summand) : Bool :=
  ((S.shown == 0) == (S.degree == 0)) && (decide (0 < S.shown) || !c.vars.isEmpty) &&
  c.vars.all Weight.fits

/-! ## The rounds -/

/-- The sizes of one run: all that its rounds depend on. They do not hold the kind of each weight,
the number of kept maps or the summand's formula. -/
structure Size where
  /-- for each variable of the claim the number of coefficients of a round's polynomial -/
  degree : List Nat
  /-- whether there is a round in Y and a round of values -/
  withY : Bool := true
  /-- the degree of the polynomial of the round in Y -/
  degreeY : Nat := 2
  /-- the number of shown values -/
  values : Nat := 2
  deriving DecidableEq, Repr, Inhabited

/-- The sizes of the run for a claim and a summand. -/
def sizeOf (c : Claim) (S : Summand) : Size where
  degree := c.vars.map (·.d)
  withY := decide (0 < S.shown)
  degreeY := S.degree
  values := S.shown

/-- A round in which the prover sends n elements and one element is drawn. nz: 1 if that element
is never 0, else 0. -/
def rOne (name : String) (kind : Fmt.Kind) (work n nz : Nat) : Fmt.Round where
  entry := { name := name, work := work, msg := 24 * n, drawE := 1, drawNZ := nz }
  kind := kind
  items := List.replicate n .e

/-- The round of the shown values. Nothing is drawn. -/
def rValues (n : Nat) : Fmt.Round where
  entry := { name := "PSC values", msg := 24 * n }
  kind := .nothing
  items := List.replicate n .e

/-- The rounds of one run, for tests. work: the bits of proof of work that every round with a draw
is given here. In a real plan that number belongs to the rounds in which a polynomial that is not
zero may vanish at the challenge, and all rounds of this block with a draw are of that kind. -/
def roundsOf (work : Nat) (x : Size) : List Fmt.Round :=
  [rOne "PSC epsilon" .join work 1 0] ++
  (x.degree.map fun d => rOne "PSC round" .elems work (d - 1) 0) ++
  (if x.withY then [rOne "PSC Y" .elems work x.degreeY 1, rValues x.values] else [])

/-! ## Reading the rounds -/

/-- What the verifier has heard and said in one run. -/
structure Heard where
  /-- the sum of the hiding polynomial -/
  mu : E
  /-- the element that joins the hiding polynomial to the claim -/
  eps : E
  /-- for each variable, Y last: the coefficients sent and the challenge -/
  rounds : List (List E × E)
  /-- the shown values -/
  values : List E
  deriving Inhabited

/-- A round in which the prover sends n elements and one element is drawn. nz: 1 if that element
is never 0, else 0. Returns what was sent and what was drawn. -/
def hearOne (name : String) (kind : Fmt.Kind) (n nz : Nat) : Blk (List E × E) := do
  let q ← Blk.recvEs n
  let g ← Blk.closeOne name kind nz
  pure (q, g)

/-- The rounds of the variables whose polynomials have the listed numbers of sent coefficients. -/
def hearMany : List Nat → Blk (List (List E × E))
  | [] => pure []
  | n :: ns => do
    let a ← hearOne "PSC round" .elems n 0
    let l ← hearMany ns
    pure (a :: l)

/-- Reads the rounds of one run. -/
def hear (x : Size) : Blk Heard := do
  let first ← hearOne "PSC epsilon" .join 1 0
  let mu ← Blk.get first.1.head?
  let inX ← hearMany (x.degree.map (· - 1))
  if x.withY then
    let inY ← hearOne "PSC Y" .elems x.degreeY 1
    let values ← Blk.recvEs x.values
    Blk.closeEmpty "PSC values"
    pure ⟨mu, first.2, inX ++ [inY], values⟩
  else
    pure ⟨mu, first.2, inX, []⟩

/-! ## What is handed on -/

/-- What one run hands on. The row says: the mask form rowMasks, plus the sum over the kept maps of
rowMaps[i] times map i at the point, equals rowTarget. -/
structure Out where
  /-- the challenges of the claim's variables -/
  point : List E
  /-- the row's mask form -/
  rowMasks : MaskForm
  /-- the row's coefficient on each kept map at the point, in the order of the kept maps -/
  rowMaps : List E
  /-- the row's target -/
  rowTarget : E
  /-- one claim for each shown map, all at the point -/
  ends : List PointClaim
  /-- the element that joins the hiding polynomial to the claim -/
  eps : E
  /-- the challenge of Y, if there is one -/
  beta : Option E
  deriving Inhabited

/-- The running claim after the rounds. R: the claim before them. -/
def claimAfter : List Weight → List (List E × E) → E → E
  | w :: ws, (q, g) :: rs, R => claimAfter ws rs (polyAt (w.complete q R) g)
  | _, _, R => R

/-- Computes what is handed on. fresh: mask entries just taken from an oracle message's ledger
(takeSlots), masksOf c S of them. Nothing is returned if a size does not fit or formOK fails. -/
def run (c : Claim) (S : Summand) (fresh : List Slot) (h : Heard) : Option Out :=
  let vars := varsOf c S
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := S.coeffs point h.values
  let hw := hidingWalk (vars.zip challenges)
  let last := claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if S.shown == 0 then none else challenges.getLast?
  if formOK c S && fresh.length == masksOf c S && h.rounds.length == vars.length &&
      h.values.length == S.shown && a.length == 1 + S.kept &&
      ((vars.zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d) then
    some {
      point := point
      rowMasks := fresh.zip hw.1 ++ scaleForm (mulE h.eps hw.2) c.masks
      rowMaps := (a.drop 1).map fun x => mulE h.eps x
      rowTarget := subE last (mulE h.eps (a.headD zeroE))
      ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
        ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
      eps := h.eps
      beta := beta }
  else none

/-- The verifier's part in one run: reads the rounds and computes what is handed on. -/
def verify (c : Claim) (S : Summand) (fresh : List Slot) : Blk Out := do
  let h ← hear (sizeOf c S)
  Blk.get (run c S fresh h)

end Psc

/-! ## Mask entries and rows -/

/-- Takes the next n free mask entries of oracle message o. -/
def takeSlots (o n : Nat) : Blk (List Slot) := do
  pure ((← Blk.takeMasks o n).map fun i => ⟨o, i⟩)

/-- Adds a mask form to a row. -/
def Row.addMasks (r : Row) (m : MaskForm) : Row :=
  m.foldl (fun r t => r.addUnit t.1.oracle .mask t.1.index t.2) r

/-- Says where a map of a summand lives: adds coeff times the map's value at a point to a row, as
structured vectors on oracle messages. Only a map that is the extension of a sent vector has one.
The claim on a shown map that is never sent goes on to line or to the next sumcheck. A kept map that
is never sent is not served by Psc.rowU, which wants a MapAt for every kept map. -/
abbrev MapAt : Type := Row → List E → E → Row

/-- The multilinear map whose table is an aligned block of a table of oracle message o, read as a
vector: the entries number block 2^a to (block + 1) 2^a - 1, with a the number of the point's
coordinates. tableBits: the number of all index bits of the table. If a is above tableBits no
variable is added, where the C++ (block_of_table) ends the process. -/
def blockOfTable (o : Nat) (part : Part) (tableBits block : Nat) : MapAt := fun row point coeff =>
  row.add o part
    ((Tensor.eq point coeff).insertChoice point.length (tableBits - point.length) block)

/-- The multilinear map whose table is one row of a table of o that has rowBits row bits. The point
runs over the places of the row. which must be below 2^rowBits: only its low rowBits bits are
read. -/
def rowOfTable (o : Nat) (part : Part) (rowBits which : Nat) : MapAt := fun row point coeff =>
  row.add o part ((Tensor.eq point coeff).insertChoice 0 rowBits which)

/-- The row of a run. kept: one MapAt for each kept map; nothing is returned if their number
differs. -/
def Psc.rowU (o : Psc.Out) (kept : List MapAt) : Option Row :=
  if kept.length == o.rowMaps.length then
    some ((kept.zip o.rowMaps).foldl (fun r p => p.1 r o.point p.2)
      (({ target := o.rowTarget } : Row).addMasks o.rowMasks))
  else none

/-- A claim on a map at a point as a row. -/
def pointRow (c : PointClaim) (map : MapAt) : Row :=
  (map { target := c.value } c.point oneE).addMasks c.masks

/-! ## Rounds in which the prover sends nothing -/

/-- A round in which the prover sends nothing and n elements are drawn. -/
def rDraw (name : String) (work n : Nat) : Fmt.Round where
  entry := { name := name, work := work, drawE := n }
  kind := .elems

/-- Closes a round in which the prover sends nothing and n elements are drawn, and returns
them. -/
def hearDraw (name : String) (n : Nat) : Blk (List E) := do
  let l ← Blk.closeElems name
  Blk.must (l.length == n)
  pure l

/-- (1 - rho) times the first claim plus rho times the second, at the first claim's point with
rho as one more coordinate. -/
def lineAt (rho : E) (half0 half1 : PointClaim) : PointClaim where
  point := half0.point ++ [rho]
  masks := Psc.scaleForm (subE oneE rho) half0.masks ++ Psc.scaleForm rho half1.masks
  value := addE (mulE (subE oneE rho) half0.value) (mulE rho half1.value)

/-- Two claims at one point of k coordinates, on the halves of a multilinear map in its last
variable (the entries j and j + 2^k of its table), become one claim on the map. The verifier draws
rho, which becomes the last coordinate of the point. rho is a coordinate of the point of the next
sumcheck, so it is drawn in a round of its own, before that sumcheck's first message. Fails if the
two points differ. -/
def line (half0 half1 : PointClaim) : Blk PointClaim := do
  Blk.must (half0.point.length == half1.point.length)
  Blk.test (half0.point == half1.point)
  let l ← hearDraw "LINE" 1
  let rho ← Blk.get l.head?
  pure (lineAt rho half0 half1)

end OnBytes
