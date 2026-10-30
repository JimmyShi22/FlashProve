-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestLookProver.lean: a prover for a lookup on hidden values, for tests.

The verifier's side of the lookup (OnBytes/Model/Look.lean) tests no equation by itself. It turns
the messages into linear claims on hidden values. This file holds a prover for small groups of
calls, written from the description of the argument, and a function that evaluates every claim on
that prover's data. Four files in OnBytes/Model/ run it: TestLookHonest.lean,
TestLookHonestFaults.lean, TestLookHonestThree.lean and TestLookHonestThreeFaults.lean.
TestLookStack.lean uses only its script. The program does not import these files.

The prover here uses no masks: all entries of its mask row and all hiding polynomials are 0. Then a
hidden value is what was shown for it, and a claim's value is its public part. How masks enter a
claim is tested in OnBytes/Model/TestPsc.lean. The verifier's draws are made-up elements; no hash is
called.

Main definitions: Prover, roundP, levelP, Setup, Fault, two, three, prove, claimValues, valuesOn,
allZero.

The prover here is not the C++ prover. It was written from the same reading of the argument as
OnBytes/Model/Look.lean, so a misreading that both share is not found here. It also calls functions
of the verifier's side: Forest.shape and Forest.pubRun for the numbers of the trees and of the
padding keys, orderForestRange and orderDefault for the order of the variables, eqTab, and
Call.tauAt. claimValues reads the planes under the verifier's own weights, phiB and phiP. An error
in one of these functions can go unseen here. No guard alters a message; all faults are in the
prover's data.
-/
import OnBytes.Model.TestLook

namespace OnBytes.Model.Forest.Honest

/-! ## The prover's script -/

/-- A made-up element of E. The constant is one of the SplitMix64 generator's, a publicly known
mixing function. -/
def made (s : Nat) : E :=
  let w (i : Nat) : F := ((3 * s + i + 1) * 0x9E3779B97F4A7C15 % 2 ^ 64 % pW.toNat).toUInt64
  E.mk3 (w 0) (w 1) (w 2)

/-- What a prover has written so far: the closed rounds, the open message, the number of draws. -/
structure Script where
  /-- the closed rounds -/
  rounds : Array Fmt.RoundView := #[]
  /-- the elements of the open message -/
  message : Array E := #[]
  /-- how many elements the verifier has drawn -/
  draws : Nat := 0

/-- A prover: it writes messages and is told what the verifier draws. -/
abbrev Prover : Type → Type := StateM Script

/-- Adds elements to the open message. -/
def send (xs : List E) : Prover Unit :=
  modify fun s => { s with message := s.message ++ xs.toArray }

/-- Closes the round: the verifier draws n elements. -/
def draw (n : Nat) : Prover (Array E) :=
  modifyGet fun s =>
    let d := (Array.range n).map fun i => made (s.draws + i)
    (d, { rounds := s.rounds.push
            { vals := s.message.toList.map fun x => Fmt.ItemValue.e x.triple,
              drawn :=
                { elems := d.toList.map E.triple, poss := [], trits := [], digest := none } },
          message := #[], draws := s.draws + n })

/-- Closes the round: the verifier draws one element. -/
def draw1 : Prover E := do
  pure ((← draw 1).getD 0 zeroE)

/-! ## A sumcheck without masks -/

/-- A sumcheck under way: the coordinates that are still free, from the top bit down; the tables of
the maps on these; the challenges so far, by coordinate. -/
structure Run where
  /-- the coordinates that are still free -/
  free : List Nat
  /-- the maps' tables on the free coordinates -/
  tabs : List (Array E)
  /-- the challenges, by coordinate -/
  r : Array E

/-- The inverse of 2 in the base field, as an element of E. -/
def half : E := ofF 9223372034707292161

#guard mulE half (ofF 2) == oneE

/-- One round, in coordinate c. z is the equality point, comb the summand as a function of the maps'
values. The round polynomial is found from its values at 0, 1 and 2. Its constant is not sent. eps
multiplies what is sent. degree is the number of coefficients sent, 2 or 1. -/
def roundP (eps : E) (z : Array E) (comb : List E → E) (s : Run) (c degree : Nat) :
    Prover Run := do
  let rest := s.free.filter (· != c)
  let low := 2 ^ (s.free.length - 1 - s.free.idxOf c)
  let w := eqTab (rest.map fun i => z.getD i zeroE).toArray
  let at0 (i : Nat) : Nat := i / low * (2 * low) + i % low
  let q (x : Nat) : E := (List.range w.size).foldl
    (fun acc i =>
      let vals := s.tabs.map fun t =>
        let a := t.getD (at0 i) zeroE
        let b := t.getD (at0 i + low) zeroE
        if x = 0 then a else if x = 1 then b else subE (addE b b) a
      addE acc (mulE (w.getD i zeroE) (comb vals)))
    zeroE
  let q0 := q 0
  let q1 := q 1
  let c2 := mulE half (addE (subE (q 2) (addE q1 q1)) q0)
  let c1 := subE (subE q1 q0) c2
  send (([c1, c2].take degree).map (mulE eps))
  let x ← draw1
  let bound := s.tabs.map fun t => (Array.range w.size).map fun i =>
    let a := t.getD (at0 i) zeroE
    addE a (mulE x (subE (t.getD (at0 i + low) zeroE) a))
  pure { free := rest, tabs := bound, r := s.r.setIfInBounds c x }

/-- The beginning of a sumcheck: the hiding polynomial's sum, which is 0; then eps is drawn. -/
def begin : Prover E := do
  send [zeroE]
  draw1

/-- All rounds of a sumcheck over the coordinates of z. order lists pairs of a coordinate and the
degree of its round. Returns the challenges by coordinate and the maps' values at that point. -/
def roundsP (eps : E) (z : Array E) (order : List (Nat × Nat)) (tabs : List (Array E))
    (comb : List E → E) : Prover (Array E × List E) := do
  let s ← order.foldlM (fun (s : Run) (x : Nat × Nat) => roundP eps z comb s x.1 x.2)
    { free := List.range z.size, tabs := tabs, r := Array.replicate z.size zeroE }
  pure (s.r, s.tabs.map (·.getD 0 zeroE))

/-- The end of a sumcheck with shown values. Without masks the polynomial in the further variable
is a constant, which is not sent. -/
def ends (degreeInY : Nat) (values : List E) : Prover Unit := do
  send (List.replicate degreeInY zeroE)
  let _ ← draw1
  send values
  let _ ← draw 0

/-- The product of two values. -/
def times : List E → E
  | [a, b] => mulE a b
  | _ => zeroE

/-- One level of a product tree. next holds the 2^(mu + 1) entries of the level below; the top bit
of an index there says which factor it is. order lists variables: variable i is bit i of an index.
Returns the point for the level below. -/
def levelP (mu : Nat) (rho next : Array E) (order : List Nat) : Prover (Array E) := do
  let eps ← begin
  let (r, values) ← roundsP eps rho (order.map fun i => (mu - 1 - i, 2))
    [next.extract 0 (2 ^ mu), next.extract (2 ^ mu) (2 ^ (mu + 1))] times
  ends 2 values
  pure (#[← draw1] ++ r)

/-- The level above a level of a product tree. -/
def up (a : Array E) : Array E :=
  (Array.range (a.size / 2)).map fun x => mulE (a.getD x zeroE) (a.getD (a.size / 2 + x) zeroE)

/-- A product tree's levels, the smallest first: the leaves and the given number of levels above
them. -/
def levels : Nat → Array E → List (Array E)
  | 0, a => [a]
  | n + 1, a => levels n (up a) ++ [a]

/-! ## The data

Two groups. In the first, call 0 has 2^10 keys in the range table of 2^5 rows (row t has the value
t) and call 1 has 2^11 keys in a written table of 2^6 rows. There are three trees of 2^10 keys and
one tree that holds only padding, so v = 12 and d = 7. In the second, three calls have one tree
each, so that no call has the number 3 and tree number 3 holds only padding; again v = 12 and
d = 7.
-/

/-- A group of calls with made-up keys. -/
structure Setup where
  /-- the calls -/
  calls : Array Call
  /-- for each call the number of its places, from place 0 on, that hold a real key; the places
  after them are padding -/
  real : Array Nat
  /-- the logarithm of the number of rows of the matrix that holds the planes -/
  lm : Nat

/-- What can be wrong with the prover's data. -/
structure Fault where
  /-- a call, a place, and the value that is put there instead of the key -/
  key : Option (Nat × Nat × F) := none
  /-- an index into the planes, and the value that is put there instead of the bit -/
  bit : Option (Nat × F) := none
  /-- two pairs of a call and a row: the first row's count, which must not be 0, is one less, and
  the second's one more -/
  moved : Option ((Nat × Nat) × (Nat × Nat)) := none

/-- A written table of 2^6 rows. -/
def table1 : Array F := (Array.range 64).map fun t => (1000 + 7 * t).toUInt64

/-- Two calls. The second has two trees. Tree number 3 belongs to no call and holds only padding. -/
def two : Setup where
  calls := #[{ name := "range", n := 10, k := 5, kappa := 5, t0 := 3 },
    { name := "written", n := 11, k := 6, kappa := 5, fn := 1, t0 := 5, tau := some table1 }]
  real := #[1000, 1500]
  lm := 7

/-- Three calls of one tree each. No call has the number 3, and tree number 3 holds only padding. -/
def three : Setup where
  calls := #[
    { name := "written", n := 10, k := 5, kappa := 5, fn := 1, t0 := 5,
      tau := some (table1.extract 0 32) },
    { name := "range", n := 10, k := 5, kappa := 5, t0 := 3 },
    { name := "last", n := 10, k := 5, kappa := 5, t0 := 0 }]
  real := #[1024, 700, 1]
  lm := 8

/-- The shape, with the numbers of padding keys, or the name of a refusal. -/
def Setup.shapeOrName (S : Setup) : Except String Shape := do
  let h ← shape S.calls 10
  let pub ← (List.range h.NC).foldlM
    (fun (p : Array Nat) c =>
      pubRun h p c (S.real.getD c 0) (2 ^ (S.calls.getD c {}).n - S.real.getD c 0))
    (noPub h)
  pure { h with pub := pub }

/-- The shape, with the numbers of padding keys. -/
def Setup.shape (S : Setup) : Shape := S.shapeOrName.toOption.getD {}

#guard two.shape.pub == #[0, 548, 24] && two.shape.v == 12 && two.shape.d == 7
#guard three.shape.pub == #[0, 324, 1023] && three.shape.v == 12 && three.shape.d == 7

/-- The table row that the key at a place of a call points to. -/
def Setup.rowOf (S : Setup) (c i : Nat) : Nat := (i * i + 3 * i + c) % 2 ^ (S.calls.getD c {}).k

/-- The key at a place of a call. -/
def Setup.keyAt (S : Setup) (f : Fault) (c i : Nat) : F :=
  let k := S.calls.getD c {}
  if f.key.any fun x => x.1 == c && x.2.1 == i then (f.key.map (·.2.2)).getD 0
  else k.tauAt (if i < S.real.getD c 0 then S.rowOf c i else k.t0)

/-- The key vector of a call. -/
def Setup.keysOf (S : Setup) (f : Fault) (c : Nat) : Array E :=
  (Array.range (2 ^ (S.calls.getD c {}).n)).map fun i => ofF (S.keyAt f c i)

/-- How many real keys of call c point to each row, by the honest rule. -/
def Setup.countsOf (S : Setup) (c : Nat) : Array Nat :=
  (List.range (S.real.getD c 0)).foldl (fun a i => a.modify (S.rowOf c i) (· + 1))
    (Array.replicate 64 0)

/-- The counts of all calls, with the count that the fault moves. -/
def Setup.counts (S : Setup) (f : Fault) : Array (Array Nat) :=
  let honest := (Array.range S.shape.NC).map S.countsOf
  match f.moved with
  | none => honest
  | some (a, b) =>
    (honest.modify a.1 (·.modify a.2 (· - 1))).modify b.1 (·.modify b.2 (· + 1))

/-- The planes: entry ((t 2^cK + c) 32 + j) is bit j of the count of row t of call c. Nothing is
counted under a number that is no call's. -/
def Setup.planes (S : Setup) (f : Fault) : Array E :=
  let h := S.shape
  let counts := S.counts f
  (Array.range (2 ^ (h.d + 5))).map fun i =>
    if f.bit.any fun x => x.1 == i then ofF ((f.bit.map (·.2)).getD 0)
    else
      ofF ((counts.getD (i / 32 % 2 ^ h.cK) #[]).getD (i / 32 / 2 ^ h.cK) 0 / 2 ^ (i % 32) %
        2).toUInt64

/-- The value of a multilinear map, given by its table, at a point. -/
def mle (a z : Array E) : E :=
  (eqTab z).zip a |>.foldl (fun s x => addE s (mulE x.1 x.2)) zeroE

/-! ## The prover of the lookup -/

/-- The messages of the lookup, in the order of the argument. -/
def prove (S : Setup) (f : Fault) : Prover Unit := do
  let h := S.shape
  let theta ← draw1
  let alpha ← draw1
  let moved (c : Nat) (x : F) : E := addE (ofF x) (scaleE c.toUInt64 theta)
  let call (c : Nat) : Call := S.calls.getD c {}
  let keyLeaves := (Array.range (2 ^ h.v)).map fun i =>
    let y := i % 2 ^ h.rK
    let c := h.callOf.getD y 0
    -- y - first[c] says which of its call's trees tree y is
    if y < h.NT then
      subE alpha (moved c (S.keyAt f c ((y - h.first.getD c 0) * 2 ^ h.dT + i / 2 ^ h.rK)))
    else subE alpha (moved 0 ((call 0).tauAt (call 0).t0))
  let b := S.planes f
  let factor := (Array.range (2 ^ (h.d + 5))).map fun i =>
    let c := min (i / 32 % 2 ^ h.cK) (h.NC - 1)
    subE (subE alpha oneE) (moved c ((call c).tauAt (i / 32 / 2 ^ h.cK % 2 ^ (call c).k)))
  let tableLeaves := (Array.range (2 ^ (h.d + 5))).map fun i =>
    addE oneE (mulE (b.getD i zeroE) (factor.getD i zeroE))
  let K := levels h.v keyLeaves
  let T := levels h.d tableLeaves
  let G (j : Nat) : E := (T.getD 0 #[]).getD j zeroE
  -- P[i] is the power P_(31 - i)
  let P := (List.range 31).foldl
    (fun (l : Array E) i =>
      let p := l.getD i zeroE
      l.push (mulE (mulE p p) (G (30 - i))))
    #[G 31]
  for j in List.range 31 do
    let _ ← begin
    let shown := [P.getD (30 - j) zeroE, G j]
    ends 3 (if j = 0 then (K.getD 0 #[]).getD 0 zeroE :: shown else shown)
  let rhoT := (← draw 5).reverse
  let _ ← (List.range h.v).foldlM
    (fun (rho : Array E) mu =>
      levelP mu rho (K.getD (mu + 1) #[])
        (if mu + 1 = h.v then orderForestRange mu h.rK else orderDefault mu))
    #[]
  let rhoT ← (List.range h.d).foldlM
    (fun (rho : Array E) l => levelP (5 + l) rho (T.getD (l + 1) #[]) (orderDefault (5 + l))) rhoT
  let m := h.d + 5
  let eps ← begin
  let _ ← roundsP eps rhoT ((List.range m).map fun j => (j, if j < h.d then 2 else 1)) [b, factor]
    fun x => addE oneE (times x)
  let point := (← draw m).reverse
  let eps ← begin
  let (_, values) ← roundsP eps point ((List.range m).map fun j => (j, 2)) [b]
    fun x => subE (times (x ++ x)) (x.getD 0 zeroE)
  ends 2 values

/-! ## The verifier's side on these messages -/

/-- The sum over the rows of the planes' matrix of a weight times the entry in column col. The
matrix has 2^lm rows: row (the low lm - 5 bits of t, then j), column (c, then the other bits of
t). -/
def onColumn (S : Setup) (b phi : Array E) (col : Nat) : E :=
  let h := S.shape
  let w := h.kT + 5 - S.lm
  (List.range (2 ^ S.lm)).foldl
    (fun s row =>
      let t := col % 2 ^ w * 2 ^ (S.lm - 5) + row / 32
      addE s (mulE (phi.getD row zeroE)
        (b.getD ((t * 2 ^ h.cK + col / 2 ^ w) * 32 + row % 32) zeroE)))
    zeroE

/-- Runs the verifier on the lookup's messages, makes all its claims on the prover's data, and
returns their values. -/
def claimValues (S : Setup) (f : Fault) : SubM (Array E) := do
  let g ← pad S.calls S.shape.pub 10
  let b := S.planes f
  let phi0 ← SubM.get (phiB g S.lm 0)
  let phi1 ← SubM.get (phiB g S.lm 1)
  let onPlanes ← planeClaims g S.lm
    (fun e col => pure (Aff.ofConst (onColumn S b (if e = 0 then phi0 else phi1) col)))
    (fun col => pure (Aff.ofConst (onColumn S b (phiP S.lm) col)))
  let onKeys ← join g ((Array.range S.calls.size).map fun c =>
    Aff.ofConst (mle (S.keysOf f c) (g.zk.getD c #[])))
  (g.rows ++ onPlanes ++ #[onKeys]).mapM SubM.publicPart

/-- The values of all claims on the messages of the prover with the given fault; none if the walk
fails or does not use up all rounds. -/
def valuesOn (S : Setup) (f : Fault) : Option (Array E) :=
  let h := S.shape
  let rounds := (Id.run (StateT.run (prove S f) {})).2.rounds.toList
  match Blk.walk (StateT.run (claimValues S f) (({} : Fork).slots (elems h)))
      { entries := Test.lookupEntries h.v h.d true, st := {} } [] rounds with
  | some (x, []) => some x.1
  | _ => none

/-- True if the walk goes through and all claims are 0; false if it goes through and some claim is
not 0; none if the walk fails. -/
def allZero (S : Setup) (f : Fault) : Option Bool := (valuesOn S f).map (·.all isZeroE)

/-- The numbers of the claims that are not 0, in the order of claimValues. At v = 12 and d = 7: 0 to
30 the tie, 31 to 42 the key levels, 43 to 49 the table levels, 50 the bits' sumcheck, 51 to 53 the
claims on the planes, 54 the claim on the key vectors. none if the walk fails. -/
def notZeroAt (S : Setup) (f : Fault) : Option (List Nat) :=
  (valuesOn S f).map fun x => (List.range x.size).filter fun i => !isZeroE (x.getD i zeroE)

end OnBytes.Model.Forest.Honest
