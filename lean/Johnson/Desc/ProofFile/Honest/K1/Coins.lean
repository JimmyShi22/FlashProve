-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Coins.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: how many coins a sending's part takes, and how its ONE value of coins is laid into the
rows that the sending's core is handed (Rows, Johnson/Prover/Send/Core.lean). Definitions with code;
no theorem.

The order: message by message in the order of sending; in a message: (1) the main rows' tails, row
0 first, in the rows' own field · (2) for a word with main rows and no answer: its main rows'
messages · (3) the pad, if it lies in a main row: answer 0 first; over the base field three coins an
answer · (4) all entries of the mask rows, entry c of row rho of m rows at place c * m + rho · (5)
the mask rows' tails, row 0 first. The coins of each field are numbered through all messages.

  Ride          a table that rides in a sending and whose mask rows are LAID of fewer coins than
                they have entries, in step (4)'s stead: a fold's fresh table: two public numbers
  hideOfCoins, Ride.count, Ride.lay   (k rounds, 2 ^ h rows): the 2 k + 1 coins are the
                hiding polynomial's coefficients IN THAT POLYNOMIAL's OWN ORDER: (1,1) (1,2) ...
                (k,0) (k,1) (k,2); the table is laid of them by the format's model prover's own
                packing (Fmt.M1.FoldOwn.freshRow, Fmt/M1Fold.lean); 0 beyond
  rideFits, sendFits   TWO PUBLIC TESTS: a riding table fits its message's shape; the job fits its
                place. rowsR IS TOTAL AND TESTS NEITHER: the part (Honest/K1/Part.lean) returns an
                error where sendFits says no, and a law on a pad's coin names it as a premise
                (Honest/K1/PadLaw.lean)
  Steps, stepsOf, Steps.main   a message's five counts; the first three together
  dueMsg, dueR, startR   a message's count by field; a place's; where message number k's coins begin
  cf, ce        a coin by number; 0 beyond the count
  rowsR         message number k's rows: what is no coin is the caller's data; where the caller
                gives none: 0. Every reader is 0 at a row's number from the rows' count on
  due, rowsOf   the two at a place where no table rides

data k r j: message number k, main row r, place j: an element of the base field or of the extension
field, or none. A pad's place and a word's message are laid of coins WHATEVER data says there; from
the code's message length on a row holds 0 WHATEVER data says there (what the core's head asks of
its caller).

Limits. Nothing holds these counts against the book's maker or the format's pages. A row over the
base field takes of data an element of that field alone: another counts as none. The pad's places
are counted by the code's message length, as the statement's page counts them (Own.padMade,
Johnson/Desc/Own/Send.lean); K1's own sample row counts them by the next power of two (K1.Msg.pad,
Johnson/Desc/K1/Own.lean): the two are one under sendFits. cf and ce let 0 stand in beyond the
count: that no row reads there: Honest/K1/CoinsIn.lean. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Prover.Send.Core
import Fmt.M1Fold
import Johnson.Desc.K1.Own
import Johnson.Desc.Own.Lin
import Johnson.Desc.Own.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- **A table that rides: a fold's fresh table**: the fold's rounds k; 2 ^ h rows. Public
numbers. -/
structure Ride where
  k : Nat
  h : Nat
  deriving DecidableEq

/-- A hiding polynomial's coefficients of coins in that polynomial's own order: by variable; in a
variable by rising degree; degrees 1, 2 for every variable but the last; 0, 1, 2 for the last. -/
def hideOfCoins (k : Nat) (c : Nat → GE) : Fmt.M1.FoldOwn.Hide :=
  ⟨fun l t => ofE (c (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)),
    ofE (c (2 * (k - 1)))⟩

/-- Its coins: 2 k + 1. -/
def Ride.count (R : Ride) : Nat := 2 * R.k + 1

/-- Of the coins, by number: the entry at (row, place): by the packing of the format's model prover
(Fmt/M1Fold.lean: freshRow); 0 beyond. -/
def Ride.lay (R : Ride) (c : Nat → GE) (r j : Nat) : GE :=
  toE ((Fmt.M1.FoldOwn.freshRow .two R.k R.h (hideOfCoins R.k c) r).getD j Fmt.Fld.zeroE)

/-- **A PUBLIC TEST: a riding table fits its message's shape**: no sample, no main row, 2 ^ h mask
rows, h ≤ k, at least one round, and the 2 k - h + 1 places that the packing uses lie inside the
mask code's message length. -/
def rideFits (codes : Codes) (s : OracleShape) (R : Ride) : Bool :=
  s.answers == 0 && s.mainRows == 0 && s.maskRows == 2 ^ R.h && decide (R.h ≤ R.k) &&
    decide (1 ≤ R.k) && decide (2 * R.k - R.h + 1 ≤ (codes.mask.getD s.maskCode default).ell)

/-- A message's five counts, in the order of the file's head. -/
structure Steps where
  tails : Nat
  word : Nat
  pad : Nat
  mask : Nat
  maskTails : Nat

def stepsOf (codes : Codes) (s : OracleShape) (ride : Option Ride) : Steps :=
  let C := codes.base.getD s.code default
  let Z := codes.mask.getD s.maskCode default
  { tails := s.mainRows * C.r
    word := if s.mainRows != 0 && s.answers == 0 then s.mainRows * C.ell else 0
    pad := if s.maskRows == 0 && s.answers != 0 then
      (if s.mainDeg == 3 then 1 else 3) * s.answers else 0
    mask := (ride.map (·.count)).getD (s.maskRows * Z.ell)
    maskTails := s.maskRows * Z.r }

/-- The coins of a message's main rows. -/
def Steps.main (n : Steps) : Nat := n.tails + n.word + n.pad

/-- A message's count, by field. -/
def dueMsg (codes : Codes) (s : OracleShape) (ride : Option Ride) : Due :=
  let n := stepsOf codes s ride
  if s.mainDeg == 3 then ⟨0, n.main + n.mask + n.maskTails⟩ else ⟨n.main, n.mask + n.maskTails⟩

/-- Where message number k's coins begin. -/
def startR (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) : Due :=
  (List.range k).foldl (fun a j => a.plus (dueMsg P.codes (shapeAt P j) (ride j))) ⟨0, 0⟩

/-- **A place's count.** -/
def dueR (P : K1.Par) (ride : Nat → Option Ride) : Due := startR P ride P.sent.size

/-- **A PUBLIC TEST: THE JOB FITS ITS PLACE**: every code's message length is a power of two (the
sample rows count a pad's places by the next power of two, rowsR by the length) · every message has
an admitted shape: the plan's own test (Own.sentShapeFits, Johnson/Desc/Own/Sent.lean): it has a
row; the numbers of the codes that its rows name lie in the arrays; its main rows are over one of
the two fields · every sampled message's pads fit their row · every riding table fits its message's
shape. -/
def sendFits (P : K1.Par) (ride : Nat → Option Ride) : Bool :=
  Own.lengthsFit P.codes && (List.range P.sent.size).all fun k =>
    Own.sentShapeFits P.codes (shapeAt P k) &&
      (decide ((shapeAt P k).answers = 0) || (K1.Msg.of P.codes (shapeAt P k)).padFits) &&
      ((ride k).map (rideFits P.codes (shapeAt P k))).getD true

/-- A coin by number; 0 beyond the count. -/
def cf {d : Due} (c : Cs d) (i : Nat) : GF := if h : i < d.f then c.f ⟨i, h⟩ else 0
def ce {d : Due} (c : Cs d) (i : Nat) : GE := if h : i < d.e then c.e ⟨i, h⟩ else 0

/-- **Message number k's rows.** -/
def rowsR (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k : Nat) : Rows :=
  let s := shapeAt P k
  let C := P.codes.base.getD s.code default
  let Z := P.codes.mask.getD s.maskCode default
  let n := stepsOf P.codes s (ride k)
  let a := startR P ride k
  let overE := s.mainDeg == 3
  -- the number, among the pad's coins, of the place j of the row r; none: no pad's place
  let padAt (r j : Nat) : Option Nat :=
    if n.pad != 0 && r + 1 == s.mainRows && decide (C.ell - n.pad ≤ j) && decide (j < C.ell) then
      some (j - (C.ell - n.pad)) else none
  -- the number, among the message's main coins, of the entry (r, j); none: the caller's data
  let coinAt (r j : Nat) : Option Nat :=
    if n.word != 0 then (if j < C.ell then some (n.tails + r * C.ell + j) else none)
    else (padAt r j).map (n.tails + ·)
  let m0 := a.e + if overE then n.main else 0
  { mainE := fun r j => if !overE || decide (s.mainRows ≤ r) || decide (C.ell ≤ j) then 0 else
      match coinAt r j with
      | some i => ce c (a.e + i)
      | none =>
        match data k r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap GF GE x
        | none => 0
    mainF := fun r j => if overE || decide (s.mainRows ≤ r) || decide (C.ell ≤ j) then 0 else
      match coinAt r j with
      | some i => cf c (a.f + i)
      | none =>
        match data k r j with
        | some (.inl x) => x
        | _ => 0
    mainTlE := fun r q => if overE && decide (r < s.mainRows) && decide (q < C.r) then
      ce c (a.e + r * C.r + q) else 0
    mainTlF := fun r q => if !overE && decide (r < s.mainRows) && decide (q < C.r) then
      cf c (a.f + r * C.r + q) else 0
    mask := fun r j =>
      match ride k with
      | some R => if r < s.maskRows ∧ j < Z.ell then
          R.lay (fun i => if i < R.count then ce c (m0 + i) else 0) r j else 0
      | none => if r < s.maskRows ∧ j < Z.ell then ce c (m0 + j * s.maskRows + r) else 0
    maskTl := fun r q => if r < s.maskRows ∧ q < Z.r then ce c (m0 + n.mask + r * Z.r + q) else 0 }

/-- The two at a place where no table rides. -/
def due (P : K1.Par) : Due := dueR P fun _ => none
def rowsOf (P : K1.Par) (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (due P)) (k : Nat) :
    Rows := rowsR P (fun _ => none) data c k

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.Ride
#print axioms ProofFile.Honest.K1.hideOfCoins
#print axioms ProofFile.Honest.K1.Ride.count
#print axioms ProofFile.Honest.K1.Ride.lay
#print axioms ProofFile.Honest.K1.rideFits
#print axioms ProofFile.Honest.K1.Steps
#print axioms ProofFile.Honest.K1.stepsOf
#print axioms ProofFile.Honest.K1.Steps.main
#print axioms ProofFile.Honest.K1.dueMsg
#print axioms ProofFile.Honest.K1.startR
#print axioms ProofFile.Honest.K1.dueR
#print axioms ProofFile.Honest.K1.sendFits
#print axioms ProofFile.Honest.K1.cf
#print axioms ProofFile.Honest.K1.ce
#print axioms ProofFile.Honest.K1.rowsR
#print axioms ProofFile.Honest.K1.due
#print axioms ProofFile.Honest.K1.rowsOf
