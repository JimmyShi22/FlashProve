-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/Text.lean: plain data of a lookup, and end claims, read from a text of lines and written
as one.

Why. Transcripts of the C++ lookup's own prover come as files. This reader takes such a file, as a
string, to the plain data (Flat) and to the end claims that the C++ verifier has handed on
(EndClaim, OnBytes/G4/Flat.lean), so that a test can compare them with the program's in Lean.

The text. One item a line; words are parted by single blanks; numbers are decimal. An element is
three words w0 w1 w2, each below 2^64 (the reader does not test whether it is below p; Flat.fits
tests that of the vectors' words and of the drawn words). Empty lines and lines that begin with "#"
are passed over. Every other line is one of these:
  R r name      round number r, from 1, has this name (the name may hold blanks)
  S r w0 w1 w2  the next element sent in round r
  D r w0 w1 w2  the next element drawn in round r
  K i w0 w1 w2  entry i, from 0, of the keys that are not padding
  P i w0 w1 w2  entry i of the bits of the multiplicities
  M i w0 w1 w2  entry i of the mask entries
  C c T w0 w1 w2    the target of end claim number c, from 1
  C c K i w0 w1 w2  its coefficient on entry i of the keys; likewise C c P i and C c M i
The lines R come in the order of the rounds, one for each round, without a gap. Elements of a round
are in the order of their lines. The lines K, P and M come each in the order of their entries,
without a gap. A coefficient that has no line is 0; an entry named twice is refused. Each claim has
one target, and the targets' lines come in the order of the claims, from 1, without a gap.
The lines S and D of a round may stand anywhere in the text. There is no end mark: a text that is
cut behind a whole line is read as far as it goes, so a test asks for the numbers of rounds, entries
and claims (Flat.fits, judge). The names are read and compared by nobody here: a test does.

Main definitions: Line, lineOf, Told, told, Told.flat, Told.names, Told.claims; for writing: spell,
spellList, textOf.
Not claimed. No theorem. Nothing on who wrote a text.


-/
import OnBytes.G4.Flat

namespace OnBytes.G4

/-- A number written in decimal digits and nothing else. -/
def numberOf (s : String) : Option Nat :=
  if !s.isEmpty && s.all Char.isDigit then s.toNat? else none

/-- A decimal number below 2^64 as a word. -/
def wordOf (s : String) : Option UInt64 :=
  (numberOf s).bind fun n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none

/-- Three words as an element. -/
def elementOf : List String → Option E
  | [a, b, c] => do pure (E.mk3 (← wordOf a) (← wordOf b) (← wordOf c))
  | _ => none

/-- One of the three vectors. -/
inductive Vec where
  | keys
  | planes
  | masks
  deriving DecidableEq, Repr, Inhabited

/-- The vector of a letter. -/
def vecOf : String → Option Vec
  | "K" => some .keys
  | "P" => some .planes
  | "M" => some .masks
  | _ => none

/-- A line as read. -/
inductive Line where
  | name (round : Nat) (name : String)
  | sent (round : Nat) (x : E)
  | drawn (round : Nat) (x : E)
  | entry (v : Vec) (index : Nat) (x : E)
  | target (claim : Nat) (x : E)
  | coeff (claim : Nat) (v : Vec) (index : Nat) (x : E)
  deriving DecidableEq, Repr, Inhabited

/-- Reads a line that is neither empty nor a comment. -/
def lineOf (s : String) : Option Line :=
  match s.splitOn " " with
  | "R" :: r :: w :: ws => (numberOf r).map fun r => .name r (" ".intercalate (w :: ws))
  | "S" :: r :: ws => do pure (.sent (← numberOf r) (← elementOf ws))
  | "D" :: r :: ws => do pure (.drawn (← numberOf r) (← elementOf ws))
  | "C" :: c :: "T" :: ws => do pure (.target (← numberOf c) (← elementOf ws))
  | "C" :: c :: v :: i :: ws => do pure (.coeff (← numberOf c) (← vecOf v) (← numberOf i) (← elementOf ws))
  | v :: i :: ws => do pure (.entry (← vecOf v) (← numberOf i) (← elementOf ws))
  | _ => none

/-- All lines of a text. -/
abbrev Told : Type := List Line

/-- Reads a text. Nothing if a line is of no kind. -/
def told (text : String) : Option Told :=
  ((text.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#").mapM lineOf

/-- The numbers are first, first + 1, first + 2 and so on. -/
def inARow (first : Nat) (l : List Nat) : Bool := l == (List.range l.length).map (first + ·)

/-- The rounds' names, if the lines R come in the order of the rounds, from 1, without a gap. -/
def Told.names (T : Told) : Option (List String) :=
  let l := T.filterMap fun x =>
    match x with
    | .name r n => some (r, n)
    | _ => none
  if inARow 1 (l.map (·.1)) then some (l.map (·.2)) else none

/-- One of the three vectors, if its lines come in the order of the entries, from 0, without a gap.
-/
def Told.vector (T : Told) (v : Vec) : Option (List E) :=
  let l := T.filterMap fun x =>
    match x with
    | .entry w i e => if w == v then some (i, e) else none
    | _ => none
  if inARow 0 (l.map (·.1)) then some (l.map (·.2)) else none

/-- The plain data. Nothing if the names or a vector have a gap, or an element is of a round that
has no name. -/
def Told.flat (T : Told) : Option Flat := do
  let n := (← T.names).length
  let inRange := T.all fun x =>
    match x with
    | .sent r _ => decide (1 ≤ r) && decide (r ≤ n)
    | .drawn r _ => decide (1 ≤ r) && decide (r ≤ n)
    | _ => true
  if !inRange then none
  pure {
    rounds := (List.range n).map fun i =>
      { sent := T.filterMap fun x =>
          match x with
          | .sent r e => if r == i + 1 then some e else none
          | _ => none
        drawn := T.filterMap fun x =>
          match x with
          | .drawn r e => if r == i + 1 then some e else none
          | _ => none }
    keys := ← T.vector .keys
    planes := ← T.vector .planes
    masks := ← T.vector .masks }

/-- The coefficients of claim c on a vector of the given length. Nothing if an entry is named twice
or lies beyond the vector. -/
def Told.coeffs (T : Told) (c : Nat) (v : Vec) (length : Nat) : Option (List E) :=
  let l := T.filterMap fun x =>
    match x with
    | .coeff d w i e => if d == c && w == v then some (i, e) else none
    | _ => none
  if Lkp.allPairs (fun a b => a != b) (l.map (·.1)) && l.all fun p => decide (p.1 < length) then
    some ((List.range length).map fun i => (l.lookup i).getD zeroE)
  else none

/-- The end claims of a text, for vectors of the lengths of the lookup's. Nothing if the targets do
not come in the order of the claims, from 1, without a gap, or a coefficient is of a claim without a
target, or Told.coeffs gives nothing. -/
def Told.claims (T : Told) (S : Lkp.Public) : Option (List EndClaim) := do
  let ts := T.filterMap fun x =>
    match x with
    | .target c e => some (c, e)
    | _ => none
  let known := T.all fun x =>
    match x with
    | .coeff c _ _ _ => decide (1 ≤ c) && decide (c ≤ ts.length)
    | _ => true
  if !(inARow 1 (ts.map (·.1)) && known) then none
  ts.mapM fun p => do
    pure {
      keys := ← T.coeffs p.1 .keys (realPlaces S).length
      planes := ← T.coeffs p.1 .planes (planeBits S)
      masks := ← T.coeffs p.1 .masks (Lkp.allMasks S)
      target := p.2 }

/-! ## Writing -/

/-- An element as three decimal words. -/
def spell (x : E) : String := s!"{x.c0.toNat} {x.c1.toNat} {x.c2.toNat}"

/-- The lines of a list under a head, with each member's number from 0. -/
def spellList (head : String) (l : List E) (skipZero : Bool := false) : List String :=
  (((List.range l.length).zip l).filter fun p => !(skipZero && isZeroE p.2)).map fun p =>
    s!"{head} {p.1} {spell p.2}"

/-- The text of plain data and end claims, in the form that `told` reads. Rounds of t beyond the
number of the entries of S are left out, and the names written are those of `entries S`, not of the
data. That `told` reads the text back to t and the claims is no law and no test of this file. -/
def textOf (S : Lkp.Public) (t : Flat) (claims : List EndClaim) : String :=
  "\n".intercalate (
    (((List.range t.rounds.length).zip ((entries S).zip t.rounds)).flatMap fun p =>
      s!"R {p.1 + 1} {p.2.1.name}" ::
        (p.2.2.sent.map fun x => s!"S {p.1 + 1} {spell x}") ++
        (p.2.2.drawn.map fun x => s!"D {p.1 + 1} {spell x}")) ++
    spellList "K" t.keys ++ spellList "P" t.planes ++ spellList "M" t.masks ++
    ((List.range claims.length).zip claims).flatMap fun p =>
      s!"C {p.1 + 1} T {spell p.2.target}" ::
        spellList s!"C {p.1 + 1} K" p.2.keys true ++ spellList s!"C {p.1 + 1} P" p.2.planes true ++
        spellList s!"C {p.1 + 1} M" p.2.masks true) ++ "\n"

end OnBytes.G4
