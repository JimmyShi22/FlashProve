-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwRun.lean.
The flat function at the small lookup Lkp.o65, and what a test computes on it at one transcript.

Definitions alone: Lean generates code for all of them. The tests that call `report`, `reportAt`
and `expected`, and their recorded texts, are [not in this library].

Main names:
  `o65V t`: TwV.vOf at the numbers of Lkp.o65 (o65N), in the field Cb.Gl.E, on the places
    Fin 15 ⊕ Fin 16 ⊕ Fin 104, at the plain data t : OnBytes.G4.Flat read by Slice.readE.
  `msgOf t`, `SRow.Holds`: the three committed messages of t on these places; a row holds at them.
  `spread`, `inPortOrder`: a row as coefficients on the three messages; the rows in the order of
    the byte-level verifier's end claims, by the one re-indexing TwNums.o65S.reIdx.
  `writeE`, `writeClaim`: an element of Cb.Gl.E in words below the prime.
  `Report`, `reportOn`, `reportAt`, `report`, `expected`: what is tested at one transcript.
Limits: it holds no theorem. That the rows in that order are the byte-level verifier's end claims
(the fields vsPort, vsCpp) is a matter of those tests: no theorem and no test in this library
compares `o65V` with OnBytes.G4.endClaims. At o65N the field count of Report is 17 at every input,
since the function's walks recurse on the public numbers. The field points compares TwV.pointsOf, a
function made for this test; eight of the fourteen points are empty, and both sides take their
orders from the same two functions (Lkp.defaultOrder, Lkp.orderBeginning), so a wrong order it
cannot see.

-/
import OnBytes.Tie.Pv.Lookup.Out.TwVN
import OnBytes.Slice.ProgField
import OnBytes.G4.Text
import OnBytes.G4.Points

set_option autoImplicit false

namespace TwV
open OnBytes OnBytes.G4

abbrev F : Type := Cb.Gl.E

/-- the places: the entries of the three committed messages -/
abbrev Pl : Type := Cb.Tw.JOf TwNums.o65S

def o65N : Nums Pl F := numsJ F TwNums.o65S

/-- the plain data's rounds, read into Cb.Gl.E -/
def readRounds (t : Flat) : Rounds F :=
  t.rounds.map fun r => (r.sent.map Slice.readE, r.drawn.map Slice.readE)

/-- the three committed messages, read into Cb.Gl.E, on these places -/
def msgOf (t : Flat) : Pl → F :=
  Sum.elim (fun i => Slice.readL t.keys i.1) (Sum.elim (fun i => Slice.readL t.planes i.1) fun i =>
      Slice.readL t.masks i.1)

def o65Trace (t : Flat) : Trace F := traceOfFlat o65N (readRounds t)

/-- The function at the small lookup: seventeen rows, sparse, in the typed verifier's order. -/
def o65V (t : Flat) : List (SRow Pl F) := vOf o65N (readRounds t)

/-- a sparse row holds at the entries m -/
def SRow.Holds {P K : Type} [CommRing K] (r : SRow P K) (m : P → K) : Prop :=
  (r.cf.map fun pc => pc.2 * m pc.1).sum = r.tg
instance {P K : Type} [CommRing K] [DecidableEq K] (r : SRow P K) (m : P → K) : Decidable
    (r.Holds m) :=
  inferInstanceAs (Decidable (_ = _))

/-- the function at other numbers (for the controls alone) -/
def vAt (N : Nums Pl F) (t : Flat) : List (SRow Pl F) := vOf N (readRounds t)

/-- a form with its target, coefficient by coefficient on the three committed messages -/
structure Claim where
  keys : List F
  planes : List F
  masks : List F
  target : F
  deriving DecidableEq

def spread (r : SRow Pl F) : Claim where
  keys := (List.finRange TwNums.o65S.nKeys).map fun i => dense r.cf (.inl i)
  planes := (List.finRange TwNums.o65S.nPlanes).map fun i => dense r.cf (.inr (.inl i))
  masks := (List.finRange TwNums.o65S.nMasks).map fun i => dense r.cf (.inr (.inr i))
  target := r.tg

def readClaim (c : EndClaim) : Claim :=
  ⟨c.keys.map Slice.readE, c.planes.map Slice.readE, c.masks.map Slice.readE, Slice.readE c.target⟩

/-- the rows in the order of the byte-level verifier's end claims: its claim number reIdx[i] is row
number i: one re-indexing for all transcripts -/
def inPortOrder {α : Type} (l : List α) : List (Option α) :=
  (List.range l.length).map fun c => l[TwNums.o65S.reIdx.idxOf c]?

def claimsAt (N : Nums Pl F) (t : Flat) : List (Option Claim) := inPortOrder ((vAt N t).map spread)
def o65Claims (t : Flat) : List (Option Claim) := claimsAt o65N t

/-- back to machine words, for the evaluation OnBytes.G4.judge: the words below p of an element of
Cb.Gl.E -/
def writeE (x : F) : E :=
  E.mk3 (UInt64.ofNat x.c0.val) (UInt64.ofNat x.c1.val) (UInt64.ofNat x.c2.val)
def writeClaim (c : Claim) : EndClaim :=
  ⟨c.keys.map writeE, c.planes.map writeE, c.masks.map writeE, writeE c.target⟩

def numbersWhere {α : Type} (p : α → Bool) (l : List α) : List ℕ :=
  ((List.range l.length).zip l).filterMap fun x => if p x.2 then some (x.1 + 1) else none

/-- where two lists of claims part: the claim's number (from 1) and which part -/
def partsAt (a b : List (Option Claim)) : List (ℕ × String) :=
  ((List.range a.length).zip (a.zip b)).flatMap fun x =>
    match x.2.1, x.2.2 with
    | some c, some e =>
      (if c.keys == e.keys then [] else [(x.1 + 1, "K")]) ++
          (if c.planes == e.planes then [] else [(x.1 + 1, "P")]) ++
      (if c.masks == e.masks then [] else [(x.1 + 1, "M")]) ++
          (if c.target == e.target then [] else [(x.1 + 1, "T")])
    | _, _ => [(x.1 + 1, "none")]

/-- What is tested at one text. (That no row reads anything but the three messages' entries holds
by the type of a place.) -/
structure Report where
  read : Bool          -- the text is read; names are the plan's
  fits : Bool          -- OnBytes.G4.Flat.fits
  count : ℕ            -- how many rows the function gives
  vsPort : List (ℕ × String)   -- where o65V parts from readE of endClaims
  vsCpp : List (ℕ × String)    -- the same, of the text's own «C» lines
  back : Bool          -- the forms, written in words and read again, are the forms
  verdict : Verdict    -- judge on o65V's forms, in the end claims' numbering
  failing : List ℕ     -- failing on o65V's forms: all that miss their targets
  falseOurs : List ℕ   -- the same, by SRow.Holds on the sparse rows in Cb.Gl.E
  points : Bool        -- the fourteen points are those of OnBytes.G4.points
  deriving Repr, DecidableEq

/-- the tests at plain data t; named: the rounds' names are the plan's; held: the end claims that
come with these data -/
def reportOn (N : Nums Pl F) (t : Flat) (named : Bool) (held : Option (List EndClaim)) : Report :=
  let ours := claimsAt N t
  { read := named
    fits := t.fits Lkp.o65
    count := (vAt N t).length
    vsPort := match endClaims Lkp.o65 t with
      | some l => if l.length == ours.length then partsAt ours (l.map fun c => some (readClaim c))
          else [(0, "length")]
      | none => [(0, "no end claims")]
    vsCpp := match held with
      | some l => if l.length == ours.length then partsAt ours (l.map fun c => some (readClaim c))
          else [(0, "length")]
      | none => [(0, "no claims held")]
    back := (ours.filterMap id).all fun c => readClaim (writeClaim c) == c
    verdict := judge Lkp.o65 ((ours.filterMap id).map writeClaim) t
    failing := failing ((ours.filterMap id).map writeClaim) t
    falseOurs :=
      numbersWhere
        (fun r : Option (SRow Pl F) =>
          match r with | some r => !decide (r.Holds (msgOf t)) | none => true)
        (inPortOrder (vAt N t))
    points :=
      some (pointsOf N (traceOfFlat N (readRounds t))) == (points Lkp.o65 t).map
          (·.map (·.map Slice.readE)) }

def reportAt (N : Nums Pl F) (change : Flat → Flat) (text : String) : Report :=
  match told text with
  | none => ⟨false, false, 0, [], [], false, .unfit, [], [], false⟩
  | some T =>
    match T.flat with
    | none => ⟨false, false, 0, [], [], false, .unfit, [], [], false⟩
    | some t0 => reportOn N (change t0) (T.names == some ((entries Lkp.o65).map (·.name)))
        (T.claims Lkp.o65)

def report (text : String) : Report := reportAt o65N id text

/-- what is expected of a text whose failing claims are these -/
def expected (failing : List ℕ) : Report :=
  ⟨true, true, 17, [], [], true, (failing.head?.map Verdict.fails).getD .holds, failing, failing,
      true⟩

end TwV
