-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/ToyGuards.lean: the tests on the lookup's honest row at the small
size of Honest/K3/Toy.lean. Tests by evaluation (`#guard` lines) and the few definitions that they
need; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the second writing is Honest/K3/ToyOwn.lean.

What is tested. Part I (part II stands in Honest/K3/ToyFast.lean) tries the harness with the second
writing's row, points and summands: the honest run leaves 0 everywhere, and every alteration that is
tried makes something fail. The comment over each line says what it tests and what would make it
fail. The claims' numbers, in `Left.all`: 0 and 1, the tie's two steps; 2, 3 and 4, the key tree's
levels; 5 and 6, the table side's levels; 7, the bits' sumcheck; 8, the leaves' sumcheck, closed on
the planes; 9, the planes' value at the bits' point; 10, the counts' sum; 11, the key side's last
form.

Limits. Those of Honest/K3/Toy.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Toy
open OnBytes (E addE subE mulE zeroE oneE)
open ProofFile.Honest.SumToy (e sig firsts turn)

/-! ## Letters -/

abbrev W3 : Type := UInt64 × UInt64 × UInt64

/-- Challenges by a formula: round i's sample number k; as many as the chain's own entries say. -/
def drawsBy (f : LFace) (g : Nat → Nat → W3) : List Fmt.Drawn :=
  ((blocks f).flatMap fun b => b.rounds.map (·.entry.drawE)).zipIdx.map fun x =>
    ⟨(List.range x.1).map (g x.2), [], [], none⟩

/-- Three lists of challenges: two in the base field, one with all three coordinates. -/
def h₁ (i k : Nat) : W3 := (11 + 7 * i.toUInt64 + 3 * k.toUInt64, 0, 0)
def h₂ (i k : Nat) : W3 := (5 + 13 * i.toUInt64 + k.toUInt64, 0, 0)
def h₃ (i k : Nat) : W3 :=
  (2 + 3 * i.toUInt64 + k.toUInt64, 1 + i.toUInt64, 4 + 5 * i.toUInt64 + 2 * k.toUInt64)

/-- Two rows of coins. -/
def g₁ (j : Nat) : W3 := (100 + 7 * j.toUInt64, 0, 0)
def g₃ (j : Nat) : W3 := (100 + 7 * j.toUInt64, j.toUInt64 + 1, 2 * j.toUInt64 + 3)

abbrev Row : Type := List (Part Unit Ask Unit)

/-- The second writing's row. Here pts says how the points are read, and off is added to the true
number of rounds in front. -/
def rowOwn (f : LFace) (J : LookJobs Hidden)
    (pts : LFace → Nat → List Fmt.Drawn → Pts := ownPts) (off : Nat := 0) : Row :=
  ownRow { atOf f with base := baseOf f + off } pts J.asked

/-- The lookup's rounds of a played chain. -/
def run (f : LFace) (row : Row) (d : Nat → Made) (g : Nat → W3) (h : Nat → Nat → W3) :
    Option (List Fmt.RoundView) :=
  (playAll f row (askOf d) g (drawsBy f h)).toOption.map (own f)

/-- Played, heard, and the claims evaluated on the played coins and the played data. -/
def left (f : LFace) (row : Row) (d : Nat → Made) (g : Nat → W3) (h : Nat → Nat → W3) :
    Option Left :=
  (run f row d g h).bind fun rs => residues f rs (maskOf g) (askOf d (drawsBy f h))

def J₁ : LookJobs Hidden := ownJobs f₁ rowAt
def J₂ : LookJobs Hidden := ownJobs f₂ rowAt

/-! ## I.1 The honest run -/

-- the chain is played whole: 52 rounds; it would fail at a row that is cut otherwise, a part's
-- count that is not the book's, or a message of another shape than the entry states
#guard (playAll f₁ (rowOwn f₁ J₁) (askOf honest) g₁ (drawsBy f₁ h₁)).toOption.map (·.length) ==
  some 52
-- the verifier's text returns and all twelve claims are 0
#guard (left f₁ (rowOwn f₁ J₁) honest g₁ h₁).map (·.all.length) == some 12
#guard allZero (left f₁ (rowOwn f₁ J₁) honest g₁ h₁)
-- at a second list of challenges (another c too: other keys and counts)
#guard allZero (left f₁ (rowOwn f₁ J₁) honest g₁ h₂)
-- at coins and challenges with all three coordinates
#guard allZero (left f₁ (rowOwn f₁ J₁) honest g₃ h₃)
-- at the coins 0
#guard allZero (left f₁ (rowOwn f₁ J₁) honest (fun _ => (0, 0, 0)) h₁)
-- at the other order of the key tree's rounds
#guard allZero (left f₂ (rowOwn f₂ J₂) honest g₁ h₁)
#guard allZero (left f₂ (rowOwn f₂ J₂) honest g₃ h₃)
-- the order matters: the summands of one order under the verifier's text at the other: some claim
-- fails, and none but the key tree's (2 3 4) and the key side's last form (11)
#guard someNot (left f₂ (rowOwn f₂ J₁) honest g₁ h₁)
#guard (notZero (left f₂ (rowOwn f₂ J₁) honest g₁ h₁)).any (·.all [2, 3, 4, 11].contains)

/-! ## I.2 The alterations -/

-- the filling that says nothing: shapes alone: the text still returns; claims are not 0
#guard someNot (left f₁ (rowOwn f₁ noJobs) honest g₁ h₁)

/-- A key that is no row of the table, at place 0. -/
def badKey (c : Nat) : Made :=
  { honest c with keys := (fun th => addE (rowAt th 0) (e 1)) :: (honest c).keys.drop 1 }
/-- A count off by one: row 1's lowest bit altered from what it is. -/
def badCount (c : Nat) : Made :=
  { honest c with bit := fun u j =>
      if u == 1 && j == 0 then subE oneE ((honest c).bit u j) else (honest c).bit u j }
/-- A bit that is 2. -/
def badBit (c : Nat) : Made :=
  { honest c with bit := fun u j => if u == 2 && j == 1 then e 2 else (honest c).bit u j }

-- a key outside the table: the tie's first step alone
#guard notZero (left f₁ (rowOwn f₁ J₁) badKey g₁ h₁) == some [0]
-- a false count: the tie's first step and the counts' sum
#guard notZero (left f₁ (rowOwn f₁ J₁) badCount g₁ h₁) == some [0, 10]
-- a bit that is 2: these two and the bits' sumcheck
#guard notZero (left f₁ (rowOwn f₁ J₁) badBit g₁ h₁) == some [0, 7, 10]

-- one coin changed by one, in the evaluation, each of the 73 in turn: some claim is not 0
#guard (run f₁ (rowOwn f₁ J₁) honest g₁ h₁).any fun rs => (List.range f₁.slots).all fun j =>
  someNot (residues f₁ rs (maskOf fun i => if i == first + j then ((g₁ i).1 + 1, 0, 0) else g₁ i)
    (askOf honest (drawsBy f₁ h₁)))
-- what is sent moves with each of the 73
#guard (List.range f₁.slots).all fun j => sig (run f₁ (rowOwn f₁ J₁) honest g₁ h₁) !=
  sig (run f₁ (rowOwn f₁ J₁) honest (fun i => if i == first + j then ((g₁ i).1 + 1, 0, 0) else g₁ i)
    h₁)
-- the owner's other coins (four in front, three behind) are not read
#guard sig (run f₁ (rowOwn f₁ J₁) honest g₁ h₁) == sig (run f₁ (rowOwn f₁ J₁) honest
  (fun i => if first ≤ i && i < first + f₁.slots then g₁ i else (0, 0, 0)) h₁)

-- one sent scalar changed by one, each of the 73 in turn: some claim is not 0
#guard (run f₁ (rowOwn f₁ J₁) honest g₁ h₁).any fun rs =>
  (rs.map (·.vals.length)).sum == f₁.slots &&
  rs.zipIdx.all fun r => (List.range r.1.vals.length).all fun j =>
    someNot (residues f₁ (turn rs r.2 j) (maskOf g₁) (askOf honest (drawsBy f₁ h₁)))

-- a wrong number of rounds in front: one more (one fewer is not tried)
#guard someNot (left f₁ (rowOwn f₁ J₁ ownPts 1) honest g₁ h₁)

-- a point that is not reversed: that of "JOIN"; that of "ZERO"
#guard someNot (left f₁ (rowOwn f₁ J₁ fun f b l =>
  { ownPts f b l with rhoT := (ownPts f b l).rhoT.reverse
                      tabPt := fun k => if k == 0 then (ownPts f b l).rhoT.reverse
                                        else (ownPts f b l).tabPt k }) honest g₁ h₁)
#guard someNot (left f₁ (rowOwn f₁ J₁ fun f b l =>
  { ownPts f b l with zeroPt := (ownPts f b l).zeroPt.reverse }) honest g₁ h₁)

-- the data follow the challenge in front: read on the data of another c, claims fail
#guard (run f₁ (rowOwn f₁ J₁) honest g₁ h₁).any fun rs =>
  someNot (residues f₁ rs (maskOf g₁) (honest 0).hidden) &&
    allZero (residues f₁ rs (maskOf g₁) (honest 11).hidden)

-- the verifier's own rejections: the sample 0 for Y (round 3 of the lookup is the first tie step's
-- "PSC Y"): the chain is played, and it is the text that returns nothing; a round too few
#guard (run f₁ (rowOwn f₁ J₁) honest g₁ fun i k => if i == 2 + 3 then (0, 0, 0) else h₁ i k).isSome
#guard (left f₁ (rowOwn f₁ J₁) honest g₁ fun i k => if i == 2 + 3 then (0, 0, 0) else h₁ i k).isNone
#guard (run f₁ (rowOwn f₁ J₁) honest g₁ h₁).any fun rs =>
  (residues f₁ rs.dropLast (maskOf g₁) (honest 11).hidden).isNone

-- the frame's own rejections: a row with a part too few; the first two parts as one (the same
-- rounds, cut otherwise than the book cuts)
#guard (playAll f₁ (rowOwn f₁ J₁).dropLast (askOf honest) g₁ (drawsBy f₁ h₁)).toOption.isNone
#guard (match rowOwn f₁ J₁ with
  | p :: q :: l => (playAll f₁ (p.andThen q :: l) (askOf honest) g₁ (drawsBy f₁ h₁)).toOption.isNone
  | _ => false)

end ProofFile.Honest.K3.Toy
