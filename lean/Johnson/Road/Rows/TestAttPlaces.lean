-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/TestAttPlaces.lean: the dictionary between the names of the late entries of an
attention sub-proof and the entries of the verifier's vector of tables, tried at the small
configuration.

The tests run when this file is compiled. The program does not import this file.

What is tried, with the verifier's own list of tables at the small configuration (64 tokens; the
record heard of Johnson/Road/Rows/TestAttKit14.lean). names S T lists the names that the
library-side forms read in the table T: those that the premises Good8, LinGood and so on call good
(Cb/Pv/Att/End/FirstOut.lean, Lin.lean, LastOut.lean).
 - Every name's place (placeAtt) lies within its table: it is below the length that the verifier has
   stored for the table.
 - Within a table, different names have different places.
 - The 21 tables do not overlap, and all end within the vector.
 - The units of the scores stand in the order that tabOfAtt takes: below the diagonal, then on it.
So at this configuration the map from good names to entries of the vector is one-to-one.
 - For the tables that are read whole, there are as many names as the table has entries.

The teeth. With the places of the tables on single features in the place of those on blocks of
features, a place falls outside its table or two names meet.

What is not tested. One configuration. That the entry at a name's place holds what the name says:
that is what the tables' truth says (Johnson/Road/Rows/AttRead.lean), and the end values' statements
are proved from it.


-/
import Johnson.Road.Rows.AttPlaces
import Johnson.Road.Rows.TestAttKit14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows.TestPlaces

open OnBytes.Attention (Heard Shape Seg)
open Inst.Model.AttSeg (Raw Reg)
open Cb.Pv.Att.End (AttTab)
open TestEnds14 (heard)

/-- All tables' names. -/
def allTabs : List AttTab :=
  [.tA, .tVM, .tVD, .tMm, .tQm, .tKm, .tMd, .tQd, .tKd, .hW, .hX, .hE, .hT, .hPi, .hR2, .tO, .qO,
    .qVM, .qVD, .qF, .qKx]

/-- The lists of all pairs, triples and quadruples of numbers below given bounds. -/
def two (a b : Nat) : List (Nat × Nat) :=
  (List.range a).flatMap fun x => (List.range b).map fun y => (x, y)
def three (a b c : Nat) : List (Nat × Nat × Nat) :=
  (List.range a).flatMap fun x => (two b c).map fun y => (x, y)
def four (a b c d : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range a).flatMap fun x => (three b c d).map fun y => (x, y)

/-- The names of the first cells of the entries of a region's planes. -/
def colNames (S : Shape) (reg : Reg) (nb : Nat) : List Raw :=
  (three 5 S.NP (2 ^ (nb - S.cf.lmS))).map fun x => .c reg x.1 x.2.1 (0 + x.2.2 * 2 ^ S.cf.lmS)

/-- The names of the first cells of the entries for a number in n limbs, a pair and a head. -/
def rowNames (S : Shape) (n : Nat) (mk : Nat → Nat → Nat → Raw) : List Raw :=
  (three n S.NP (2 ^ S.cf.lgk)).map fun x => mk x.1 x.2.1 x.2.2

/-- The names of the first cells of the entries for a tensor in n limbs. cnt: pairs, or layers. -/
def longNames (S : Shape) (n cnt : Nat) (mk : Nat → Nat → Nat → Nat → Raw) : List Raw :=
  (four n cnt (2 ^ S.cf.lgk) (2 ^ (S.cf.ldh - S.ls))).map fun x =>
    mk x.1 x.2.1 x.2.2.1 (0 + x.2.2.2 * 2 ^ S.ls)

/-- The names that the library-side forms read in a table. -/
def names (S : Shape) : AttTab → List Raw
  | .tA => colNames S .M S.nM ++ colNames S .D S.nD
  | .tVM => colNames S .M S.nM
  | .tVD => colNames S .D S.nD
  | .tMm => rowNames S 4 fun k b g => .mx k b g 0
  | .tMd => rowNames S 4 fun k b g => .mx k b g 0
  | .hT => rowNames S 4 fun k b g => .mx k b g 0
  | .hW => rowNames S 4 fun k b g => .den k b g 0
  | .hE => rowNames S 4 fun k b g => .den k b g 0
  | .hX => rowNames S S.cf.lt fun k b g => .ib k b g 0
  | .hPi => rowNames S S.cf.lt fun k b g => .ib k b g 0
  | .hR2 => rowNames S S.cf.lt fun k b g => .ib k b g 0
  | .tO => longNames S 1 S.NP (fun _ b g n => .qh b g 0 n) ++
      longNames S 1 S.NP fun _ b g n => .qh' b g 0 n
  | .qO => longNames S 2 S.NP fun k b g n => .out k b g 0 n
  | .tQm => longNames S 2 S.NP fun k b g n => .qry k b g 0 n
  | .tQd => longNames S 2 S.NP fun k b g n => .qry k b g 0 n
  | .qF => longNames S 2 S.NP fun k b g n => .qry k b g 0 n
  | .tKm => longNames S 2 S.Lam fun k lam g n => .key k lam g 0 n
  | .tKd => longNames S 2 S.Lam fun k lam g n => .key k lam g 0 n
  | .qKx => longNames S 2 S.Lam fun k lam g n => .key k lam g 0 n
  | .qVM => longNames S 2 S.Lam fun k lam g n => .val k lam g 0 n
  | .qVD => longNames S 2 S.Lam fun k lam g n => .val k lam g 0 n

/-- The length that the verifier has stored for a table. -/
def lenOf (h : Heard) (T : AttTab) : Nat := (h.t.tabLen.lookup (tabOfAtt h T)).getD 0

/-- No number occurs twice in a list of numbers below n. -/
def distinct (n : Nat) (l : List Nat) : Bool :=
  (l.foldl (fun (st : Array Bool × Bool) i =>
    (st.1.setIfInBounds i true, st.2 && !(st.1.getD i true))) (Array.replicate n false, true)).2

/-- The places of a table's names, under a given function of places. -/
def placesOf (h : Heard) (pl : AttTab → Raw → Nat) (T : AttTab) : List Nat :=
  (names h.S T).map (pl T)

/-- All places of a table's names lie within the table and no two are the same. -/
def tableFine (h : Heard) (pl : AttTab → Raw → Nat) (T : AttTab) : Bool :=
  distinct (lenOf h T) (placesOf h pl T)

-- every table has names and a length
#guard (heard.map fun h => allTabs.all fun T => 0 < lenOf h T && 0 < (names h.S T).length) ==
  some true
-- within its table; different names, different places
#guard (heard.map fun h => allTabs.all (tableFine h (placeAtt h.S))) == some true
-- the tables do not overlap, and end within the vector
#guard (heard.map fun h => distinct h.S.tableElems
    (allTabs.flatMap fun T => (List.range (lenOf h T)).map fun i => tabOfAtt h T + i)) == some true
-- the order of the units
#guard (heard.map fun h => h.scores.toList.map (·.seg)) == some [Seg.fm, Seg.fd]
-- the tables that are read whole
#guard (heard.map fun h => [AttTab.tA, .tO].all fun T => (names h.S T).length == lenOf h T) ==
  some true
-- how many names; how long the tables are
#guard (heard.map fun h => allTabs.map fun T => (names h.S T).length) ==
  heard.map fun h => allTabs.map fun T =>
    match T with
    | .tVM => lenOf h T * 2 / 3
    | .tVD => lenOf h T / 3
    | .tA => lenOf h T
    | .tO => lenOf h T
    | _ => (names h.S T).length
-- a tooth: the places of another kind of table
#guard (heard.map fun h => tableFine h (fun _ => placeRow h.S) .qF) == some false
#guard (heard.map fun h => tableFine h (fun _ => placeLong h.S) .hT) == some false
#guard (heard.map fun h => tableFine h (fun _ => placeCol h.S) .qKx) == some false

end OnBytes.Road.Rows.TestPlaces
