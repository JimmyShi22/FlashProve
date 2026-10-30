-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SentFit.lean: code switching: A TEST WITH CODE ON THE LIST OF ROUNDS AND THE
TABLE OF JOINTS' NUMBERS: the tenants (tree, part) that the program's layout gives the notices of a
switch's sending, all but the last, are as a set N.sent m 0. DEFINITIONS ALONE: A LIGHT FILE, so
that the test can be evaluated without the laws that spend it (K2C/SentAtPlan.lean). It imports the
table of joints (Johnson/Desc/First/Borders.lean) and the places' numbers off the list of rounds
(Johnson/Desc/ProofFile/Lot/K2OfPlan.lean), and nothing else. NO SUB-PROTOCOL IMPORTS THIS FILE.
  sentFitB N m pIn codes sent   the test at one switch. No layout: false
  sentFitOn spots N P ps        the test at a list of switches (group · the place's link · the
                                place's number in the flat list ps), at the numbers that numsAt
                                gives. No numbers at a place: false
  switchSpots · sentFitAll      the 25 switches of a request with 25 links; the test at these
LIMITS. THE TEST HAS BEEN EVALUATED AT NO LIST OF ROUNDS. It compares sets of tenants and asks
nothing on OOD samples. No soundness is claimed.
-/
import Johnson.Desc.First.Borders
import Johnson.Desc.ProofFile.Lot.K2OfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes
open VerifiableInference.Desc (Place)

/-- **The test.** codes, sent: the codes and the notices of the switch's sending, off the list of
rounds. pIn: the place of the switch's sub-protocol. m: the group into which the switch leads. -/
def sentFitB (N : Numbers) (m : Nat) (pIn : Option Place) (codes : Codes)
    (sent : Array OracleNotice) : Bool :=
  match layTrees codes sent with
  | none => false
  | some lay => sameMembers ((List.range (sent.size - 1)).map fun i =>
      (N.treesAt pIn + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0)

/-- **The test at a list of switches**, at the numbers that numsAt gives. spots: the group, the
place's link, and the place's number in the flat list. No numbers at a place: false. -/
def sentFitOn (spots : List (Nat × Option Nat × Nat)) (N : Numbers) (P : P1K2.Prep)
    (ps : List Place) : Bool :=
  spots.all fun t =>
    match P1K2.numsAt P t.2.1 with
    | none => false
    | some n => sentFitB N t.1 ps[t.2.2]? n.codes n.sent

/-- The 25 switches of a request with 25 links: the group, the place's link, and the number of the
place in the flat list: 14 l + 2 at the links 1 … 23, 339 at link 24, 353 at the finish. -/
def switchSpots : List (Nat × Option Nat × Nat) :=
  ((List.range 23).map fun i => (i + 1, some (i + 1), 14 * (i + 1) + 2)) ++
    [(24, some 24, 339), (25, none, 353)]

/-- **The test at all 25.** -/
def sentFitAll (N : Numbers) (P : P1K2.Prep) (ps : List Place) : Bool :=
  sentFitOn switchSpots N P ps

end VerifiableInference.Desc.First.K2
