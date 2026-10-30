-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/SeatsAt.lean: THE SEATS OF THE MEMBERS OF THE LOOKUPS' TWO LISTS, AS TERMS OVER THE PLANNER's SEATS, BY ROLE; AND TEN TESTS A LINK, NINE OF THEM WITH A NEGATIVE TEST (ownOnce has none). Definitions alone: no theorem.
  listAt D l: the link's own oracle messages, all moments (the digits' lookup's list, at the radius 0) · ownAt ps l i: the planner's seat whose role is "own i" in a sending of link l · seatT ps l i: its (tree, tenant); (0, 0) where there is none.
  listCallsAt D l: the kept oracle messages, then the link's own of moment 0 (the calls' lookup's list) · callAt ps D l j: below keptN D l: the seat with seg = (l, 0) and role = .kept b.1 b.2, b := (bornAt D l)[j]; from keptN on: seg = (l, 0) and role = .own (j - keptN) · seatCallsT ps D l j.
  THE TESTS: ownThere · ownShapes · ownSent · ownBelow · ownOnce · callsThere (with zeroFirst · bornFits) · callsShapes · callsSent · callsBelow · callsOnce; seatsOk | seatsCallsOk; controls | controlsCalls: the negative tests, each to be TRUE.
ownSent tests "in N.sent l t for a t of [2, 0, 1]" (the form in which the digits' law spends it) · the two negative tests that move a tenant move it by 1000, OUT of what stands sent (by one, the moved tenant could be another member's: the test on callsSent would be idle).
THE (0, 0) WHERE THERE IS NO SEAT ANSWERS IN SILENCE: ownThere | callsThere, and the tests someB | sentB of Johnson/P5J/Rad3Seat3At.lean, are what guards it.
It reads nothing and writes nothing: the caller hands it values.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.NumbersOf
import Johnson.Desc.First.Look.K3CallerBase
import Johnson.Desc.First.Look.K3CallerAtt

open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.Look

namespace P6T
open P5T

/-- The link's own oracle messages, all moments, at the radius 0. -/
def listAt (D : Sent) (l : Nat) : List (OnBytes.OracleShape × Nat) :=
  sigList D (fun _ => 0) l (lastMoment D l)

/-- Is p the planner's «own i» of link l? -/
def isOwn (l i : Nat) (p : PSeat) : Bool := p.seg.map (·.1) == some l && p.role == .own i

def ownAt (ps : List PSeat) (l i : Nat) : Option PSeat := ps.find? (isOwn l i)

/-- **seatT, off the planner's seats.** -/
def seatT (ps : List PSeat) (l i : Nat) : Nat × Nat := ((ownAt ps l i).map (·.seat)).getD (0, 0)

/-- **arr, off the planner's seats.** -/
def arr (ps : List PSeat) : Nat → Nat → Nat := arrOf ps

/-- (a) -/
def ownThere (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  !(listAt D l).isEmpty &&
    (List.range (listAt D l).length).all fun i => (ownAt ps l i).any (·.smpd)

/-- (b), at a list that is handed in. -/
def ownShapesOf (ps : List PSeat) (l : Nat) (L : List (OnBytes.OracleShape × Nat)) : Bool :=
  L.zipIdx.all fun x => (ownAt ps l x.2).any fun p => p.shape == x.1.1

/-- (b) -/
def ownShapes (ps : List PSeat) (D : Sent) (l : Nat) : Bool := ownShapesOf ps l (listAt D l)

/-- (c) -/
def ownSent (N : Numbers) (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  (List.range (listAt D l).length).all fun i =>
    match ownAt ps l i with
    | some p => [2, 0, 1].any fun t => (N.sent l t).contains p.seat
    | none => false

/-- (d) -/
def ownBelow (ps : List PSeat) (D : Sent) (l base : Nat) : Bool :=
  (List.range (listAt D l).length).all fun i => decide ((seatT ps l i).1 < base)

/-- **The four together.** -/
def seatsOk (N : Numbers) (ps : List PSeat) (D : Sent) (l base : Nat) : Bool :=
  ownThere ps D l && ownShapes ps D l && ownSent N ps D l && ownBelow ps D l base

/-! ## The negative tests -/

/-- The link's «own 0» taken out. -/
def struck (ps : List PSeat) (l : Nat) : List PSeat := ps.filter fun p => !isOwn l 0 p

/-- The tenant of the link's «own 0» moved by 1000: out of what stands sent. -/
def bumped (ps : List PSeat) (l : Nat) : List PSeat :=
  ps.map fun p => if isOwn l 0 p then { p with t := p.t + 1000 } else p

/-- The link's list with one main row more at its first member. -/
def widened (D : Sent) (l : Nat) : List (OnBytes.OracleShape × Nat) :=
  match listAt D l with
  | [] => []
  | x :: L => ({ x.1 with mainRows := x.1.mainRows + 1 }, x.2) :: L

/-- The four negative tests at a link, each to be TRUE (each says that its Bool says no at the fault). At
a link whose list is empty the second, the third and the fourth would say
false: (a) says no there already. -/
def controls (ps : List PSeat) (D : Sent) (l base : Nat) : Bool × Bool × Bool × Bool :=
  (!ownThere (struck ps l) D l,
   !ownShapesOf ps l (widened D l),
   !ownSent (numbersOf ps) (bumped ps l) D l,
   !ownBelow ps D l (base - 1))

/-- For a print: link by link: the list's length, the four Bools, the four controls. base l: the
number of trees in front of the digits' lookup's piece of link l. -/
def lines (ps : List PSeat) (D : Sent) (links : Nat) (base : Nat → Nat) : List String :=
  (List.range links).map fun l =>
    s!"SEATS-AT = link {l} ; members {(listAt D l).length} ; there {ownThere ps D l} ; shapes " ++
      s!"{ownShapes ps D l} ; sent {ownSent (numbersOf ps) ps D l} ; below {ownBelow ps D l (base l)}" ++
      s!" ; controls {controls ps D l (base l)} ; seats " ++
      s!"{(List.range (listAt D l).length).map (seatT ps l)}"

/-! ## The lookup on the link's calls: the kept messages, then the link's own of moment 0 -/

/-- The list of the calls' lookup, at the radius 0 (K3CallerAtt.lean: sigListCalls). -/
def listCallsAt (D : Sent) (l : Nat) : List (OnBytes.OracleShape × Nat) :=
  sigListCalls D (fun _ => 0) l

/-- How many kept messages stand in front. -/
def keptN (D : Sent) (l : Nat) : Nat := (keptAt D l).length

/-- Is p the planner's seat of member j of link l's list? -/
def isCall (D : Sent) (l j : Nat) (p : PSeat) : Bool :=
  p.seg == some (l, 0) &&
    (if j < keptN D l then
      p.role == .kept ((bornAt D l).getD j (0, 0)).1 ((bornAt D l).getD j (0, 0)).2
    else p.role == .own (j - keptN D l))

def callAt (ps : List PSeat) (D : Sent) (l j : Nat) : Option PSeat := ps.find? (isCall D l j)

/-- **seatT at the calls' list, off the planner's seats.** -/
def seatCallsT (ps : List PSeat) (D : Sent) (l j : Nat) : Nat × Nat :=
  ((callAt ps D l j).map (·.seat)).getD (0, 0)

/-- THE MOMENT-0 MESSAGES STAND FIRST IN THE LINK's LIST: else the list's «own» number and the
planner's (the number in the link's WHOLE list) would part. -/
def zeroFirst (D : Sent) (l : Nat) : Bool :=
  (messagesAt D l).zipIdx.all fun x =>
    x.1.moment != 0 || decide (x.2 < (sigList D (fun _ => 0) l 0).length)

/-- As many born entries as kept messages. -/
def bornFits (D : Sent) (l : Nat) : Bool := (bornAt D l).size == keptN D l

/-- (a) -/
def callsThere (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  !(listCallsAt D l).isEmpty && zeroFirst D l && bornFits D l &&
    (List.range (listCallsAt D l).length).all fun j => (callAt ps D l j).any (·.smpd)

/-- (b), at a list that is handed in: THE WHOLE SHAPE, at a kept one too. -/
def callsShapesOf (ps : List PSeat) (D : Sent) (l : Nat) (L : List (OnBytes.OracleShape × Nat)) :
    Bool :=
  L.zipIdx.all fun x => (callAt ps D l x.2).any fun p => p.shape == x.1.1

def callsShapes (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  callsShapesOf ps D l (listCallsAt D l)

/-- (c): in N.sent l 0. -/
def callsSent (N : Numbers) (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  (List.range (listCallsAt D l).length).all fun j =>
    match callAt ps D l j with
    | some p => (N.sent l 0).contains p.seat
    | none => false

/-- (d): base: the trees in front of THE CALLS' LOOKUP's piece of link l. -/
def callsBelow (ps : List PSeat) (D : Sent) (l base : Nat) : Bool :=
  (List.range (listCallsAt D l).length).all fun j => decide ((seatCallsT ps D l j).1 < base)

/-- (e): the seats of one link's list are pairwise distinct. -/
def callsOnce (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  eachOnce ((List.range (listCallsAt D l).length).map (seatCallsT ps D l))

/-- (e) at the digits' list. -/
def ownOnce (ps : List PSeat) (D : Sent) (l : Nat) : Bool :=
  eachOnce ((List.range (listAt D l).length).map (seatT ps l))

/-- **The five together.** -/
def seatsCallsOk (N : Numbers) (ps : List PSeat) (D : Sent) (l base : Nat) : Bool :=
  callsThere ps D l && callsShapes ps D l && callsSent N ps D l && callsBelow ps D l base &&
    callsOnce ps D l

/-- Member 0's seat taken out (at l > 0 the first kept one; at link 0 «own 0»). -/
def struckCalls (ps : List PSeat) (D : Sent) (l : Nat) : List PSeat :=
  ps.filter fun p => !isCall D l 0 p

/-- Member 0's tenant moved by 1000: out of what stands sent. -/
def bumpedCalls (ps : List PSeat) (D : Sent) (l : Nat) : List PSeat :=
  ps.map fun p => if isCall D l 0 p then { p with t := p.t + 1000 } else p

/-- Member 1's seat laid onto member 0's (for (e); where the list has two members). -/
def doubledCalls (ps : List PSeat) (D : Sent) (l : Nat) : List PSeat :=
  ps.map fun p =>
    if isCall D l 1 p then
      { p with j := (seatCallsT ps D l 0).1, t := (seatCallsT ps D l 0).2 }
    else p

def widenedCalls (D : Sent) (l : Nat) : List (OnBytes.OracleShape × Nat) :=
  match listCallsAt D l with
  | [] => []
  | x :: L => ({ x.1 with mainRows := x.1.mainRows + 1 }, x.2) :: L

/-- The five negative tests at a link, each to be TRUE. The fifth is asked where the list has two members;
elsewhere it says true. -/
def controlsCalls (ps : List PSeat) (D : Sent) (l base : Nat) :
    Bool × Bool × Bool × Bool × Bool :=
  (!callsThere (struckCalls ps D l) D l,
   !callsShapesOf ps D l (widenedCalls D l),
   !callsSent (numbersOf ps) (bumpedCalls ps D l) D l,
   !callsBelow ps D l (base - 1),
   decide ((listCallsAt D l).length < 2) || !callsOnce (doubledCalls ps D l) D l)

/-- For a print: link by link. base l: the trees in front of the calls' lookup's piece of link l. -/
def linesCalls (ps : List PSeat) (D : Sent) (links : Nat) (base : Nat → Nat) : List String :=
  (List.range links).map fun l =>
    s!"SEATS-AT-CALLS = link {l} ; kept {keptN D l} ; members {(listCallsAt D l).length} ; there " ++
      s!"{callsThere ps D l} ; shapes {callsShapes ps D l} ; sent " ++
      s!"{callsSent (numbersOf ps) ps D l} ; below {callsBelow ps D l (base l)} ; once " ++
      s!"{callsOnce ps D l} ; controls {controlsCalls ps D l (base l)} ; seats " ++
      s!"{(List.range (listCallsAt D l).length).map (seatCallsT ps D l)}"

end P6T
