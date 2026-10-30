-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadDoorBy.lean: the five arguments of the two cheap public tests planK6AtZ and
padsAtZ (Johnson/Desc/Kinds/HeadDoorAtZ.lean: lettersAt Z), AS A FUNCTION OF THREE PLAIN VALUES: the
proof file's three lists of sendings, the request's shape, and a short table of counts of roots.
Definitions with code. No Mathlib.

Why. lettersAt Z reads of Z its three lists of sendings (Z.made.proof), the request's shape
(Z.first.shape) and, of the three lists of declared rounds Z.D, ONLY how many roots stand in front
of the round of each sending, and two totals. Written so, the arguments can be evaluated at written
values by Lean's kernel.

  RootsV             the table: for each sending of each of the three chains the number of roots in
          front of its round; the first two chains' totals.
  rootsOf m D        that table, read off the declared rounds D at the sendings m.
  seatsBy, chainSeatsBy, seatsAllBy   P5T.planSeats, chainSeats, planSeatsAll
          (Johnson/P5T/PlanSeats.lean), with the table in the declared rounds' place.
  lettersBy m S R    lettersAt's five arguments, of these.
That they are lettersAt Z's: Johnson/Desc/Kinds/Law/HeadDoorByLaw.lean.

-/
import Johnson.Desc.Kinds.HeadDoorAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open P5T (PSeat rootsBefore rolesOf segOf numbersOf)
open Johnson.G (ChainSends)

/-- For each sending of each chain: the roots in front of its round; two chains' totals. -/
structure RootsV where
  r1 : List Nat
  r2 : List Nat
  r3 : List Nat
  t1 : Nat
  t2 : Nat
  deriving DecidableEq, Repr

/-- The table, read off the declared rounds. -/
def rootsOf (m : ChainSends × ChainSends × ChainSends)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) : RootsV :=
  { r1 := m.1.sends.map fun s => rootsBefore D.1 (s.entry - 1)
    r2 := m.2.1.sends.map fun s => rootsBefore D.2.1 (s.entry - 1)
    r3 := m.2.2.sends.map fun s => rootsBefore D.2.2 (s.entry - 1)
    t1 := rootsBefore D.1 D.1.length
    t2 := rootsBefore D.2.1 D.2.1.length }

/-- P5T.planSeats, of the first chain's sendings, the request's shape and the table's first list. -/
def seatsBy (c : ChainSends) (S : OnBytes.Params.ReqShape) (rbs : List Nat) : List PSeat :=
  let groups := (OnBytes.reqGroups S).toList
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      let seg := segOf (groups.length + 1) 16 s.1.label
      let roles := match seg with
        | some (l, m) => rolesOf S groups l m
        | none => []
      (List.range s.1.sent.length).map fun i =>
        { label := s.1.label, send := s.2, seg := seg, idx := i,
          j := rbs.getD s.2 0 + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := roles.getD i .other }

/-- P5T.chainSeats, likewise. -/
def chainSeatsBy (chain base : Nat) (c : ChainSends) (rbs : List Nat) : List PSeat :=
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      (List.range s.1.sent.length).map fun i =>
        { label := s!"chain {chain}, {s.1.label}", send := 1000 * chain + s.2, seg := none,
          idx := i,
          j := base + rbs.getD s.2 0 + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := .other }

/-- P5T.planSeatsAll, likewise. -/
def seatsAllBy (m : ChainSends × ChainSends × ChainSends) (S : OnBytes.Params.ReqShape)
    (R : RootsV) : List PSeat :=
  seatsBy m.1 S R.r1 ++ chainSeatsBy 1 R.t1 m.2.1 R.r2 ++ chainSeatsBy 2 (R.t1 + R.t2) m.2.2 R.r3

/-- lettersAt's five arguments. -/
def lettersBy (m : ChainSends × ChainSends × ChainSends) (S : OnBytes.Params.ReqShape)
    (R : RootsV) : DoorLetters :=
  { arr := arrFast (seatsAllBy m S R)
    num := numFast (seatsAllBy m S R)
    group := (numbersOf (seatsBy m.1 S R.r1)).group
    sent0 := (numbersOf (seatsBy m.1 S R.r1)).sent 24 0
    mems := memsOf (seatsBy m.1 S R.r1) }

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
