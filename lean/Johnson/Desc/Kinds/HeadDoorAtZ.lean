-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadDoorAtZ.lean: the two public tests of Johnson/Desc/Kinds/HeadDoorRows.lean AS
FUNCTIONS OF Z ALONE: the five further arguments are computed from Z by the definitions in
Johnson/P5T/. Definitions with code only.

Main names.
  arrFast ps, numFast ps   P5T.arrOf ps and P5T.numOfPlan ps, with the list of keys computed once
          and not at every call.
  memsOf ps     of every entry of ps with a sample: its shape and its (tree, tenant).
  lettersAt Z   the five arguments. ps1 := P5T.planSeats Z Z.D.1 lists the oracle messages of the
          request's own rounds; psAll := P5T.planSeatsAll Z Z.D those of all three Fiat-Shamir hash
          chains. arr and num: at psAll. group and sent0: of P5T.numbersOf ps1. mems: memsOf ps1.
  planK6AtZ Z, padsAtZ Z   THE TWO TESTS.

What it imports beyond what lawsAsk's own file imports: our four light files and P5T/PlanSeats,
NumbersOf, NumOfPlan (1, 6 and 2 new modules, none of Mathlib).
Not claimed here. No theorem. What acceptance implies: Law/HeadDoorAtZLaw.lean. The full size only.
Nothing on soundness.

-/
import Johnson.Desc.Kinds.HeadDoorRows
import Johnson.P5T.NumbersOf
import Johnson.P5T.NumOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open P5T (PSeat keyOf planSeats planSeatsAll numbersOf)

/-- P5T.arrOf ps, with the list of keys computed once. -/
def arrFast (ps : List PSeat) : Nat → Nat → Nat :=
  let keys := (ps.map keyOf).eraseDups
  fun j t =>
    match ps.find? fun p => p.j == j && p.t == t with
    | some p => keys.idxOf (keyOf p)
    | none => keys.length

/-- P5T.numOfPlan ps, with the list of keys computed once. -/
def numFast (ps : List PSeat) : Nat → Nat → Nat :=
  let keys := (ps.map keyOf).eraseDups
  fun l k => keys.idxOf (0, l, k)

/-- Of every entry with a sample: its shape and its (tree, tenant). -/
def memsOf (ps : List PSeat) : List (OnBytes.OracleShape × (Nat × Nat)) :=
  (ps.filter (·.smpd)).map fun p => (p.shape, p.seat)

/-- The five arguments, computed from Z. -/
def lettersAt (Z : ProofFile.Pub) : DoorLetters :=
  { arr := arrFast (planSeatsAll Z Z.D)
    num := numFast (planSeatsAll Z Z.D)
    group := (numbersOf (planSeats Z Z.D.1)).group
    sent0 := (numbersOf (planSeats Z Z.D.1)).sent 24 0
    mems := memsOf (planSeats Z Z.D.1) }

/-- **The first test, as a function of Z alone.** -/
def planK6AtZ (Z : ProofFile.Pub) : Bool := planK6Row Z (lettersAt Z)

/-- **The second test, as a function of Z alone.** -/
def padsAtZ (Z : ProofFile.Pub) : Bool := padsRow Z (lettersAt Z)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
