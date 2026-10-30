-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/PlanMemberDefs.lean: A VALUE OF THE TYPE OF WHAT K4's HEARING RETURNS, WRITTEN
DOWN OFF
THE PLAN WITH 0 FOR EVERY ELEMENT, AND THE TEST "the listing front returns at it". Definitions with
code alone; nothing of Mathlib beneath: so that a program can import and run them. Their laws:
Johnson/Road/K4/Total/PlanMember.lean.

  `planOwnAt`, `planOwn P hp g sh`: that value; nothing where the plan names no array of the reads
    or the tables cannot be laid.
  `frontB rows P hp g sh`: **THE TEST.**
**Limits.** Definitions. NOTHING SAYS HERE THAT THE TEST IS TRUE AT ANY PLAN. NO RUN OF IT IS CITED
HERE. Nothing on soundness.


-/
import OnBytes.Desc.First.K4.Claims
import OnBytes.Model.LayerPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt layTables tableAsks)

/-- A value of the skeleton that the plan gives, with 0 for every element. iU3: the number of the
array of the reads. tab: the list of tables. sh: the lookup's shape. -/
def planOwnAt (P : Pub) (hp : HPlan2) (g : Nat) (sh : Forest.Shape) (iU3 : Nat)
    (tab : List TableAt) : Own :=
  { v := { y := P.y, sc := P.sc, g := g, iU3 := iU3,
           K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := #[] }
    H := { fo := { shape := sh, leaves := {} }, PV := #[], ztF := #[], sW := 0, gp := #[]
           wpl := { r := Array.replicate P.rd.muV zeroE }, sPv := 0, omV := #[], tV := {}
           tT := some {} }
    K := { rs := #[], sA0 := 0, sH1 := 0, sB0 := 0, sV := 0, fin := {}, rowS := {} }
    hd := { r := Array.replicate P.rd.muH zeroE }
    hd2 := some { r := Array.replicate P.rd.muH2 zeroE }
    sVE := 0
    wo := {}
    funs := #[] }

/-- The same, its two numbers read off the plan as the hearing reads them. -/
def planOwn (P : Pub) (hp : HPlan2) (g : Nat) (sh : Forest.Shape) : Option Own :=
  (hp.tl.ix.U.getD 2 none).bind fun iU3 =>
    (layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0).map
      fun x => planOwnAt P hp g sh iU3 x.1

/-- **THE TEST: the listing front returns at the plan's value.** -/
def frontB (rows : Bool) (P : Pub) (hp : HPlan2) (g : Nat) (sh : Forest.Shape) : Bool :=
  ((planOwn P hp g sh).bind fun o₀ => front rows P g o₀ {} {}).isSome

end OnBytes.Desc.First.K4.Total
