-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/PlanRowDefs.lean: A LEAVING OF THE MERGE OF THE CLAIMS ON THE WEIGHTS, WRITTEN
DOWN OFF THE PLAN WITH 0 FOR EVERY ELEMENT, AND THE TEST "wsPending returns at it". Definitions with
code alone; nothing of Mathlib beneath: so that a program can import and run them. Their laws:
Johnson/Road/K4/Total/PlanRow.lean.

  `zeroFac`, `zeroClaim`: a factor of the sizes that a group asks, and a claim on a unit, at zeros.
  `unitsA`, `unitsT`, `unitsW`: A SECOND TEXT: the units' numbers as claimsA, claimsT, weightClaims
    (OnBytes/Model/LayerPanels.lean) list the claims: the same kinds X and layers lam, without the
    factors. Held against the first text, where the first returns, in PlanRow.lean.
  `planEnv`, `unitsOf P g`: the units' numbers off the plan. `planWoOf`, `planWo P g`: the leaving.
  `rowB P g n lin`: **THE TEST.**
**Limits.** Definitions. NOTHING SAYS HERE THAT THE TEST IS TRUE AT ANY PLAN. NO RUN OF IT IS CITED
HERE. Nothing on soundness.


-/
import OnBytes.Model.Layer
import OnBytes.Model.Pending

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub ClaimEnv isAcc callsTS callsAC)
open OnBytes.Params (LinShape)

/-- A factor of the sizes that the group asks, at zeros. -/
def zeroFac (G : WsGrp) : WsFac :=
  if G.cls == 'E' then { HV := Array.replicate G.o zeroE, pt := Array.replicate G.z zeroE }
  else { AV := Array.replicate G.R zeroE }

/-- A claim on unit number ui, at zeros. -/
def zeroClaim (lay : WsLay) (ui : Nat) : WsClaim :=
  { ui := ui, f := (((lay.U[ui]?).map (·.g)).getD []).map zeroFac }

/-- The units of the claims of one segment of a call of the lookup's join. -/
def unitsA (c : ClaimEnv) (sn : String) : Option (List Nat) :=
  let y := c.v.y
  if !isAcc sn then some []
  else
    (List.range (if sn == "LR" then y.LamM else y.Lam)).mapM fun i =>
      let lam := if sn == "LR" then 2 * i + 1 else i
      let mo := c.v.isMoe lam
      let X := if sn == "G" then (if mo then 5 else 3)
        else if sn == "U" then (if mo then 6 else 4)
        else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11
      c.wsLay.unitOf X (c.v.lay lam)

/-- The units of the claims of one segment of a call with terms in the second token sumcheck. -/
def unitsT (c : ClaimEnv) (sn : String) : Option (List Nat) :=
  let y := c.v.y
  let h := y.h
  if sn == "QK" then (List.range y.Lam).mapM fun lam => c.wsLay.unitOf 0 (c.v.lay lam)
  else if h.p3 && (sn == "G" || sn == "U" || sn == "D") then
    (List.range y.LamM).mapM fun lm =>
      c.wsLay.unitOf (if sn == "G" then 7 else if sn == "U" then 8 else 10) (c.v.lay (2 * lm + 1))
  else some []

/-- The units of the panels' weight claims, in their order. -/
def unitsW (c : ClaimEnv) (TS : List Nat) : Option (List Nat) :=
  let y := c.v.y
  let segsOf (q : Nat) : List String := (y.calls.getD q default).segs.map (·.name)
  (((callsAC y).flatMap segsOf).mapM (unitsA c)).bind fun a =>
    ((TS.flatMap segsOf).mapM (unitsT c)).map fun t => a.flatten ++ t.flatten

/-- An environment of claims with the plan's public parts, and nothing else. -/
def planEnv (P : Pub) (g : Nat) : ClaimEnv :=
  { v := { y := P.y, sc := P.sc, g := g, iU3 := 0, K3 := 0, tab := [], zk := #[] }
    wsLay := P.wsLay, rope := #[], rs := #[], rt := #[] }

/-- **The units' numbers of the claims that a hearing hands to the merge**, off the plan. -/
def unitsOf (P : Pub) (g : Nat) : Option (List Nat) :=
  (callsTS P).bind fun TS => (unitsW (planEnv P g) TS).bind fun cp =>
    (if (g == 0) = true then (P.wsLay.unitOf 12 P.y.h.L).map ([·]) else some []).map fun ce =>
      cp ++ ce

/-- A leaving of the merge with these units, at zeros. -/
def planWoOf (lay : WsLay) (uis : List Nat) : WsForkOut :=
  { rm := Array.replicate lay.lk zeroE
    recs := uis.map fun ui => wsRowPart lay (zeroClaim lay ui) zeroE }

/-- The same, its units read off the plan. -/
def planWo (P : Pub) (g : Nat) : Option WsForkOut := (unitsOf P g).map (planWoOf P.wsLay)

/-- **THE TEST: verify-on-bytes's routine wsPending returns at the plan's leaving.** -/
def rowB (P : Pub) (g n : Nat) (lin : LinShape) : Bool :=
  ((planWo P g).bind fun w₀ => (wsPending P.wsLay w₀ n lin).toOption).isSome

end OnBytes.Desc.First.K4.Total
