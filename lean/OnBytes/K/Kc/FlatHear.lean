-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/FlatHear.lean: the whole receiving side of the check of the output head's sub-proof,
with the lookup of a sub-proof's calls, as functions on plain data.

OnBytes/K/Kc/Flat.lean says what "on plain data" means here and why: a function of the type `Fl`
takes the ledger of the sub-proof's slots and the rounds as lists of field elements, and returns
nothing, or a value with the new ledger and the rounds that are left. This file goes on with
 - the lookup's messages: `lkDraws`, `lkTieStep`, `lkTie`, `lkLevel`, `lkPad`, the counterparts of
   `Model.Forest.draws`, `tieStep`, `tie`, `level`, `pad` (OnBytes/Model/Look.lean). The checks of
   the layers' sub-proofs call the same routine;
 - the two routines of the head that test a value: `flatReplyToken` (the form of the reply's token)
   and `flatMergedPoint` (every call's key point ends in the same coordinates), the counterparts of
   `Model.Head.replyToken` and `mergedPoint`;
 - `flatHear`: all messages of the head's sub-proof from just after the link's first message up to
   the commitment to its reads, the counterpart of `Model.Head.hear`
   (OnBytes/Model/HeadHeard.lean).
The texts are the program's, line for line. Left out: the names of refusals, and the twelve calls
of `Model.Head.noteH`, which keep an intermediate value for a comparison with another verifier (its
own comment: no test reads it).

What `flatHear` tests of values: the two tests named above, and nothing else. Every sumcheck leaves
one linear claim, kept in the result.

Main definitions: `Fl.roundsIn`, `lkPad`, `flatReplyToken`, `flatMergedPoint`, `flatHear`.

Not claimed. This file holds no theorem; OnBytes/K/Kc/HearProved.lean has the
laws. What the head of OnBytes/K/Kc/Flat.lean says that a flat function does not see holds here too.
Nothing on soundness.
The program does not import this file.

-/
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork Aff Psc Tsc Level RoundForm)

/-- The slot of the next scalar that is sent. -/
def Fl.slot : Fl Nat := Fl.ask fun F => some F.next

/-- Enters a claim in the list of owed claims. Returns its number. -/
def Fl.owe (what : String) : Fl Nat := Fl.take fun F => some (F.owe what)

/-- Sets up n slots, none of them filled. -/
def Fl.slots (n : Nat) : Fl Unit := Fl.change fun F => some (F.slots n)

/-- Rounds of one form in a row. Returns the challenges in the order of the rounds. -/
def Fl.roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) : Fl (Array E × Psc) :=
  zs.foldlM
    (fun (s : Array E × Psc) z => do
      let (r, q) ← Fl.roundIn form s.2 z.1 z.2
      pure (s.1.push r, q))
    (#[], p)

/-! ## The lookup of a sub-proof's calls -/

section Lookup

open OnBytes.Model (eqTab orderDefault Call)
open OnBytes.Model.Forest (Shape Heard Tie TieStep Descent padKeyOf shape pubAsk elems lins tableAt
  joinedTableAt callWeight orderForestRange)

/-- The shift, if the group has several calls, then alpha. Returns them with the public factor. -/
def lkDraws (h : Shape) : Fl (E × E × E) := do
  let theta ← if h.NC > 1 then Fl.answer .lkpShift else pure zeroE
  let alpha ← Fl.answer .lkp
  let a := (List.range h.NT).foldl
    (fun a y =>
      mulE a (powE (subE alpha (padKeyOf h theta (h.callOf.getD y 0))) (h.pub.getD y 0)))
    (powE (subE alpha (padKeyOf h theta 0)) h.emptyKeys)
  pure (theta, alpha, a)

/-- Step j of the tie of the two sides' roots: a sumcheck without a variable. -/
def lkTieStep (a : E) (s : TieStep) (j : Nat) : Fl TieStep := do
  let p ← Fl.pscBegin (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP)
  let (first, p) ← Fl.pscEnds p 3 (if j = 0 then 3 else 2)
  let sZ := if j = 0 then first else s.sZ
  let sP := if j = 0 then first + 1 else first
  let vP ← Fl.shown sP
  let vG ← Fl.shown (sP + 1)
  let power := mulE (mulE vP vP) vG
  let summand ← if j = 0 then do pure (subE (← Fl.shown sZ) (mulE a power)) else pure power
  let (row, _) ← Fl.pscRow p summand
  pure { rows := s.rows.push row, sZ := sZ, sP := sP, sG := s.sG.push (sP + 1) }

/-- The tie, and the point that joins the roots of the planes. -/
def lkTie (a : E) : Fl Tie := do
  let s ← (List.range 31).foldlM (lkTieStep a) {}
  let sG := s.sG.push s.sP
  let rhoT := (← Fl.point .lkpPlanes 5).reverse
  let ej := eqTab rhoT
  let cT := (List.range 32).foldl
    (fun (f : Aff) j => Aff.addMul f (Aff.slot (sG.getD j 0)) (ej.getD j zeroE))
    (Aff.ofConst zeroE)
  pure { rows := s.rows, sZ := s.sZ, rhoT := rhoT, cT := cT }

/-- One level of a product tree with mu variables, bound in the given order. -/
def lkLevel (s : Descent) (mu : Nat) (order : List Nat) : Fl Descent := do
  let o ← Fl.levelIn mu s.rho s.form order
  let (rho, form) := o.handDown
  pure { rows := s.rows.push o.row, rho := rho, form := form }

/-- The messages of the lookup. -/
def lkPad (calls : Array Call) (pub : Array Nat) (lid : Nat) : Fl Heard := do
  let h0 ← Fl.need (shape calls lid).toOption
  Fl.must (pubAsk h0 pub).toBool
  let h : Shape := { h0 with pub := pub }
  let v := h.v
  let d := h.d
  let m := 5 + d
  let slot0 ← Fl.slot
  let owedObjects ← Fl.owe "look-up-mask-claims"
  let owedPlanes ← Fl.owe "look-up-plane-claims"
  let owedJoin ← Fl.owe "look-up-join"
  let (theta, alpha, a) ← lkDraws h
  let t ← lkTie a
  let keys ← (List.range v).foldlM
    (fun (s : Descent) mu =>
      lkLevel s mu (if mu + 1 = v then orderForestRange mu h.rK else orderDefault mu))
    { rows := t.rows, rho := #[], form := Aff.slot t.sZ }
  let zx := keys.rho.extract 0 h.dT
  let zy := keys.rho.extract h.dT keys.rho.size
  let table ← (List.range d).foldlM
    (fun (s : Descent) l => lkLevel s (5 + l) (orderDefault (5 + l)))
    { rows := keys.rows, rho := t.rhoT, form := t.cT }
  Fl.must (table.rho.size == m)
  let leaves ← Fl.pscBegin table.form
  let (zb0, leaves) ← Fl.roundsIn .eq leaves
    ((List.range m).map fun j => (table.rho.getD j zeroE, if j < d then 2 else 1))
  let r5 := (← Fl.point .zero m).reverse
  let bits ← Fl.pscBegin (Aff.ofConst zeroE)
  let (zb1, bits) ← Fl.roundsIn .eq2 bits (r5.toList.map fun z => (z, 0))
  let (sBit, bits) ← Fl.pscEnds bits 2 1
  let vBit ← Fl.shown sBit
  let (bitsRow, _) ← Fl.pscRow bits (subE (mulE vBit vBit) vBit)
  let rows := table.rows.push bitsRow
  Fl.must ((← Fl.slot) == slot0 + elems h && rows.size == lins h)
  Fl.must (h.iota.all fun i => decide (i ≤ h.rK))
  let zk := (Array.range h.NC).map fun c => zy.extract (h.rK - h.iota.getD c 0) zy.size ++ zx
  Fl.must ((List.range h.NC).all fun c =>
    (zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0)
  let tT := h.calls.map fun k => tableAt k (zb0.extract (h.kT - k.k) h.kT)
  let row := joinedTableAt h theta tT (zb0.extract h.kT (h.kT + h.cK))
  pure {
    shape := h, theta := theta, alpha := alpha, a := a, rows := rows, leaves := leaves,
    leavesA := subE (subE alpha oneE) row, sBit := sBit, zx := zx, zy := zy,
    e := (Array.range h.NC).map (callWeight h zy), cEnd := keys.form, zb0 := zb0, zb1 := zb1,
    tT := tT, zk := zk, owedObjects := owedObjects, owedPlanes := owedPlanes,
    owedJoin := owedJoin }

end Lookup

/-! ## The head -/

section Head

open OnBytes.Model (lastOf)
open OnBytes.Model.Head (Shape HL HPlanH2 Covered Heard winOf callNo ztOf)

/-- The reply's token: its form is tested. -/
def flatReplyToken (plain : Array E) (V : Nat) : Fl Nat := do
  Fl.must (plain.size == 1)
  let y := plain.getD 0 zeroE
  Fl.must (y.c1 == 0 && y.c2 == 0 && decide (y.c0.toNat < V))
  pure y.c0.toNat

/-- The last la coordinates of the lookup's point; every call's key point must end in them. -/
def flatMergedPoint (h : Shape) (g1 : Model.Forest.Heard) : Fl (Array E) := do
  let Zl ← Fl.need (lastOf g1.zx h.la).toOption
  Fl.must (g1.zk.all fun zk => zk.extract (zk.size - h.la) zk.size == Zl)
  pure Zl

/-- All messages of the sub-proof up to the commitment to its reads. plain: the plain scalars of the
link's first message. -/
def flatHear (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (plain : Array E) : Fl Heard := do
  let yTok ← flatReplyToken plain h.V
  Fl.slots hp.ns
  let g1 ← lkPad L.cl L.fs.pub h.LIDB
  let Zl ← flatMergedPoint h g1
  let PV ← Fl.point .zero h.lt
  let (sW, gp, wpl) ← flatSquares h.XL h.lPd h.lt PV
  let (sPv, omV, tV) ← flatProducts h.XL h.lt PV
  let qN ← Fl.need (callNo L "NF")
  let qH ← Fl.need (callNo L "HD0")
  let tN ← flatStream h.lt (ztOf h L g1 qN)
  let (tH, rs) ← flatLogits h.lt hp.lamS (ztOf h L g1 qH)
  pure { win := winOf cov h.T yTok, g1 := g1, Zl := Zl, PV := PV, sW := sW, gp := gp, wpl := wpl,
         sPv := sPv, omV := omV, tV := tV, tN := tN, tH := tH, rs := rs, qN := qN, qH := qH }

end Head

end OnBytes.K.Kc
