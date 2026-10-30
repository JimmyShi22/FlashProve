-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeadHeard.lean: THE SHAPE OF WHAT THE OUTPUT HEAD's OWN ROUNDS HEARD: what
is left of Model.Head.Heard (OnBytes/Model/HeadHeard.lean) when every field element and every token
is left out. One structure, its maker, and two equations by rfl. HeadPart.lean's HeadSh holds it
whole (its field x).
  `HeadHeardSh` of Head.Heard, a field a field, under its own name: of the arrays of field elements
    Zl, PV, gp, omV, rs their sizes; of win (the tokens that are checked) its size alone; sW, sPv
    (slots' numbers) and qN, qH (calls' numbers) as they stand; wpl : LevelSh; tV, tN, tH : TscSh
    (Own.lean: of a layer of a product tree and of a token sumcheck the numbers of challenges, the
    slots' numbers, PscSh and AffSh).
  `headHeardSh`. `headHeardSh_xEnd`: the number that HeadSh.xEnd sees is (headHeardSh x).tH.sEnd.
    `headHeardSh_rs`.
NOT SEEN HERE: g1, the copy of what the lookup returned: the chain's shape sees it by a component of
its own (look).
Limits. Definitions: no law says what a step lays into these fields. win's entries are made of the
request's words and of the heard reply: so they are left out, as the chain's shape sees neither: a
guard that reads a checked token cannot be written on this shape. A slot's number is a count of the
ledger: that it hangs on no value is not shown in this file. That LevelSh, TscSh, PscSh and AffSh
hold no field element is a reading of their types (the heads of Own.lean and Parts.lean). The names
HeardSh and heardSh are taken in this namespace (the lookup's record). Nothing on soundness,
completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Shape.Own
import OnBytes.Model.HeadHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model

/-- **The shape of what the output head's own rounds heard**: a field of Head.Heard a field, under
its own name; g1 is not here. -/
structure HeadHeardSh where
  /-- how many positions have a checked token: the tokens themselves are left out -/
  win : Nat
  Zl : Nat
  PV : Nat
  sW : Nat
  gp : Nat
  wpl : LevelSh
  sPv : Nat
  omV : Nat
  tV : TscSh
  tN : TscSh
  tH : TscSh
  rs : Nat
  qN : Nat
  qH : Nat

def headHeardSh (x : Head.Heard) : HeadHeardSh :=
  { win := x.win.size, Zl := x.Zl.size, PV := x.PV.size, sW := x.sW, gp := x.gp.size
    wpl := levelSh x.wpl, sPv := x.sPv, omV := x.omV.size, tV := tscSh x.tV, tN := tscSh x.tN
    tH := tscSh x.tH, rs := x.rs.size, qN := x.qN, qH := x.qH }

/-- The one number that HeadPart.lean's reader HeadSh.xEnd takes of it. -/
theorem headHeardSh_xEnd (x : Head.Heard) : (headHeardSh x).tH.sEnd = x.tH.sEnd := rfl

/-- The size of rs. -/
theorem headHeardSh_rs (x : Head.Heard) : (headHeardSh x).rs = x.rs.size := rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.headHeardSh_xEnd
#print axioms VerifiableInference.Desc.First.Shape.headHeardSh_rs
