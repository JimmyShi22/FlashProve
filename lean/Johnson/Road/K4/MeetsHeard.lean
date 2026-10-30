-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MeetsHeard.lean: THE FIELD hc OF `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean),
"K4's text covers the public record", FROM THE RETURN OF K4's HEARING: the text of `hear` refuses a
record that it does not cover (`hear_parts_later`, OnBytes/Desc/First/K4/HearParts.lean). Two
statements.

  `covers_of_hear`: where `hear` returns at { P with tokv := tk } in a group that is not the first:
    `covers P = true` (the test reads the layout and the reads alone, not the tokens).
  `Plan4.meets_public_heard`: `Plan4.meets_public` (Johnson/Road/K4/PlanPublic.lean) with the
    hearing's return in the place of hc.

Limits. One direction: from a return. What stays of `Meets` at the public part's record: that the
library's sizes agree with the parameter file's shape (Z) and the choice of the letter kW.

-/
import Johnson.Road.K4.PlanPublic
import OnBytes.Desc.First.K4.HearParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Model.Verify (Public publicOf layerShape)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par engFl hear hear_parts_later)

/-- The text refuses a record that it does not cover. -/
theorem covers_of_hear {P : Pub} {tk : Array Nat} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own}
    (h : hear engFl { P with tokv := tk } hp g fo F t = some (o, G, u)) (hg : (g == 0) = false) :
    covers P = true :=
  (hear_parts_later h hg).1

variable [scl : Scl] {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **The premises of the maps at a place that holds the public part's record and plan, where the
hearing returns.** -/
theorem Plan4.meets_public_heard {M Xs : Type} (Q : Plan4 Cb.Gl.E M Xs)
    (h : publicOf pol KL lay = .ok X) {p : Par} {tk : Array Nat}
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (Z : Sized (layerShape X.P) Q.D) (wk : Q.kW = X.layers.wsLay.lk) (hg : (p.g == 0) = false)
    {tk' : Array Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (hh : hear engFl { X.layers with tokv := tk' } p.hp p.g fo F t = some (o, G, u)) :
    Q.Meets p (layerShape X.P) X.P.polCalls :=
  Q.meets_public h hP hG (covers_of_hear hh hg) Z wk hg

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.covers_of_hear
#print axioms OnBytes.Road.K4.Plan4.meets_public_heard
