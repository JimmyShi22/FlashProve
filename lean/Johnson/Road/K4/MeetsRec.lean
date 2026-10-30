-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MeetsRec.lean: THE RECORD `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean) AT THE
RECORD THAT THE VERIFIER's OWN `publicOf` RETURNS, AT THE LIBRARY's REFERENCE SIZES, FROM ONE
TEST, AND THAT K4's TEXT COVERS THE RECORD OR ITS HEARING RETURNS. Two statements. Nothing new is
argued.

  `Plan4.meets_of_record`: where `publicOf` returns X, the test `recordB X g`
    (Johnson/Road/Ends/AlgBridgeRec.lean) says true, the place holds X's record of the layers (with
    whatever tokens) and X's plan of the group g, g is not the first group, K4's text covers the
    record, and the value has D := `Dim.ref` and kW := `kRef`: `Meets`.
  `Plan4.meets_of_record_heard`: the same with the return of K4's hearing in the place of "covers"
    (`covers_of_hear`, Johnson/Road/K4/MeetsHeard.lean).

Of the eight fields of `Meets`: four by `Plan4.meets_public` (Johnson/Road/K4/PlanPublic.lean); that
the sizes agree with the shape by the test (`bridgeB_parts`); the column bits of the weights by the
test and `wsLayOf_units`; that K4's text covers the record is a premise of the first
statement and comes from the hearing's return in the second; that the group is not the first
stays a premise of both.

WHAT IS A THEOREM AND WHAT IS A RUN, AND AT WHICH SIZES: the head of
Johnson/Road/K4/PubLinesRec.lean says it, and it holds here word for word: that the test says true
anywhere is no theorem; a run of it stands in Johnson/Road/Ends/GuardRec.lean.

Limits. D := `Dim.ref` and kW := `kRef` are choices of the value's letters, premises here. Nothing
on soundness.
-/
import Johnson.Road.K4.MeetsHeard
import Johnson.Road.Ends.AlgBridgeOne
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Road.Alg (recordB bridgeB_parts returns_of_record)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (covers Par engFl hear)

variable [scl : Scl] {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **`Meets` at `publicOf`'s own record and the reference sizes, from the test.** -/
theorem Plan4.meets_of_record {M Xs : Type} (Q : Plan4 Cb.Gl.E M Xs) (hD : Q.D = Dim.ref)
    (hk : Q.kW = kRef) (h : publicOf pol KL lay = .ok X) {p : Par}
    (t : recordB X p.g = true) {tk : Array Nat} (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg : (p.g == 0) = false) (hc : covers X.layers = true) :
    Q.Meets p (layerShape X.P) X.P.polCalls := by
  obtain ⟨_, _, _, _, _, hW, tb⟩ := returns_of_record h t
  obtain ⟨_, Z, _⟩ := bridgeB_parts tb
  exact Q.meets_public h hP hG hc (hD ▸ Z) (hk.trans (wsLayOf_units hW).1.symm) hg

/-- **The same, where K4's hearing returns.** -/
theorem Plan4.meets_of_record_heard {M Xs : Type} (Q : Plan4 Cb.Gl.E M Xs) (hD : Q.D = Dim.ref)
    (hk : Q.kW = kRef) (h : publicOf pol KL lay = .ok X) {p : Par}
    (t : recordB X p.g = true) {tk : Array Nat} (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg : (p.g == 0) = false) {tk' : Array Nat}
    {fo : Forest.Heard} {F G : Fork} {t0 u : Tape} {o : Own}
    (hh : hear engFl { X.layers with tokv := tk' } p.hp p.g fo F t0 = some (o, G, u)) :
    Q.Meets p (layerShape X.P) X.P.polCalls :=
  Q.meets_of_record hD hk h t hP hG hg (covers_of_hear hh hg)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.meets_of_record
#print axioms OnBytes.Road.K4.Plan4.meets_of_record_heard
