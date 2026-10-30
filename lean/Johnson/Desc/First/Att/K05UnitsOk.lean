-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05UnitsOk.lean: the public record `UnitIs`
(Johnson/Desc/First/Att/K05LookAll.lean) at all seven units of the place of the kind K5, from one
test on the plan.

Definitions, statements and proofs.
Main names:
  `remainders g`: the two units of the remainder calls (the lists rm and rd), made as `Geo.scores`
    makes those of the softmax-table calls.
  `unitsOk S fs`: the test: the place has two remainder units, two score units (the first below the
    diagonal, the second on it) and the three single units wl, ix and wh, and `unitOk` says yes at
    (m1, call 0), (d1, call 0), (m2, call 1), (d2, call 1), (w3, call 2), (x3, call 2) and (f4, call
    3), at D := dimOf S and C := callsOf fs.
  `UnitsAll S fs …`, `units_all`: what a yes gives: the seven units by name, the two flags, seven
    `UnitIs`.
  `unitIs_m1`, `unitIs_d1`: a score unit's record at the family m2 or d2 is its record at m1 or d1
    too, where the first two calls have one size.
  `lookAll_of_units`: `LookAll` from `KeyPtsAre` and `UnitsAll`.
Used: plain records, pure functions and lemmas on them alone; no routine in a context:
`unitOk`, `unitIs_of_ok`, `lookAll_of`, `geoOf`, `dimOf`, `callsOf`.
Limits: `UnitsAll` is shown of no place by a theorem; `unitsOk` is evaluated in no file of this
tree. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LookAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb OnBytes OnBytes.Model Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Road.L5 (callsOf dimOf)

/-- The units of the remainder calls, in the order of hearing. -/
def remainders (g : Geo) : List UnitG := (g.units .kr [.rm, .rd]).map fun u => g.unitAt u.1 u.2.1 u.2.2

/-- **The one test on the place's seven units.** -/
def unitsOk (S : Attention.Shape) (fs : Model.Forest.Shape) : Bool :=
  match remainders (geoOf S), (geoOf S).scores, (geoOf S).single .wl, (geoOf S).single .ix,
      (geoOf S).single .wh with
  | [r1, r2], [u1, u2], some wl, some ix, some wh =>
    u1.below && !u2.below &&
      unitOk (dimOf S) (callsOf fs) .m1 0 r1 && unitOk (dimOf S) (callsOf fs) .d1 0 r2 &&
      unitOk (dimOf S) (callsOf fs) .m2 1 u1 && unitOk (dimOf S) (callsOf fs) .d2 1 u2 &&
      unitOk (dimOf S) (callsOf fs) .w3 2 wl && unitOk (dimOf S) (callsOf fs) .x3 2 ix &&
      unitOk (dimOf S) (callsOf fs) .f4 3 wh
  | _, _, _, _, _ => false

/-- What a yes gives. -/
structure UnitsAll (S : Attention.Shape) (fs : Model.Forest.Shape) (r1 r2 u1 u2 wl ix wh : UnitG) : Prop where
  rem : remainders (geoOf S) = [r1, r2]
  sco : (geoOf S).scores = [u1, u2]
  sWl : (geoOf S).single .wl = some wl
  sIx : (geoOf S).single .ix = some ix
  sWh : (geoOf S).single .wh = some wh
  below : u1.below = true
  on : u2.below = false
  m1 : UnitIs (dimOf S) (callsOf fs) .m1 0 r1
  d1 : UnitIs (dimOf S) (callsOf fs) .d1 0 r2
  m2 : UnitIs (dimOf S) (callsOf fs) .m2 1 u1
  d2 : UnitIs (dimOf S) (callsOf fs) .d2 1 u2
  w3 : UnitIs (dimOf S) (callsOf fs) .w3 2 wl
  x3 : UnitIs (dimOf S) (callsOf fs) .x3 2 ix
  f4 : UnitIs (dimOf S) (callsOf fs) .f4 3 wh

theorem units_all {S : Attention.Shape} {fs : Model.Forest.Shape} (h : unitsOk S fs = true) :
    ∃ r1 r2 u1 u2 wl ix wh, UnitsAll S fs r1 r2 u1 u2 wl ix wh := by
  unfold unitsOk at h
  split at h
  · rename_i r1 r2 u1 u2 wl ix wh e1 e2 e3 e4 e5
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := h
    exact ⟨r1, r2, u1, u2, wl, ix, wh, e1, e2, e3, e4, e5, a1, a2, unitIs_of_ok b1, unitIs_of_ok b2,
      unitIs_of_ok b3, unitIs_of_ok b4, unitIs_of_ok b5, unitIs_of_ok b6, unitIs_of_ok b7⟩
  · cases h

/-- A score unit's record at m2 is its record at m1, where the first two calls have one size. -/
theorem unitIs_m1 {D : Dim} {C : Calls} {u : UnitG} (h01 : C.a 0 = C.a 1) (U : UnitIs D C .m2 1 u) :
    UnitIs D C .m1 1 u :=
  ⟨U.call, h01.symm, U.bits, U.le, U.nPw, U.w⟩

theorem unitIs_d1 {D : Dim} {C : Calls} {u : UnitG} (h01 : C.a 0 = C.a 1) (U : UnitIs D C .d2 1 u) :
    UnitIs D C .d1 1 u :=
  ⟨U.call, h01.symm, U.bits, U.le, U.nPw, U.w⟩

/-- **LookAll from the lookup's kind's record and the one test.** -/
theorem lookAll_of_units {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type} (P0 : OwnPar K M0 X)
    {S : Attention.Shape} {fs : Model.Forest.Shape} (hD : P0.D = dimOf S) (hC : P0.C = callsOf fs)
    (h01 : (callsOf fs).a 0 = (callsOf fs).a 1) {r1 r2 u1 u2 wl ix wh : UnitG}
    (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (zk : Array (Array E)) (x0 : X)
    (Kp : KeyPtsAre ρ P0.C (P0.zOf x0) zk) : LookAll P0 S zk u1 u2 ρ x0 :=
  lookAll_of P0 S zk u1 u2 x0 Kp (qW := 2) (qM := 1) (qD := 1)
    (fun w hw => by
      rw [U.sWl] at hw
      rw [← Option.some.inj hw, hD, hC]
      exact U.w3)
    (by rw [hD, hC]; exact unitIs_m1 h01 U.m2) (by rw [hD, hC]; exact unitIs_d1 h01 U.d2)

end VerifiableInference.Desc.First.Att.P
