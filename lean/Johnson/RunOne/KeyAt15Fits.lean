-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyAt15Fits.lean: NO NEW FACT: A TEST OF FIT. The public premises of Johnson/RunOne/KeyAt15Seat.lean | KeyAt15Base.lean are restated AT ANOTHER FILE's OWN NAME i₁ (Johnson/RunOne/Law/K12Law15At.lean) and closed by the theorems as they stand: so that «in the law's own letters» is held by Lean and not by reading.

-/
import Johnson.RunOne.KeyAt15Base
import Johnson.RunOne.Law.K12Law15At

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes.Maker
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁)
open Johnson.RunOne.Law.K12Law15At (i₁)

theorem hlog_fits (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) :
    ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i₁).1 = some o → o.logLength = aOf csKey (six.get i₁).1 :=
  (seat_15_scope X N P hi hc hr).1

theorem told_fits (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) :
    ((Fk X N P).oracleAt (seatAt six numSix atSix i₁).1).isSome = true :=
  (seat_15_scope X N P hi hc hr).2

theorem hseed_fits (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D' : WholeD) (a : Xi × FirstState)
    (h : Hist₁ (Fk X N P) D' 15 a) : ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y :=
  seed_15_scope X N P hp hc hr D' a h

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.hlog_fits
#print axioms Johnson.RunOne.KeyLetters.told_fits
#print axioms Johnson.RunOne.KeyLetters.hseed_fits
