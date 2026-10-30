-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ConfAlong.lean: "WHAT THE STORED TABLE DECODES TO": THE TOP STATEMENTS' OWN DECODER conf.D, AT THE LIBRARY's CONFIGURATION OF A STORED TABLE WITH A RECORD (DecR.configurationOfStoredTable, OnBytes/Slice/ConfOf.lean) OVER THE DATA MADE OFF THE TYPED SHAPE, THROUGH THE CELLS, IS THE GUARDED DECODER OF THE SHARED CHAIN's BLOCK 1 AT THE
CORRESPONDING RECORD. Two theorems. General in the shape, the claims and the rest.

  dec_at_conf: (DecR.configurationOfStoredTable A R).D (tabBack logN c) r = decGuard collAt dcdAt (DecR.configurationOfStoredTable A R).held c (trS of the seed, the answers): by the library's conf_D (the decoder written out: rfl) and dec_at_shape (Johnson/Desc/Sound/StoredAlong.lean). IT ENDS IN conf.D.
  dec_at_letters: the same at (lettersAt A R).conf (Johnson/EntryRec/AtConf.lean), the form in which the release's configuration is written.
SO the condition (DEC) of Johnson/Desc/Sound/ClaimCarried.lean holds, with tr r := (trS r.1, r.2) and held := the configuration's own ("in range", then the matrix), AT EVERY CONFIGURATION OVER decROfS. WHAT STAYS: that the RELEASE's data of a decoder (at written sizes) ARE decROfS of the plan's shape at the plan's radius.

Limits. rank is the library's. Nothing at a record whose factor is 0. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StoredAlong
import Johnson.EntryRec.AtConf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open VerifiableInference.Desc.Sound (tabBack decGuard CellsOf)

/-- **The top statements' own decoder, through the cells, is block 1's guarded decoder at the corresponding record.** -/
theorem dec_at_conf {X : Type} (p : Par) (err eM : Nat) (A : (decROfS p.S.fold eM).Claims X)
    (R : (decROfS p.S.fold eM).RelationsAndEncoding A) (c : CellsOf) (r : (decROfS p.S.fold eM).Rec) :
    (DecR.configurationOfStoredTable A R).D (tabBack p.S.fold.index.code.logN c) r =
      decGuard (collAt p err eM (rankLib p.S.fold)) (dcdAt p err eM (rankLib p.S.fold)) (DecR.configurationOfStoredTable A R).held c
        (trS p.S.fold.index err r.1, r.2) := by
  rw [DecR.conf_D]
  exact dec_at_shape p err eM (DecR.configurationOfStoredTable A R).held c r

/-- The same in the form in which the release's configuration is written. -/
theorem dec_at_letters {X : Type} (p : Par) (err eM : Nat) (A : (decROfS p.S.fold eM).Claims X)
    (R : (decROfS p.S.fold eM).RelationsAndEncoding A) (c : CellsOf) (r : (decROfS p.S.fold eM).Rec) :
    (OnBytes.RunA.lettersAt A R).conf.D (tabBack p.S.fold.index.code.logN c) r =
      decGuard (collAt p err eM (rankLib p.S.fold)) (dcdAt p err eM (rankLib p.S.fold)) (DecR.configurationOfStoredTable A R).held c
        (trS p.S.fold.index err r.1, r.2) :=
  dec_at_conf p err eM A R c r

end Desc.K14.Law

#print axioms Desc.K14.Law.dec_at_conf
#print axioms Desc.K14.Law.dec_at_letters
