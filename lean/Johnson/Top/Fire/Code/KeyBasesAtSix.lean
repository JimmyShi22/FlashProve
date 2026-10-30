-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyBasesAtSix.lean: at the full size: «THE PINNED TREES LIE BELOW THE PIECES' BASES» AT THE SIX WRITTEN SEATS, THE WRITTEN NUMBERS OF ROUNDS AND THE WRITTEN DATA; and, in scope, FROM ONE PUBLIC EQUATION (the data are the written data), the yes of the test at the tables' own lists. The closed fact is another file's, CALLED.
Main names.
  `bases_at_six`: `basesDoor atSix roundsW₁ roundsW₂ roundsW₃ writtenKFull = true`: `bases_at_six'` (BaseCountsFull.lean: by lower bounds on the trees that six short stretches send: the kernel does not walk the long ones), at this file's names of the same numerals.
  `basesAll_at_six`: in scope, where the data are the written data: `basesAll atSix (Fk X N P) D = true`: by `rounds_in_scope` | `lengths_in_scope` (KeyRoundsAtSeat.lean) and `basesAll_of_door` (BasePinsTie.lean).
OBJECT: `Key.descriptionFromSource X N P` in scope, the written data · USER: KeyAtPin.lean · LETTERS: none.
Limits. THAT THE RECORD's DATA ARE THE WRITTEN DATA IS A PREMISE HERE: other files have it as a theorem over the key file's door with its second test; not in the build on which this file was written.
(Where this and lean/THEOREM.md differ, the page holds.) Public numbers alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.BasePinsTie
import Johnson.Top.Fire.Code.KeyRoundsAtSeat
import Johnson.Top.Fire.Code.BaseCountsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (Fk oneAt atSix)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.G (writtenKFull)

theorem bases_at_six : basesDoor atSix roundsW₁ roundsW₂ roundsW₃ writtenKFull = true := bases_at_six'

/-- **In scope, at the written data, the test at the tables' own lists says yes.** -/
theorem basesAll_at_six {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) {D : WholeD} (hD : D = writtenKFull) : basesAll atSix (Fk X N P) D = true := by
  obtain ⟨r1, r2, r3⟩ := rounds_in_scope hZ hP hm hX hp hw
  obtain ⟨l1, l2, l3⟩ := lengths_in_scope hZ hP hm hX hp hw
  refine basesAll_of_door atSix (Fk X N P) D (by omega) (by omega) (by omega) ?_
  rw [r1, r2, r3, hD]
  exact bases_at_six

end LPFD

#print axioms LPFD.bases_at_six
#print axioms LPFD.basesAll_at_six
