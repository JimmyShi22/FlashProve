-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyTenInScope.lean: THEOREMS; CALLS ALONE. **IN THE GOALS' SCOPE: the test on a seat finds no fault at the shared chain's three sampled messages (6, 0) · (7, 0) · (8, 0), and the second chain's frame at the written data holds their trees at their codes' depths**: beside the seven of Johnson/RunOne/KeySevenInScope.lean: X N P as letters.
OBJECT: Key.descriptionFromSource X N P. USER: none yet (meant: other files' six premises n3 n4 n5 · holdsB (fr₂ D) 6 | 7 | 8 at the second frame). LETTERS: the public files Zp · Z · cfg · m · X N P: as in seven_at.
  chains_of     the source's field «chains» is the planner's chains as madeAt returns them (by sourceOf's text)
  Six           three tests with code on the description (seatFaultAt) and three facts on the second frame's list at the data
  six_at        **seven_at's seven premises ⊢ the six**
What is not claimed. That the premises hold at any files: as for seven_at ([RAN] at the stored full-size public files, at publicOf's reading). Anything of the rider at (6, 1). It names no o. Nothing on soundness.

-/
import Johnson.RunOne.KeySevenInScope
import Johnson.RunOne.KeySeatScope23
import Johnson.RunOne.KeyScopeNums23

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Maker
open VerifiableInference.Desc
open Johnson.RunOne.KeyRows23 (fr₂)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shU shO shSp)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.KeyInScope (key_in_scope)
open Johnson.RunOne.Sound (rounds_in_scope)

/-- The source's field «chains» is the planner's chains as madeAt returns them. -/
theorem chains_of {m : Johnson.G.OfPlan.Made} {X : Key.Source} (h : Key.sourceOf m = .ok X) : X.chains = m.p.chains := by
  unfold Key.sourceOf at h
  obtain ⟨D, _, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨T, _, h⟩ := OnBytes.Params.exc_bind h
  cases h
  rfl

/-- Three tests on the description's telling, three facts on the second frame's list. -/
def Six (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (D : WholeD) : Prop :=
  (∀ t3 t4 t5 : String, seatFaultAt (Key.descriptionFromSource X N P) csKey t3 shU 6 0 = none ∧ seatFaultAt (Key.descriptionFromSource X N P) csKey t4 shO 7 0 = none ∧
    seatFaultAt (Key.descriptionFromSource X N P) csKey t5 shSp 8 0 = none) ∧
  ((fr₂ D).all.any fun t => t.no == 6 && decide (aOf csKey shU ≤ t.a)) = true ∧
  ((fr₂ D).all.any fun t => t.no == 7 && decide (aOf csKey shO ≤ t.a)) = true ∧
  ((fr₂ D).all.any fun t => t.no == 8 && decide (aOf csKey shSp ≤ t.a)) = true

/-- **The six, X N P as letters.** -/
theorem six_at {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull) : Six X N P writtenKFull :=
  ⟨fun t3 t4 t5 => n345_scope X N P ((congrArg (·.made.sized.key) (chains_of hX)).trans (key_in_scope hZ hP hm)) hp hD
    (rounds_in_scope hZ hP hm hX hp hw).1 t3 t4 t5, holds6, holds7, holds8⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.chains_of
#print axioms Johnson.RunOne.KeyLetters.six_at
