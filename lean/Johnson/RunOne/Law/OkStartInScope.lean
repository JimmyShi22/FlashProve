-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/OkStartInScope.lean: It stands on one file of Johnson/RunOne/Sound/.
THE KEY FILE'S TEST ON THE INSTANCE SAYS YES AT EVERY
TYPED RECORD, IN SCOPE, AT ANY DIGEST. The test okStart of Key.descriptionFromSource X N P at the instance of a typed
record (Key.keyInstanceOfOutOfDomainSample rec) says yes just where three public numbers of the source's shape are the type's
(okStart_instK_iff, Johnson/RunOne/Sound/OkStartAtInstK.lean): the record is not read. Here the
three are shown: the shared chain's shape as read is the one-time chain's (the clause "shape" of the
test on the file), that is the planner's sized key's (five_at), that is the written value keyFull's
(key_at_chains), at which the three numbers are evaluated by the kernel.

Main names (fk_shape, index_full and index_full_no stand, under their full names, in
KeyInScope.lean):
  okStart_in_scope: ∀ rec, okStart (keyInstanceOfOutOfDomainSample rec) = true.

Object: (Key.descriptionFromSource X N P).okStart, at the X N P of a laid piece.
User: all_in_scope (AllAtO.lean).
Letters: Zp in scope · Z under ReadOf · any digest.

Limits. One size. One direction. Nothing on soundness.

-/
import Johnson.RunOne.Law.KeyInScope
import Johnson.RunOne.Sound.OkStartAtInstK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.OkStartInScope
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Flat
open OnBytes.Model.Verify (Public)
open Lk6.AtPlan
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source madeAt sourceOf sourceClauses)
open Johnson.RunOne.Sound (okStart_instK_iff)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **THE TEST ON THE INSTANCE SAYS YES AT EVERY TYPED RECORD, IN SCOPE, AT ANY DIGEST.** -/
theorem okStart_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true)
    (rec : RecFull) :
    (VerifiableInference.Desc.Key.descriptionFromSource X N P).okStart (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample rec) =
      true := by
  rw [okStart_instK_iff, Johnson.RunOne.Law.KeyInScope.shared_lin_in_scope hZ hP hm hX hp]
  exact index_full

end Johnson.RunOne.Law.OkStartInScope

#print axioms Johnson.RunOne.Law.OkStartInScope.okStart_in_scope
