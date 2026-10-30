-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/AtFreeCfg.lean: It stands on Johnson/RunOne/Sound/.
AT EVERY THREE PUBLIC FILES IN THE GOALS' SCOPE, AND AT EVERY DIGEST THAT
IS HANDED TO THE MAKER, THE THREE PUBLIC PREMISES OF THE LINKS' LAWS HOLD AT THE KEY FILE'S OWN
DESCRIPTION: the target is 128; the planner's own rounds hold for each lookup (LookHeld); what all
lookups take of the two messages' mask entries fits (RoomFor).

Why at every digest. The verifier's text lays the key file's description at a fixed digest
(Key.keyDataAndDecisionAtFixedDigest, Johnson/Desc/Key/Slot.lean), not at the digest of the public files. A law that is
typed at the planner's own digest does not reach it. The key's sizes do not hang on the digest:
key_at_chains says so, by the steps of key_at_policy (Johnson/Goal/PlanValues/ScopeAtPlan.lean) from
chainsOf alone in the place of planned. Nor is it asked that Z comes from the program's own
publicOf, which calls a concrete hash function: the verifier's text reads the public files by a
routine that takes the hash function as a letter. Asked is ReadOf, which names none.

Main names (ReadOf, readOf_publicOf and key_at_chains have moved, under their full names, to
KeyInScope.lean):
  seat_in_scope: THE THREE PREMISES, at the source that the maker's record gives.
  seat_at_fixed: the same from the yes of Key.keyDataAndDecisionAtFixedDigest.

Object: Key.keyDataAndDecisionAtFixedDigest Z lay, through laid_parts (KeyInScope.lean; laidFixed_is): the description
descriptionFromSource X N P whose run the verifier's text calls; (FK X N P) is it, pulled to the records.
User: seat_at_o (ReadAtO.lean). The three conclusions are fk_chain₁_own's hL (Chain1Priced.lean),
promL_room's hR (TakesSum.lean) and the reading of its bound 2⁻¹ ^ X.set.target as 2⁻¹ ^ 128.
Letters: Zp: three public files in scope · Z: under ReadOf Zp.pol Z · cfg: ANY digest.

Limits. One size: the scope's. One direction: from routines that return and tests that say yes. The
facts at keyFull are evaluations by the kernel (HeldFull.lean, TakesFull.lean). The target counts a
round's proof of work. Nothing on soundness.

-/
import Johnson.RunOne.Law.SourceIs
import Johnson.RunOne.Law.LinkAtPlan
import Johnson.Desc.First.Look.KeyLaw.HeldFull
import Johnson.Desc.First.Look.KeyLaw.TakesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.AtFreeCfg
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open Lk6.AtPlan
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source madeAt sourceOf)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.SourceIs

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **THE THREE PUBLIC PREMISES OF THE LINKS' LAWS, IN SCOPE, AT ANY DIGEST.** -/
theorem seat_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (FK X N P).planOk = true) :
    X.set.target = 128 ∧
      (∀ l, l < X.Y.k.oneTime.ranges.lookups.length →
        LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) ∧
      RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
        X.Y.k.oneTime.indexMasks.shape := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope hZ hP hm hX hp
  refine ⟨by rw [e1]; exact target_full, fun l hl => ?_, by rw [e2, e3, e4, e5]; exact room_full⟩
  have hmem : Lof X.Y.k.oneTime l ∈ keyFull.ranges.x.lookups := by
    unfold Lof
    rw [← e2, List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  rw [e1, e2, e3]
  exact lookHeld_of_list (List.all_eq_true.1 held_full _ hmem)

/-- **The same from the yes of the key file's piece at the fixed digest.** -/
theorem seat_at_fixed {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {D : OnBytes.Maker.WholeD}
    {r : VerifiableInference.Desc.Key.KeyRun}
    (h : VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest Z Zp.lay = .ok (D, r)) :
    ∃ X N P, (FK X N P).planOk = true ∧ (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ X.set.target = 128 ∧
      (∀ l, l < X.Y.k.oneTime.ranges.lookups.length →
        LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) ∧
      RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
        X.Y.k.oneTime.indexMasks.shape := by
  obtain ⟨m, X, N, P, hm, hX, hp, hD, hr⟩ := Johnson.RunOne.Law.KeyInScope.laid_parts h
  exact ⟨X, N, P, hp, hD, hr, seat_in_scope (N := N) (P := P) hZ hP hm hX hp⟩

end Johnson.RunOne.Law.AtFreeCfg

#print axioms Johnson.RunOne.Law.AtFreeCfg.seat_in_scope
#print axioms Johnson.RunOne.Law.AtFreeCfg.seat_at_fixed
