-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyOwedFull.lean: r6 OF THE KEY FILE's BACK: UNDER THE
NAMED EQUATIONS (Johnson.KB8.Pins) AND TWO MORE (hs · hD): owedOk SAYS YES: for every row of the
table «owed» a sub-protocol stands at that place, one of its rounds draws, and it names in «before»
every message of the row.

WHAT IS SAID.
  owedFirst_at · owedShared_at · owedSecond_at   the table's three parts read of the one-time
                   chain's values ranges and lin alone, and the shared chain's lin: so under the
                   equations they are the closed table owedW's.
  owedAll_in       under the equations each of the fifteen of owedAll 5 (IMR/KeyOwedYes.lean) stands
                   in the description's three flat lists, as beforesOf sees them.
  key_owedOk       **r6, to the ledger's letter (IM.keyBack_of_rows): (Key.descriptionFromSource X N P).owedOk =
                   true**, under Pins X N P · hs · hD.
  key_D_of_planOk  SO THAT hD HAS A PAYER: under Pins and r4 (planOk): X.Y.D = declKeyFull: by
                   decl_of_planOk (Johnson/Desc/Sound/ReadsOkProofs.lean) and
                   decl_full (Johnson/HB/LLHARD/KB8/Row.lean).
  key_owedOk_of_planOk   r6 under Pins · hs · r4.
THE PREMISES, BY NAME. h : Johnson.KB8.Pins X N P · hs : X.Y.k.shared.lin = keyFull.once.shape (the
shared chain's linear shape, as read back from the parameter bytes, is the typed one-time shape) ·
hD : X.Y.D.1 = declKeyFull.1: THE FIRST CHAIN's DECLARED ROUNDS AS HANDED IN ARE THE WRITTEN LIST:
the batching of the rows on the table counts in them the trees sent in front of it.
THE LEANING IS ACYCLIC: r6 ⟸ Pins · hs · hD; hD ⟸ Pins · r4. Nothing takes r6 back.
What is not claimed. THAT THE PREMISES HOLD AT THE RELEASE's OWN X N P. That the sub-protocol at a
place is the one that draws the challenge which the row means: that rests on the label (Block.lean's
own limit: owedOk is worth its name only beside wantedOk). No soundness.

-/
import Johnson.IMR.KeyOwedYes
import Johnson.IMR.KeyOwedSent
import Johnson.Desc.Sound.ReadsOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Johnson.KB8
open Lk6.AtPlan (keyFull)

theorem owedFirst_at (one : OneTime) (h1 : one.ranges = keyFull.ranges.x)
    (h2 : one.lin = keyFull.once.shape) : owedFirst one = owedFirst keyMade.oneTime := by
  unfold owedFirst
  rw [h1, h2]
  rfl

theorem owedShared_at (one : OneTime) (S : LinShape) (h1 : one.ranges = keyFull.ranges.x) :
    owedShared one S = owedShared keyMade.oneTime S := by
  unfold owedShared treeOfW
  rw [h1]
  rfl

theorem owedSecond_at (one : OneTime) (h1 : one.ranges = keyFull.ranges.x) :
    owedSecond one = owedSecond keyMade.oneTime := by
  unfold owedSecond treeOfW
  rw [h1]
  rfl

/-- **Under the equations the fifteen stand in the three flat lists.** -/
theorem owedAll_in {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    (hD : X.Y.D.1 = declKeyFull.1) : ∀ t ∈ owedAll 5,
      t ∈ beforesOf (descriptionFromSource X N P).first.blocksInOrder ++ beforesOf (descriptionFromSource X N P).shared.blocksInOrder ++
        beforesOf (descriptionFromSource X N P).second.blocksInOrder := by
  obtain ⟨O, hO, hOc, hOn⟩ := h.o
  have hW : H2U.roundsOfNums P.W.nums = some declKeyFull.2.2 := by rw [h.wN]; exact third_full
  have hbp : beforeSharedPoint P = (H2U.beforeOf 3 wNums).filter fun x => x.1 == 1 := by
    unfold beforeSharedPoint
    rw [(k12_before_at (Cl := Unit) K12.guardedProximityTestParts (place := ⟨3, none, 2, .K12⟩) h.wC.symm hW).2,
      h.wC, h.wN]
  intro t ht
  unfold owedAll at ht
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
    have hx' : x ∈ (lookupsOf X.Y.k.oneTime).zipIdx := by
      unfold lookupsOf
      rw [h.ranges, h.lin]
      exact hx
    have w := look_trip X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N hx'
    have e : lookRounds X.set x.1 = lookList keyFull.set x.1 := by
      rw [h.set, look_eq fit_full (List.all_eq_true.1 looks_zip_ok x hx)]
    rw [e] at w
    exact List.mem_append_left _ (List.mem_append_left _ w)
  rcases List.mem_append.1 ht with ht | ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have w := ranges_trip X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set h.nC
        (by rw [h.nN]; exact some_R)
      rw [h.nC, h.nN] at w
      exact List.mem_append_left _ (List.mem_append_left _ w)
    · have w := batt_trip X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N
      have e1 : rootsBefore X.Y.D.1 (batchRound X.Y.D.1) = 5 := by
        rw [hD]
        exact sent_full
      have e2 : battRoundsOf X.Y.k.oneTime.ranges X.Y.k.oneTime.lin =
          battRoundsOf keyFull.ranges.x keyFull.once.shape := by rw [h.ranges, h.lin]
      rw [e1, e2] at w
      exact List.mem_append_left _ (List.mem_append_left _ w)
  rcases List.mem_append.1 ht with ht | ht
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ht
    have w := shared_trip X.chains P (b := b) (by rw [h.sized, hbp]; exact hb)
    exact List.mem_append_left _ (List.mem_append_right _ w)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · have w := gu_trip X.chains h.uC (by rw [h.uN]; exact some_U)
      rw [h.uC, h.uN] at w
      exact List.mem_append_left _ (List.mem_append_right _ w)
    · have w := gomega_trip X.chains hO hOc (by rw [hOn]; exact some_O)
      rw [hOc, hOn] at w
      exact List.mem_append_left _ (List.mem_append_right _ w)
    · have w := own_trip X.chains h.wC hW
      rw [h.wC, h.wN] at w
      exact List.mem_append_right _ w

/-- **r6: every row of the table «owed» finds its sub-protocol.** -/
theorem key_owedOk {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    (hs : X.Y.k.shared.lin = keyFull.once.shape) (hD : X.Y.D.1 = declKeyFull.1) :
    (descriptionFromSource X N P).owedOk = true := by
  have e : (descriptionFromSource X N P).owed = owedW := by
    show owedFirst X.Y.k.oneTime ++ owedShared X.Y.k.oneTime X.Y.k.shared.lin ++
      owedSecond X.Y.k.oneTime = owedW
    rw [owedFirst_at _ h.ranges h.lin, owedShared_at _ _ h.ranges, owedSecond_at _ h.ranges, hs]
    rfl
  unfold FileDescription.owedOk
  rw [e]
  exact all_any_mono owedAt owedW (owedAll 5) _ (owedAll_in h hD) owed_yes

/-- So that hD has a payer: under the tests on the plan the declared rounds as handed in are the
written lists. -/
theorem key_D_of_planOk {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    (r4 : (descriptionFromSource X N P).planOk = true) : X.Y.D = declKeyFull :=
  (VerifiableInference.Desc.Sound.decl_of_planOk (descriptionFromSource X N P) r4).symm.trans (decl_full h)

theorem key_owedOk_of_planOk {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    (hs : X.Y.k.shared.lin = keyFull.once.shape) (r4 : (descriptionFromSource X N P).planOk = true) :
    (descriptionFromSource X N P).owedOk = true :=
  key_owedOk h hs (by rw [key_D_of_planOk h r4])

end IM

#print axioms IM.owedFirst_at
#print axioms IM.owedShared_at
#print axioms IM.owedSecond_at
#print axioms IM.owedAll_in
#print axioms IM.key_owedOk
#print axioms IM.key_D_of_planOk
#print axioms IM.key_owedOk_of_planOk
