-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/Hmask15.lean: THE PREMISE
hmask OF ANOTHER FILE'S RIDERS AT THE FIELD r1_15 (ride_15, back_15:
Johnson/RunOne/Law/KeyRide15.lean), PAID IN ITS VERY FORM, at the reading Reading.gl: at every state
that the key file's first chain reaches at border 15, the reading of the mask form of every pending
row on a lookup's keys is the same at a witness and at that witness with message 1's table laid
anew.

How: keys_ix_of_hist (KeysIx.lean): that reading is one at any two worlds of mask entries that read
alike on message number 0; the laying of message 1 leaves what the reader reads of message 0
(reads_layAt_off, Johnson/Desc/Key/KeyLay.lean, under the three premises that ride_15 has itself).

Main names:
  mk_lay: at a slot of message 0 the mask entry read is the same before and behind the laying.
  hmask_15: the premise, written after its text, at ρ := Reading.gl.

Object: the premise hmask of ride_15 and back_15. User: none yet (meant: the joining of "back" at
the field r1_15). Letters: X, N, P, D · y: strings of the frame (rec_of_hist's letter; the statement
does not read it) · G, at_, R: the table's reading, seats and reader · w, m: a witness, a table.
Premises: planOk · RoomFor · the own message counts an answer · two lookups (the last three are
theorems in scope) · the history at border 15 · ArrOk G at_ [0] · ReadsPinned G at_ R [0] ·
SeatsApart at_ [1] [0] (ride_15's own ha, hr, hs).

Limits. A sentence on values. At Reading.gl alone. THAT THE STATEMENT'S TYPE IS ride_15's BINDER IS
NOT CHECKED BY LEAN HERE (this file does not import KeyRide15.lean): it is written after its text;
the caller's join is that check. Nothing on soundness.

-/
import Johnson.RunOne.Law.KeysIx
import Johnson.Desc.Key.KeyLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.Hmask15
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where valOf mkOf formAt layAt ArrOk
  ReadsPinned SeatsApart reads_layAt_off)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁)
open Johnson.RunOne.Law.KeysIx
open LPFD (Hist₁)

variable {Cells M Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- At a slot of message 0 the mask entry read is the same before and behind the laying of message
1. -/
theorem mk_lay (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where) (R : KRead Cells M)
    (one : OneTime) (w : Wit Cells Unit M) (m : M) (ha : ArrOk G at_ [0])
    (hr : ReadsPinned G at_ R [0]) (hs : SeatsApart at_ [1] [0]) (z : Slot) (hz : z.oracle = 0) :
    mkOf (plan₁ one) R (layAt at_ [1] (fun _ => m) w) z = mkOf (plan₁ one) R w z := by
  unfold mkOf
  rw [hz]
  show R.val (R.of (layAt at_ [1] (fun _ => m) w) 0) .mask z.index = R.val (R.of w 0) .mask z.index
  rw [reads_layAt_off G at_ R [1] [0] (fun _ => m) w ha hr (by simp) hs 0 (by simp)]

/-- **hmask, PAID, AT BORDER 15.** -/
theorem hmask_15 (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (hans : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (a : Xi × FirstState)
    (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 15 a)
    (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where) (R : KRead Cells M)
    (w : Wit Cells Unit M) (m : M) (ha : ArrOk G at_ [0]) (hr : ReadsPinned G at_ R [0])
    (hs : SeatsApart at_ [1] [0]) :
    ∀ l ks, l < 2 → (readers₁ X.Y.k.oneTime).keysAt a.2 l = some ks → ∀ x ∈ ks,
      Model.Reading.gl.val (formAt (mkOf (plan₁ X.Y.k.oneTime) R (layAt at_ [1] (fun _ => m) w))
          x.masks) =
        Model.Reading.gl.val (formAt (mkOf (plan₁ X.Y.k.oneTime) R w) x.masks) :=
  fun l ks _ hks x hx =>
    keys_ix_of_hist D y hp hR hans hn 15 (by omega) (by omega) a h l ks hks x hx _ _ fun z hz => by
      rw [mk_lay G at_ R X.Y.k.oneTime w m ha hr hs z hz]

end Johnson.RunOne.Law.Hmask15

#print axioms Johnson.RunOne.Law.Hmask15.mk_lay
#print axioms Johnson.RunOne.Law.Hmask15.hmask_15
