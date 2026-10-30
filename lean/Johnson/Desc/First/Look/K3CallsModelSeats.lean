-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsModelSeats.lean: FROM THE FORM IN WHICH THE COMPOSED MEANING READS A
WITNESS (the sizes sizesOf X and seats seatsOf X (sizesOf X) layout num, off the
layout) TO THE FORM OF THE PREMISES hhid, hb, fit, reads OF att_model_hid, lay_model_hid
(Johnson/Desc/First/Look/K3CallsModelAt.lean: the sizes szOf (tls j), the seats seatBy (fLay layout
num)): at tls := Meaning.tlAt X the sizes are one by rfl; IN THE GOALS' SCOPE THE TWO FAMILIES OF
SEATS ARE ONE FUNCTION: below 25 by seatsOf_eq
(Johnson/Goal/Meaning/HidSeatsOf.lean); from 25 on the sizes have no matrix, so both are functions
on the empty type. A carrying: no new mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two families of seats off the public parameters and the layout.
USER: Johnson/Desc/Sound/MgAt/K3CallsTermsAt.lean, K3CallsLeftR.lean, K3CallsOwedScope.lean.
  Meant: whoever lays the premises hhid, hb, reads at the composed meaning's own H.
LETTERS: pol, KL, lay, X as in the scope's theorems; C: the public core; layout, num.

Main names: `sizesOf_none` · `seatsOf_all` · `hhid_of_seatsOf`, `hb_of_seatsOf`,
`reads_of_seatsOf`, `fit_at_tlAt`.

Limits. The goals' scope (through the public core C).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsModelAt
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Road
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open _root_.Meaning (BaseSegF seatBy fLay Msgs hidAtF ReadsOne sizesFit sizesOf seatsOf seatsOf_eq
  follows_of_core fit_sizesOf)

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- From segment 25 on the sizes sizesOf X have no matrix. -/
theorem sizesOf_none (k : ℕ) (hk : 25 ≤ k) : (sizesOf X k).NM = 0 := by
  unfold _root_.Meaning.sizesOf _root_.Meaning.tlAt
  rw [if_pos (by omega)]
  rfl

/-- **In scope the seats off the layout ARE the seats by the label, at every segment.** -/
theorem seatsOf_all (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (layout : Params.ReqLayout) (num : ℕ → ℕ → ℕ) :
    seatsOf X (sizesOf X) layout num = seatBy (fLay layout num) X (sizesOf X) := by
  funext k
  by_cases hk : k < 25
  · exact seatsOf_eq h C (follows_of_core h C) layout num hk
  · funext μ
    have h0 : (sizesOf X k).NM = 0 := sizesOf_none k (by omega)
    have h1 : μ.val < (sizesOf X k).NM := μ.isLt
    omega

variable {P W : Type} {rows cols : ℕ} {H : P5J.HidAt X P W rows cols}
  {layout : Params.ReqLayout} {num : ℕ → ℕ → ℕ} {tok : W → Fin ppref.V} {msgF : W → ℕ → Msgs}

/-- hhid. -/
theorem hhid_of_seatsOf (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hh : ∀ w, H.hid w =
      hidAtF X (sizesOf X) (seatsOf X (sizesOf X) layout num) (tok w) (msgF w)) :
    ∀ w, H.hid w = hidAtF X (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay layout num) X fun j => szOf (_root_.Meaning.tlAt X j)) (tok w) (msgF w) := by
  intro w
  rw [hh w, seatsOf_all h C layout num]
  rfl

/-- hb. -/
theorem hb_of_seatsOf (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hh : ∀ j w, H.base j w →
      BaseSegF (sizesOf X) (seatsOf X (sizesOf X) layout num) (msgF w) j) :
    ∀ j w, H.base j w → BaseSegF (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay layout num) X fun j => szOf (_root_.Meaning.tlAt X j)) (msgF w) j := by
  intro j w hb
  have h1 := hh j w hb
  rw [seatsOf_all h C layout num] at h1
  exact h1

/-- reads. -/
theorem reads_of_seatsOf (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hh : ∀ w, ReadsOne X (sizesOf X) (seatsOf X (sizesOf X) layout num) (msgF w)) :
    ∀ w, ReadsOne X (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay layout num) X fun j => szOf (_root_.Meaning.tlAt X j)) (msgF w) := by
  intro w
  have h1 := hh w
  rw [seatsOf_all h C layout num] at h1
  exact h1

/-- fit: a theorem in scope. -/
theorem fit_at_tlAt (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    sizesFit X (fun j => szOf (_root_.Meaning.tlAt X j)) = true :=
  (fit_sizesOf h C (fLay default fun _ _ => 0)).1

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.seatsOf_all
#print axioms VerifiableInference.OnPublicFiles.hhid_of_seatsOf
#print axioms VerifiableInference.OnPublicFiles.hb_of_seatsOf
#print axioms VerifiableInference.OnPublicFiles.reads_of_seatsOf
#print axioms VerifiableInference.OnPublicFiles.fit_at_tlAt
