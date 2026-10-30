-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsSeat.lean: THE TIES FROM THE LAWS AT ROWS
2.1 | 2.2 | 2.4 | 2.5 OF THE KEY FILE's TABLE TO THE CONSTANT THAT THE SEAT CALLS: the premise hl of
each («the block's yes leaves the first component and …») and the sending kind's hS, PAID AT K14's
OWN BLOCKS (Desc.K14.blocks Q: the first, second, fourth and fifth) AS THE MAKER HOLDS THEM (held b:
Johnson/Desc/Sound/PaidAtDesc.lean), at any block b that decides as K14's does (at the key file's
description: seat bᵢ: seat_decide is rfl: Johnson/RunOne/KeyCut23.lean).
OBJECT: held b, b.decide = bᵢ.decide, blocks Q = some [b1, …, b8] · USER: loc_back₂ | point_back₂ |
keeps₂_send2 | keeps₂_send5 (hl) · keeps₂_send2_at | keeps₂_send5_at (hS) · LETTERS: Q : P14; P Cl
free.
  two_of_decideSend    the sending's decision says yes at two rounds alone
  sentBack_of_sendAt   **a yes of K14's sending lays SentBack**: by send_laid
    (Johnson/Desc/Key/Laid/SendLaid.lean) and what the kind notes behind
  sentBack_of_blocks   so at the second and the fifth block
  hl_point | hl_loc | hl_send2 | hl_send5   the four premises hl at held b
  hS_send2 | hS_send5  IsSend at held b, out of isSend_of_blocks
    (Johnson/Desc/K14/Law/SendGood.lean)
What is not claimed. That the key file's description's shared chain holds these blocks at these
places (shared_at_blocks, KeyCut23.lean; blocks (p14At X P) = some l: out of the
description's own test). Nothing on soundness.

-/
import Johnson.RunOne.KeyRows2225At
import Johnson.Desc.Key.Laid.SendLaid
import Johnson.Desc.K14.Law.SendGood
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (IsSend decideSend sendOwn)
open VerifiableInference.Desc.Key.LaidW (send_laid)
open _root_.Desc.K14 (P14 blocks sendAt parK1 withU withOmega)
open _root_.Desc.K14.Law (ebind_ok emap_ok named_some behindU_inv behindOmega_inv loc_of_blocks
    point_of_blocks isSend_of_blocks)

/-- The sending's decision says yes at two rounds alone. -/
theorem two_of_decideSend {L : Type} (Q : VerifiableInference.Desc.K1.Par) (owed : Option Nat) (d :
    _root_.Desc.Plain.DState L) (rs : List Fmt.RoundView)
    (x : Array Nat × _root_.Desc.Plain.DState L) (h : decideSend Q owed d rs = .ok x) : ∃ r₁ r₂, rs
        = [r₁, r₂] := by
  rcases rs with _ | ⟨r₁, _ | ⟨r₂, _ | ⟨r₃, l⟩⟩⟩
  · simp [decideSend] at h
  · simp [decideSend] at h
  · exact ⟨r₁, r₂, rfl⟩
  · simp [decideSend] at h

/-- **A yes of K14's sending lays SentBack.** -/
theorem sentBack_of_sendAt (Q₀ : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par) (inFront :
    Option Fmt.Entry) (groups : List (List Nat))
    (behind : St₂ → Array Nat → Option St₂)
    (hb : ∀ d ids d', behind d ids = some d' → d'.st = d.st ∧ d'.loc.psiSh = d.loc.psiSh ∧
        d'.loc.key = d.loc.key ∧ d'.loc.gU = d.loc.gU) :
    ∀ d rs gs d', (sendAt Q₀ n Q inFront groups behind).decide d rs gs = .ok d' → SentBack d d' :=
        by
  intro d rs gs d' h0
  simp only [sendAt, Block.inside] at h0
  obtain ⟨t, ht, h1⟩ := ebind_ok h0
  cases ht
  obtain ⟨t', ht', h2⟩ := ebind_ok h1
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨e, e1, e2, e3⟩ := hb _ _ _ (named_some h2)
  obtain ⟨r₁, r₂, hrs⟩ := two_of_decideSend Q _ _ _ _ hx
  rw [hrs] at hx
  have L := send_laid Q _ _ x2 r₁ r₂ ids hx
  exact ⟨by rw [e]; exact L.codes, by rw [e]; exact L.groups, fun o ho =>
      by rw [e]; exact L.older o ho, e1, e2, e3⟩

/-- So at the second and the fifth block. -/
theorem sentBack_of_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q =
    some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (∀ d rs gs d', b2.decide d rs gs = .ok d' → SentBack d d') ∧ (∀ d rs gs d', b5.decide d rs gs =
        .ok d' → SentBack d d') := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  refine ⟨sentBack_of_sendAt _ _ _ _ _ _ fun d ids d' h => ?_, sentBack_of_sendAt _ _ _ _ _ _ fun d
      ids d' h => ?_⟩
  · obtain ⟨e, o, mask, _, el⟩ := behindU_inv Q.par d d' ids h
    exact ⟨e, by rw [el], by rw [el], by rw [el]⟩
  · obtain ⟨e, o, sp, _, el⟩ := behindOmega_inv Q.par d d' ids h
    exact ⟨e, by rw [el], by rw [el], by rw [el]⟩

section
variable {P Cl : Type} (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some
    [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St₂ Cl)
include hbl

theorem hl_point (hd : b.decide = b1.decide) : ∀ z rs gs z', (held b : Block (P × St₂) Cl).decide z
    rs gs = .ok z' →
    z'.1 = z.1 ∧ _root_.Desc.K14.linPoint Q.par z.2 rs = some z'.2 := fun z rs gs z' h => by
  obtain ⟨e, h2⟩ := held_decide b z rs gs z' h
  exact ⟨e, point_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ (hd ▸ h2)⟩

theorem hl_loc (hd : b.decide = b4.decide) : ∀ z rs gs z', (held b : Block (P × St₂) Cl).decide z rs
    gs = .ok z' →
    z'.1 = z.1 ∧ _root_.Desc.K14.loc Q.par z.2 rs gs = some z'.2 := fun z rs gs z' h => by
  obtain ⟨e, h2⟩ := held_decide b z rs gs z' h
  exact ⟨e, loc_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ _ _ (hd ▸ h2)⟩

theorem hl_send2 (hd : b.decide = b2.decide) : ∀ z rs gs z', (held b : Block (P × St₂) Cl).decide z
    rs gs = .ok z' →
    z'.1 = z.1 ∧ SentBack z.2 z'.2 := fun z rs gs z' h => by
  obtain ⟨e, h2⟩ := held_decide b z rs gs z' h
  exact ⟨e, (sentBack_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl).1 _ _ _ _ (hd ▸ h2)⟩

theorem hl_send5 (hd : b.decide = b5.decide) : ∀ z rs gs z', (held b : Block (P × St₂) Cl).decide z
    rs gs = .ok z' →
    z'.1 = z.1 ∧ SentBack z.2 z'.2 := fun z rs gs z' h => by
  obtain ⟨e, h2⟩ := held_decide b z rs gs z' h
  exact ⟨e, (sentBack_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl).2 _ _ _ _ (hd ▸ h2)⟩

/-- IsSend at the held blocks. -/
theorem hS_sends (hd2 : b.decide = b2.decide) : ∃ sentU, withU Q.S = some sentU ∧
    IsSend (parK1 Q 2 "o_u and the first mask" sentU) (fun z : P × St₂ => z.2.st) (held b : Block (P
        × St₂) Cl) := by
  obtain ⟨sentU, hU, h2, _⟩ := isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  exact ⟨sentU, hU, fun s s' r₁ r₂ gs h => h2 s.2 s'.2 r₁ r₂ gs (hd2 ▸ (held_decide b s _ gs s'
      h).2)⟩

theorem hS_send5 (hd5 : b.decide = b5.decide) :
    IsSend (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) (fun z : P × St₂ => z.2.st) (held b :
        Block (P × St₂) Cl) := by
  obtain ⟨_, _, _, h5⟩ := isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  exact fun s s' r₁ r₂ gs h => h5 s.2 s'.2 r₁ r₂ gs (hd5 ▸ (held_decide b s _ gs s' h).2)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.sentBack_of_blocks
#print axioms Johnson.RunOne.KeyRows23.hl_point
#print axioms Johnson.RunOne.KeyRows23.hl_loc
#print axioms Johnson.RunOne.KeyRows23.hl_send2
#print axioms Johnson.RunOne.KeyRows23.hl_send5
#print axioms Johnson.RunOne.KeyRows23.hS_sends
#print axioms Johnson.RunOne.KeyRows23.hS_send5
