-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SlotWord.lean: the code switch: THE KEPT SLOT OF THE MADE OPEN WORD
IS THE WORD THAT THE TABLE OF JOINTS' OWN READER MAKES OF THE KEPT MEMBER's SEAT.
  slot_word    (plainHd r H).sW k ‹the open word of CarryK2.lean's faAt› = ((sigOf r.cs r.lo).om
               k.1.1).upW (wordAt G r.cs r.lo seat y k.1.1): an equation of words of the library, at
               every native position and row. By SlotIs.lean's slot_is and SeatWord.lean's
               keptSym_seat; a kept member has no mask row (the typed structure's own test), so the
               word's other half has no symbol
WHAT IT IS FOR. The library's relation in front of the switch says: decW (sW k ‹open word›) ‹the
held OOD sample› = some ‹the member's part of the open word's message›. With this equation the word
under decW is the one under the table's pin at the kept seat (Johnson/Desc/Sound/MsgSig.lean's
PinAt): steps (a) and the words' half of (b) of three from that clause to the item pinKept.
LIMITS. SIX PREMISES: two mask rows · the front's frame is W₀ · W₀ lists kk at the member's place in
r.kept · kk's rows are the typed shape's main rows · the front reads something at some position ·
KeptSeat at kk.old, the typed shape, the seat and the main code's number of positions
(SeatWord.lean: a premise, shown at no real value). NOT HERE: that the held OOD sample is the
table's at the seat · one member at two lists · the table's extractor. pinKept IS NOT PAID. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.SlotIs
import Johnson.Top.H0.K2Caller.SeatWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (wordAt)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK} {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (p : K2.P2) (orc : Strs → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)

/-- **The kept slot of the made open word is the seat's word.** -/
theorem slot_word (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (W₀ : SwitchFrame) (y : Strs) (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (k : {a // (plainHd r H).cl a}) (kk : KeptPlace)
    (hk : W₀.kept[r.kept.idxOf k.1.1.val]? = some kk)
    (hr : kk.rows = (r.lo.get k.1.1).1.mainRows)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (K : KeptSeat G p t fx (orc y) y kk.old (r.lo.get k.1.1).1 (seat k.1.1)
      (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a)) :
    (plainHd r H).sW k (faAt r H p orc smp (t, fx, W₀) y).2.1.1 =
      ((sigOf r.cs r.lo).om k.1.1).upW (wordAt G r.cs r.lo seat y k.1.1) := by
  funext pN
  rcases pN with pN | pN
  · funext s
    obtain ⟨i, ⟨⟩⟩ := s
    have e : cMain r.cs (r.lo.get k.1.1).1 = (plainR r H).s.C :=
      H.hM 0 k.1.1 k.2.fst k.2.fst
    have hp : pN.val < 2 ^ (plainR r H).s.C.a := by rw [← e]; exact pN.isLt
    rw [slot_is p orc smp t fx W₀ y hm hW k i kk hk (by rw [hr]; exact i.isLt) q₀ h0 pN
      ⟨pN.val, hp⟩ rfl, keptSym_seat K i.val pN.val i.isLt pN.isLt]
    rfl
  · funext s
    have hlt : s.1.val < (r.lo.get k.1.1).1.maskRows := s.1.isLt
    have hz : (r.lo.get k.1.1).1.maskRows = 0 := H.h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
    exact absurd hlt (by omega)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.slot_word
