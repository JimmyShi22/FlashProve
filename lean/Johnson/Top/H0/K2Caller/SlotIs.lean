-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SlotIs.lean: the code switch: THE KEPT SLOT OF THE MADE OPEN WORD,
AS THE LIBRARY READS IT (Cb/Ld/LdGroupSeg.lean's GHeld.sW), IS THE KEPT MEMBER's OWN WORD OFF THE
ORACLES.
  undoTab_unW  the way back from a member's main rows (Johnson/Top/H/MemberHeld.lean's undoTab,
               whose definition goes by a substitution): the word is the table, position by position
  plainHd      the library's choice of held messages at the typed structure r and the plain letters
  slotOf       the typed kept slot of a held member's row
  sW_wordOf    the held member k's word out of StrMade.lean's wordOf g has, at the native position p
               and the row i, g's long symbol at the same position, at slotOf k i
  slot_is      THE STATEMENT: at CarryK2.lean's faAt: that word's symbol at (p, i) is
               KeptLong.lean's keptSym, read in the field: main symbol number i of the column, at p,
               of the message that the frame lists as kept member number memK
WHAT IT IS FOR. The library's relation in front of the switch says: each held slot of the open word
decodes, with its held OOD sample, to its part of the open word's message. With this file the word
that decodes there is the kept member's own committed word, as the switch's text reads columns. It
closes step (a) of three from that clause to the table's item pinKept.
LIMITS. FIVE PREMISES: the carried rows have two mask rows · the front has the frame W₀ · the frame
lists kk as kept member number memK · i is a row of kk · the front reads something at SOME position
(LongThere.lean then has it at all). NOT HERE: (b) that keptSym's word is the word that the table's
own reader of a seat makes · (c) the table's extractor. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryK2
import Johnson.Top.H0.K2Hands.KeptLong
import Johnson.Top.H0.K2Hears.LongThere
import Johnson.Top.H.MemberHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

theorem undoTab_unW (C C' : Fmt.M1.Code) (a a' n : ℕ) (B : LdCode GE (Fin (2 ^ a')))
    (hS : ∀ p, IsEmpty (B.NS p)) (hJ : IsEmpty B.J) (hQ : IsEmpty B.Q) (e : C' = C)
    (f : ((ldOf C a).il (Fin n)).Word) (p : Fin (2 ^ C'.a)) (p' : Fin (2 ^ C.a))
    (hp : p'.val = p.val) (s : Fin n × Unit) :
    (undoTab C C' a a' n B hS hJ hQ e).unW f (.inl p) s = f p' s := by
  subst e
  obtain rfl : p' = p := Fin.ext hp
  rfl

section
variable (r : SwRow) (H : r.OK)

/-- The library's choice of held messages, at the plain letters. -/
noncomputable abbrev plainHd : GHeld (plainR r H).Sh (Letters.plain r H).kq :=
  heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ
    (Letters.plain r H).kq

variable {r H}

/-- The typed kept slot of a held member's row. -/
def slotOf (k : {a // (plainHd r H).cl a}) (i : Fin (r.lo.get k.1.1).1.mainRows) :
    (plainR r H).Kp :=
  ⟨⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩, i⟩

/-- **The kept slot of a made word.** -/
theorem sW_wordOf (k : {a // (plainHd r H).cl a})
    (g : (plainR r H).s.Ps → ((plainR r H).s.cKept (plainR r H).Kp).Aa → GE)
    (p : Fin (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a)) (p' : (plainR r H).s.Ps)
    (hp : p'.val = p.val) (i : Fin (r.lo.get k.1.1).1.mainRows) :
    (plainHd r H).sW k (wordOf (plainR r H).s (plainR r H).Kp g) (.inl p) (i, ()) =
      g p' (.inl (some (slotOf k i), ())) :=
  undoTab_unW _ _ _ _ _ _ _ _ _ _ _ p p' hp (i, ())

variable {Y : Type} (p : K2.P2) (orc : Y → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)

/-- **The kept slot of the made open word is the kept member's own word.** -/
theorem slot_is (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame)
    (y : Y) (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (k : {a // (plainHd r H).cl a}) (i : Fin (r.lo.get k.1.1).1.mainRows) (kk : KeptPlace)
    (hk : W₀.kept[memK (slotOf k i)]? = some kk) (hi : i.val < kk.rows)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (pN : Fin (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a)) (p' : (plainR r H).s.Ps)
    (hp : p'.val = pN.val) :
    (plainHd r H).sW k (faAt r H p orc smp (t, fx, W₀) y).2.1.1 (.inl pN) (i, ()) =
      readE (keptSym p t fx (orc y) kk.old i.val pN.val) := by
  have hs : (K2.longFront p t fx (orc y) p'.val).isSome = true := by
    rw [K2.longFront_there p t fx (orc y) (orc y) p'.val q₀]
    exact h0
  obtain ⟨seg, hseg⟩ := Option.isSome_iff_exists.1 hs
  have e := longFront_kept hm hseg hW (memK (slotOf k i)) kk i.val hk hi
  unfold faAt
  dsimp only
  rw [sW_wordOf k _ pN p' hp i, hseg, ← hp, ← e]
  rfl

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.sW_wordOf
#print axioms VerifiableInference.Desc.First.K2Caller.slot_is
