-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPins.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE PINS AND THE PROMISE OF
ITS ROW, FROM AND TO THE FORMS OF Johnson/Desc/Sound/MsgSig.lean, WHERE THE RECORD MAY LACK A
SAMPLE.

The laws of Johnson/Desc/First/K8/LawAtFrame.lean to LawRow.lean read the samples off the carried
record by a TOTAL letter (`smpOf : S → (sigOf cs l).Smp`): the proved block's statement holds a
sample for every member. The table of joints reads them by a PARTIAL one (`smp`, member by member:
nothing where the record does not hold the member's sample), and says "the record holds it" inside
each pin (`PinAt`, `CfAt`, `PinSig`, `CfSig`). Here the total letter is MADE of the partial one:
  `totalOf smp σ0`: the record's sample where it holds one; else σ0's: a made-up filling, which no
    statement below reads where the pins or the promise hold.
  `totalOf_put`: it passes the block's one writing, if the partial letter does.
  `pinsAt_of_pinSig`: all members pinned in the table's form ⇒ the pins of the kind's row
    (`PinsAt`).
  `pinSig_of_pinsAt`: and back, where the record holds every member's sample, the seats fit and
    every leaf is shown.
  `cf_of_cfSig`: the table's promise at all members ⇒ the library's "no collision" at the total
    letter: the first half of the condition of the kind's row (`lay_onA`).
Statements and proofs; by `pinSig_over`, `pinSig_of_over`, `cfSig_over` of MsgSig.lean.
Limits. ONE signature for all members of the kind's caller; the table has a pin for each sending.
`smp` stays a letter. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Cb OnBytes.Model OnBytes.Maker Johnson.Pack VerifiableInference.Desc.Sound

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (smp : S → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp) (σ0 : (sigOf cs l).Smp)

/-- The total letter, made of the partial one. -/
def totalOf (s : S) : (sigOf cs l).Smp := fun i => (smp s i).getD (σ0 i)

theorem totalOf_eq (s : S) (σ : (sigOf cs l).Smp) (h : ∀ i, smp s i = some (σ i)) :
    totalOf cs l smp σ0 s = σ := by
  funext i
  unfold totalOf
  rw [h i]
  rfl

/-- It passes the block's one writing, if the partial letter does. -/
theorem totalOf_put
    (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
      smp (s.putTl { tl with cfF := mm, cfFirst := f }) = smp s)
    (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat) (h : s.tl? = some tl) :
    totalOf cs l smp σ0 (s.putTl { tl with cfF := mm, cfFirst := f }) = totalOf cs l smp σ0 s := by
  unfold totalOf
  rw [hs s tl mm f h]

variable (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {Cells Tok : Type} {Xi : Type}
  (G : FileDescription Xi) (F : Frame)

/-- All members pinned in the table's form give the pins of the kind's row. -/
theorem pinsAt_of_pinSig (a : S × F.E.Str) (w : Wit Cells Tok MsgT)
    (h : PinSig G cs l seat' smp arr (fun _ => True) a.1 (strsOf F a.2) w) :
    PinsAt cs l seat' arr G (totalOf cs l smp σ0) F a w := by
  obtain ⟨σ, hσ, hd⟩ := pinSig_over G cs l seat' smp arr a.1 (strsOf F a.2) w h
  unfold PinsAt
  rw [totalOf_eq cs l smp σ0 a.1 σ hσ]
  exact hd

/-- And back. -/
theorem pinSig_of_pinsAt (a : S × F.E.Str) (w : Wit Cells Tok MsgT)
    (hS : SeatFits G cs l seat') (σ : (sigOf cs l).Smp) (hσ : ∀ i, smp a.1 i = some (σ i))
    (hsh : ∀ i, ShownAt G cs l seat' (strsOf F a.2) i)
    (h : PinsAt cs l seat' arr G (totalOf cs l smp σ0) F a w) :
    PinSig G cs l seat' smp arr (fun _ => True) a.1 (strsOf F a.2) w := by
  unfold PinsAt at h
  rw [totalOf_eq cs l smp σ0 a.1 σ hσ] at h
  exact pinSig_of_over G cs l seat' smp arr a.1 (strsOf F a.2) w hS σ hσ hsh h

/-- The table's promise at all members gives the library's "no collision" at the total letter. -/
theorem cf_of_cfSig (a : S × F.E.Str)
    (h : CfSig G cs l seat' smp (fun _ => True) a.1 (strsOf F a.2)) :
    (sigOf cs l).CF (totalOf cs l smp σ0 a.1) (wordsOf G cs l seat' (strsOf F a.2)) := by
  obtain ⟨σ, hσ, hc⟩ := cfSig_over G cs l seat' smp a.1 (strsOf F a.2) h
  rw [totalOf_eq cs l smp σ0 a.1 σ hσ]
  exact hc

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.totalOf_put
#print axioms VerifiableInference.Desc.First.K8.pinsAt_of_pinSig
#print axioms VerifiableInference.Desc.First.K8.pinSig_of_pinsAt
#print axioms VerifiableInference.Desc.First.K8.cf_of_cfSig
