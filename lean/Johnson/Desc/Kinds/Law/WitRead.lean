--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/WitRead.lean: WHAT A SEGMENT READS OFF A WITNESS AT A MESSAGE's NUMBER
(Sound.readAt, Johnson/Desc/Sound/ReadAt.lean) IS THE WITNESS's OWN COMPONENT msg AT THAT NUMBER,
OUTSIDE THE PADS' PLACES. STATED AND PROVED: unfoldings. General in every letter.
Why. Wit is a plain structure (cells · tok · msg · pad): whoever holds a run's oracle messages MAKES
a witness by laying them in msg. The laws read a witness through readAt alone. This is the step from
the one to the other: with it the premises hy (Law/OwnCutWords.lean) and hm (Law/MaskWords.lean) are
statements on the component msg, that is: on what was laid.
  **readAt_msg**   readAt cs arr ms N k w n mask row place = w.msg n mask row place.
WHOSE. AT MAIN ROWS THIS IS ANOTHER HOUSE's LANDED LEMMA: Sound.readAt_offPad (that same file),
under namedOnce · GroupsSeated · OffPad: WHOEVER NEEDS MAIN ROWS ALONE CALLS THAT ONE. What is new
here: THE MASK ROWS TOO (the letter mask: the output head's mask row is read at mask := true, where
that lemma does not reach); and "named once" is not asked. (From seatTab on the two go the same
way.)
THE PREMISES, ALL ON PUBLIC LETTERS: hn: segment k's group has a tenant with the number n · hG:
every tenant of that group is the seat of a member of ms · hp: at no member of ms that sits in the
group with that number is (mask, row, place) a place of the pad (padB, Johnson/Desc/SeatAt.lean: a
test with code).
Limits. At a pad's place readAt gives the component pad of the copy's seat: nothing is said there.
NO VALUE IS EVALUATED. Nothing on soundness or on hiding.

-/
import Johnson.Desc.Sound.ReadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Sym

open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT seatOf numOf)

/-- **OUTSIDE THE PADS A SEGMENT READS THE WITNESS's OWN msg.** -/
theorem readAt_msg {Cells Tok : Type} (cs : OnBytes.Codes) (arr : Nat → Nat → Nat)
    (ms : List Mem) (N : Numbers) (k : Nat) (w : Wit Cells Tok MsgT) (n : Nat) (mask : Bool)
    (row place : Nat) (hn : ∃ x ∈ N.group k, arr x.1 x.2 = n)
    (hG : ∀ x ∈ N.group k, ∃ y ∈ ms, seatOf y = x)
    (hp : ∀ y ∈ ms, seatOf y ∈ N.group k → numOf arr y = n →
      VerifiableInference.Desc.padB cs (y.1.l.get y.2).1 mask row place = false) :
    Sound.readAt cs arr ms N k w n mask row place = w.msg n mask row place := by
  unfold Sound.readAt
  cases hf : (N.group k).find? fun x => arr x.1 x.2 == n with
  | none =>
    obtain ⟨x, hx, e⟩ := hn
    exact absurd (beq_iff_eq.2 e) (List.find?_eq_none.1 hf x hx)
  | some x =>
    have hx : x ∈ N.group k := List.mem_of_find?_eq_some hf
    have hxn : arr x.1 x.2 = n :=
      eq_of_beq (List.find?_some (p := fun x : Nat × Nat => arr x.1 x.2 == n) hf)
    show Sound.seatTab cs arr ms w x mask row place = w.msg n mask row place
    unfold Sound.seatTab
    cases hg : ms.find? fun y => Decidable.decide (seatOf y = x) with
    | none =>
      obtain ⟨y, hy, e⟩ := hG x hx
      exact absurd (decide_eq_true e) (List.find?_eq_none.1 hg y hy)
    | some y =>
      have hy : y ∈ ms := List.mem_of_find?_eq_some hg
      have hs : seatOf y = x :=
        of_decide_eq_true
          (List.find?_some (p := fun y : Mem => Decidable.decide (seatOf y = x)) hg)
      have hny : numOf arr y = n := by
        show arr (seatOf y).1 (seatOf y).2 = n
        rw [hs, hxn]
      have hin : seatOf y ∈ N.group k := by
        rw [hs]
        exact hx
      have hpad : ¬ VerifiableInference.Desc.padB cs (y.1.l.get y.2).1 mask row place = true := by
        rw [hp y hy hin hny]
        exact Bool.false_ne_true
      show Sound.memTab cs arr w y mask row place = w.msg n mask row place
      unfold Sound.memTab Wit.tab
      rw [if_neg hpad, hny]

end VerifiableInference.Desc.Kinds.Head.Law.Sym

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Sym.readAt_msg
