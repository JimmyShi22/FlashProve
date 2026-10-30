-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/StateHeard.lean: THE REPLY THAT WAS HEARD, AS A READING OF THE CARRIED RECORD S
(Johnson/Desc/First/State.lean), by name; and small laws with their proofs: which functions of
State.lean leave that reading, and what the last test's yes says of it.

Why. The proof file's hypothesis on soundness wants one reading h of the first chain's record such
that the reply's block lays h from its own rounds, no later block turns h, and the last test
compares h with what is asked (`FileDescription.Hears`, Johnson/Desc/Sound/FoldHeard.lean). THE
HEARD ELEMENT LIES AT ONE PLACE: the head's own part has no field
`plain`; the reply's place lays `out.reply` itself, and the last test reads `out.reply`.

`S.heard`: `out.reply`.


The laws.
  `S.heard_‹function›`: the function leaves the reading, at every record: mark · putFork · putLink ·
    putTl · putLook · hearLook · putLive · enterLay · enterAtt · enterFin · enterMem · leaveLink ·
    owe · closed · pay · back · call · callE · withReq.
  `S.heard_of_same`: a change of the record that leaves `here` and `out` leaves the reading (`out`
    alone is spent).
  `S.heard_openHead`: `openHead` leaves it. Its premise stands in the statement and is
    not spent: it holds by definition.
  `S.heard_of_finAsked`: where `S.finAsked asked` says yes, what was heard is asked.

Limits. Laws on State.lean's own functions alone: a
step that lays a record literal, `{ s with out := … }`, is not covered: that text is left to the
step's own kind's files. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

/-- **The reply that was heard.** -/
def heard (s : S) : Option E := s.out.reply

/-- A change of the record that leaves `here` and `out` leaves the reading. -/
theorem heard_of_same (s s' : S) (_hh : s'.here = s.here) (ho : s'.out = s.out) :
    s'.heard = s.heard := by
  unfold heard
  rw [ho]

theorem heard_mark (s : S) (name : String) : (s.mark name).heard = s.heard := by
  unfold mark
  split <;> rfl

theorem heard_putFork (s : S) (F : Fork) : (s.putFork F).heard = s.heard := by
  unfold putFork
  split <;> first | rfl | (split <;> rfl)

theorem heard_putLink (s : S) (L : LinkCtx) : (s.putLink L).heard = s.heard := by
  unfold putLink
  split <;> first | rfl | (split <;> rfl)

theorem heard_putTl (s : S) (tl : HTailF2) : (s.putTl tl).heard = s.heard := by
  unfold putTl
  split <;> first | rfl | (split <;> rfl)

theorem heard_putLook (s : S) (g : Forest.Heard) : (s.putLook g).heard = s.heard := by
  unfold putLook
  split <;> first | rfl | (split <;> rfl)

theorem heard_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).heard = s.heard := by
  unfold hearLook
  split <;> first
    | exact heard_mark _ _
    | rfl
    | (split <;> first
        | exact heard_mark _ _
        | rfl
        | (split <;> first | exact heard_mark _ _ | rfl))

theorem heard_putLive (s : S) (c : ChainCheck) : (s.putLive c).heard = s.heard := by
  unfold putLive
  split <;> first | rfl | exact heard_putLink _ _

theorem heard_enterLay (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (s.enterLay L F tl).heard = s.heard := by
  unfold enterLay
  split
  · rfl
  · exact heard_mark _ _

theorem heard_enterAtt (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (s.enterAtt L F tl).heard = s.heard := by
  unfold enterAtt
  split
  · rfl
  · exact heard_mark _ _

theorem heard_enterFin (s : S) : s.enterFin.heard = s.heard := by
  unfold enterFin
  split
  · rfl
  · exact heard_mark _ _

theorem heard_enterMem (s : S) : s.enterMem.heard = s.heard := by
  unfold enterMem
  split <;> first | exact heard_mark _ _ | rfl

theorem heard_leaveLink (s : S) : s.leaveLink.heard = s.heard := by
  unfold leaveLink
  split
  · rfl
  · exact heard_mark _ _

theorem heard_owe (s : S) (rows : Nat) : (s.owe rows).heard = s.heard := by
  unfold owe
  split <;> first | rfl | exact heard_mark _ _

theorem heard_closed (s s' : S) (rows : Nat) (h : s.closed rows = some s') :
    s'.heard = s.heard := by
  unfold closed at h
  split at h
  · exact (Option.some.inj h) ▸ heard_owe s rows
  · exact nomatch h

theorem heard_pay (s s' : S) (rows : Nat) (h : s.pay rows = some s') : s'.heard = s.heard := by
  unfold pay at h
  split at h
  · split at h
    · exact (Option.some.inj h) ▸ rfl
    · exact nomatch h
  · exact nomatch h

theorem heard_back (s : S) (c : Ctx) : (s.back c).heard = s.heard := rfl

theorem heard_withReq (s : S) (req : Array UInt32) : (s.withReq req).heard = s.heard := rfl

/-- A call of a routine of `verify-on-bytes` leaves the reading. -/
theorem heard_callE {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.callE P es rs cols b = .ok (a, s', k)) : s'.heard = s.heard := by
  unfold callE at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Except.ok.inj h)
      rw [← e]
      rfl
    · exact nomatch h

theorem heard_call {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.call P es rs cols b = some (a, s', k)) : s'.heard = s.heard := by
  unfold call at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Option.some.inj h)
      rw [← e]
      rfl
    · exact nomatch h

/-- `openHead` leaves the reading. The premise holds by definition. -/
theorem heard_openHead (s : S) (_h : s.out.reply = s.heard) : s.openHead.heard = s.heard := by
  unfold openHead
  split
  · split
    · exact heard_mark _ _
    · rfl
  · exact heard_mark _ _

/-- **Where the last test says yes, what was heard is what is asked.** -/
theorem heard_of_finAsked (asked : E) (s : S) (h : s.finAsked asked = true) :
    s.heard = some asked := by
  unfold finAsked at h
  simp only [Bool.and_eq_true] at h
  have h₂ : (s.out.reply == some asked) = true := by first | exact h.2 | exact h.1.2
  exact eq_of_beq h₂

end S

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.heard_hearLook
#print axioms VerifiableInference.Desc.First.S.heard_leaveLink
#print axioms VerifiableInference.Desc.First.S.heard_callE
#print axioms VerifiableInference.Desc.First.S.heard_openHead
#print axioms VerifiableInference.Desc.First.S.heard_of_finAsked
