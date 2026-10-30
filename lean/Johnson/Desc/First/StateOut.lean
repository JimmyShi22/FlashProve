-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/StateOut.lean: NO FUNCTION OF Johnson/Desc/First/State.lean THAT TURNS THE
CARRIED RECORD S TURNS ITS FIELD `out` (the index masks' message, the pile, THE REPLY THAT WAS
HEARD). Small laws with their proofs, one a function, each by unfolding.

Why. The proof file's hypothesis on soundness wants that no block behind the reply's block turns
what was heard (`Block.Leaves`, Johnson/Desc/Sound/FoldHeard.lean, at the reading s.out.reply). A
block of the first chain is typed over S with the functions of State.lean. With these laws a kind's
files have `Leaves` of such a block by rewriting, wherever the block's own text writes `out`
nowhere, or writes another field of it.

Main names: `S.out_‹function›`, for: mark · putFork · putLink · putTl · putLook · hearLook · putLive
· enterLay · enterAtt · enterHead · openHead · enterFin · enterMem · leaveLink · owe · closed · pay
· back · call · callE · withReq. ALSO A CALL OF A ROUTINE OF `verify-on-bytes` (`S.call`, `S.callE`)
LEAVES `out`: the context that is laid around S holds no `out`, and `S.back` reads none back: what
the routine returns as its VALUE is the step's to lay.

Limits. Laws on State.lean's own functions alone: `enterLay` and
`enterHead` take the plan's tl there: a step that lays a record literal, or `{ s with out := … }`,
is not covered: that text is left to the step's own kind's files. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

theorem out_mark (s : S) (name : String) : (s.mark name).out = s.out := by
  unfold mark
  split <;> rfl

theorem out_putFork (s : S) (F : Fork) : (s.putFork F).out = s.out := by
  unfold putFork
  split <;> first | rfl | (split <;> rfl)

theorem out_putLink (s : S) (L : LinkCtx) : (s.putLink L).out = s.out := by
  unfold putLink
  split <;> first | rfl | (split <;> rfl)

theorem out_putTl (s : S) (tl : HTailF2) : (s.putTl tl).out = s.out := by
  unfold putTl
  split <;> first | rfl | (split <;> rfl)

theorem out_putLook (s : S) (g : Forest.Heard) : (s.putLook g).out = s.out := by
  unfold putLook
  split <;> first | rfl | (split <;> rfl)

theorem out_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).out = s.out := by
  unfold hearLook
  split <;> first
    | exact out_mark _ _
    | (split <;> first
        | rfl
        | exact out_mark _ _
        | (split <;> first | rfl | exact out_mark _ _))

theorem out_putLive (s : S) (c : ChainCheck) : (s.putLive c).out = s.out := by
  unfold putLive
  split <;> first | rfl | exact out_putLink _ _

theorem out_enterLay (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (s.enterLay L F tl).out = s.out := by
  unfold enterLay
  split <;> first | rfl | exact out_mark _ _

theorem out_enterAtt (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (s.enterAtt L F tl).out = s.out := by
  unfold enterAtt
  split <;> first | rfl | exact out_mark _ _

theorem out_enterHead (s : S) (tl : HTailF2) : (s.enterHead tl).out = s.out := by
  unfold enterHead
  split <;> first | rfl | exact out_mark _ _

theorem out_openHead (s : S) : s.openHead.out = s.out := by
  unfold openHead
  split <;> first | exact out_mark _ _ | (split <;> first | rfl | exact out_mark _ _)

theorem out_enterFin (s : S) : s.enterFin.out = s.out := by
  unfold enterFin
  split <;> first | rfl | exact out_mark _ _

theorem out_enterMem (s : S) : s.enterMem.out = s.out := by
  unfold enterMem
  split <;> first | rfl | exact out_mark _ _

theorem out_leaveLink (s : S) : s.leaveLink.out = s.out := by
  unfold leaveLink
  split <;> first | rfl | exact out_mark _ _

theorem out_owe (s : S) (rows : Nat) : (s.owe rows).out = s.out := by
  unfold owe
  split <;> first | rfl | exact out_mark _ _

theorem out_closed (s s' : S) (rows : Nat) (h : s.closed rows = some s') : s'.out = s.out := by
  unfold closed at h
  split at h
  · exact (Option.some.inj h) ▸ out_owe s rows
  · exact nomatch h

theorem out_pay (s s' : S) (rows : Nat) (h : s.pay rows = some s') : s'.out = s.out := by
  unfold pay at h
  split at h
  · split at h
    · exact (Option.some.inj h) ▸ rfl
    · exact nomatch h
  · exact nomatch h

theorem out_back (s : S) (c : Ctx) : (s.back c).out = s.out := rfl

theorem out_withReq (s : S) (req : Array UInt32) : (s.withReq req).out = s.out := rfl

/-- A call of a routine of `verify-on-bytes` leaves `out`. -/
theorem out_callE {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.callE P es rs cols b = .ok (a, s', k)) : s'.out = s.out := by
  unfold callE at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Except.ok.inj h)
      rw [← e]
      rfl
    · exact nomatch h

theorem out_call {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.call P es rs cols b = some (a, s', k)) : s'.out = s.out := by
  unfold call at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Option.some.inj h)
      rw [← e]
      rfl
    · exact nomatch h

end S

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.out_hearLook
#print axioms VerifiableInference.Desc.First.S.out_callE
#print axioms VerifiableInference.Desc.First.S.out_call
