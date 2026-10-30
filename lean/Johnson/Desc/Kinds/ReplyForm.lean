-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/ReplyForm.lean: THE NEXT TOKEN, A VARIANT OF THE KIND, BESIDE THE TEXT THAT RIDES
(ReplyKind.lean, ReplyBlock.lean: not a letter of them turns): the block asks ONE TEST MORE AT ITS
OWN ROUND: "e = T, or the heard token is 0". It shows nothing by itself. Definitions with code; no
theorem here. In a model of three steps (this decide; any rest that leaves the seat's reply and e; a
last test whose yes holds the new test's) the verdict is the same with either text: that is proved
in Law/ReplyFormProof.lean (sameVerdictAny), not of FileDescription.run and not of
verify().
From that file's own head, to the letter:
«WHAT IT DOES NOT SHOW. IT SPEAKS OF A MODEL OF THREE STEPS (decide ; rest ; last), NOT OF
FileDescription.run AND NOT OF verify(): owed before it speaks of a fold: that the fold, cut at this
block's place, is such a rest; hrest; hlast at the fold's own last test, at the same T and e.
That the other blocks of a fold leave the seat and e: a premise
(hrest): left to each kind's files. The refusals' NAMES differ: where the variant refuses at the
round, the text that rides refuses at the end. Nothing on soundness.»

WHY. Where the last position is not checked (e < T) no claim of the head reads the next token; the
format asks that it be 0 there. The text that rides asks so at the very end alone, of the client's
token (Reply.fin: reqForm), which it also holds against the heard one. Here the heard token itself
is asked at the round at which it is heard: so a statement about the block alone can say "y = 0
where e < T". No byte of the format turns: the same round, the same entry of the plan.
T: a number of the plan. e: the request's, read off the carried record: where, the seat says.

-/
import Johnson.Desc.Kinds.ReplyBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Reply

variable {S : Type}

/-- The new test's name. -/
def formName : String := "the token is 0 where the last position is not checked"

/-- DECIDES: ReplyKind.lean's decideE, by name; then, on the record that it leaves: e = T, or the
token in the seat is 0. -/
def decideForm (V T : Nat) (L : Seat S) (e : S → Nat) (s : S) (rs : List Fmt.RoundView) :
    Except String S :=
  (decideE V L s rs).bind fun s' =>
    if e s' == T || token L s' == some 0 then .ok s' else .error formName

/-- The kind. Its parameters: V, the number of vocabulary entries, and T, the number of positions.
All but decide is ReplyBlock.lean's kind. -/
def kindForm {Cl : Type} (L : Seat S) (e : S → Nat) (link piece : Nat) : Kind (Nat × Nat) S Cl :=
  fun p => { kind L link piece p.1 with decide := fun s rs _ => decideForm p.1 p.2 L e s rs }

end VerifiableInference.Desc.Kinds.Reply
