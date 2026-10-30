-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/TokTerms.lean: THE TOKEN'S THREE LETTERS AS TERMS: ONE TERM EACH FOR THE TOWER
(`hidAtSeat`'s tokV; the end theorems' f and tokOf), THE TABLE'S EXTRACTOR AT K7'S ROW (`extQ`,
`extQAt`: tokOf) AND headPartK6 (tokH). Definitions with code and two small lemmas;
light imports.
  `tokOfHeard a` : ℕ := the number of the token that the record heard, else 0. (Tok := ℕ.)
  `tokVOf n` : Fin ppref.V := n as a token of the reference's vocabulary, else 0.
  `tokHOf a` := tokVOf (tokOfHeard a).
  `replyTok_is_heardTok`: the state's own reader `S.replyTok?` and `S.heardTok?`
    (Johnson/Desc/First/HeardAsked.lean) are one: in the state the
    heard element lies at one place.
  `tokHOf_of_heard`: where a token's number n below the vocabulary's size was heard, tokHOf is it.
THE TWO SILENT DEFAULTS (else 0) ARE IDLE WHEREVER A TOKEN BELOW THE VOCABULARY'S SIZE WAS HEARD:
behind K7's yes, by that kind's own test. WHERE NOTHING WAS HEARD THEY ANSWER 0 IN SILENCE: whoever
reads tokOfHeard or tokHOf at a record in front of K7's block reads that 0: THAT NO ITEM OF THE
TABLE DOES SO IS SAID BY NOTHING HERE.
-/
import Johnson.Desc.First.HeardAsked
import Johnson.Flat.PubReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Inst.Model
open VerifiableInference.Desc

/-- The number of the token that the record heard, else 0. -/
def tokOfHeard {P : Type} (a : P × First.S) : ℕ := a.2.heardTok?.getD 0

/-- A number as a token of the reference's vocabulary, else 0. -/
def tokVOf (n : ℕ) : Fin ppref.V := if h : n < ppref.V then ⟨n, h⟩ else ⟨0,
OnBytes.Flat.ppref_V_pos⟩

/-- The heard token as a token of the reference's vocabulary. -/
def tokHOf {P : Type} (a : P × First.S) : Fin ppref.V := tokVOf (tokOfHeard a)

/-- The state's own reader of the reply's token and `heardTok?` are one. -/
theorem replyTok_is_heardTok (s : First.S) : s.replyTok? = s.heardTok? := rfl

/-- Where a token's number below the vocabulary's size was heard, `tokHOf` is it. -/
theorem tokHOf_of_heard {P : Type} (a : P × First.S) (n : ℕ) (hn : a.2.heardTok? = some n)
    (hV : n < ppref.V) : tokHOf a = ⟨n, hV⟩ := by
  unfold tokHOf tokOfHeard tokVOf
  rw [hn]
  show (if h : n < ppref.V then (⟨n, h⟩ : Fin ppref.V) else ⟨0, OnBytes.Flat.ppref_V_pos⟩) = ⟨n, hV⟩
  rw [dif_pos hV]

end P5J

#print axioms P5J.replyTok_is_heardTok
#print axioms P5J.tokHOf_of_heard
