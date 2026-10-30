-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7TokTerms.lean.
WHAT IT DOES NOT SHOW. No soundness. That a token was heard at the record: not asked and not said:
the equation holds at every record, at the terms' silent default (0) too. That the composed filling
is laid at these terms: not here.
LETTERS. No "there is". dec: the reading's decoder: the reading's token does not hang on it.
OBJECT. The table's files' three terms for the token (P5J/TokTerms.lean: tokOfHeard, tokVOf,
tokHOf; the witness's token is a number) and their reading of a witness off the seats
(P5J/MeansQ.lean: hidAtSeat).
USER. The field "tok" of the bill of the next token's tie (Law/K7Seated.lean: K7Rest;
Law/K7Tied.lean: K7Due); at the composed meaning's reading, with the one decoder:
Law/K7AtMgAll.lean: tok_terms_one.
WHAT IT IS. AT THESE TERMS THE TOKEN THAT THE READING FINDS IN A WITNESS WHOSE TOKEN IS tokOfHeard b
IS tokHOf b: BY DEFINITION: the reading's token is tokVOf of the witness's, and tokHOf is tokVOf
after tokOfHeard.
  tok_terms         the equation.
A search (statements with the reading's token on one side of an equation, over
the table's files, K6's and K7's files and Goal/: 792 files, not held against what
ships) found one statement, which takes the equation
as a premise (Law/HeadCutsK6.lean: heard_to_calls).

-/
import Mathlib
import Johnson.P5J.TokTerms
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated)

variable {rows cols : Nat} {P : Type} (Wp : OnBytes.Model.Verify.Public) (cs : OnBytes.Codes)
  (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (req : P × S → P5J.TReq)
  (dec : P × S → Strs → Option (Fin rows → Fin cols → GE)) (hSN : SeatsNamed arr N s seat)
  (hGS : GroupsSeated msR N)

/-- At the reading off the seats. -/
theorem tok_terms (b : P × S) (w : Wit (Fin rows → Fin cols → GE) Nat MsgT) :
    ((P5J.hidAtSeat Wp cs arr msR N s seat P5J.tokVOf req dec hSN hGS).hid
      ⟨w.cells, P5J.tokOfHeard b, w.msg, w.pad⟩).tok = P5J.tokHOf b := rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tok_terms
