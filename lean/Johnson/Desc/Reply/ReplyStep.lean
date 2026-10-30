-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reply/ReplyStep.lean: the round REPLY of a proof file's first chain, as the
description's own decision sees it: one step and one gate, and the test on the request's form beside
which the gate stands; with code. Definitions and tests at made-up rounds. No theorem.

What it is for. The description of the proof file's protocol decides on three views
(`reductionOfWholeFile`, OnBytes/Maker/Whole.lean: `run : Xi → View → View → View → Bool`). Its decision on the
first view is to be one fold of steps, each from what is carried and a stretch of the view's rounds
to what is carried next. In the round REPLY the prover names the next token in the clear: one field
element; the verifier draws nothing (docs/format/10-proof-file.md, the table's row REPLY). The first
query of the chain binds the request with 0 in the reply's place, so the user's reply is held
against the proof at one place alone: the comparison behind all links.

Main names:
  `readReply r`: the one element that the round r holds. None unless the round's items are exactly
    one element (a view's round holds no roots: they are left out when a view is made) and the round
    draws nothing: no element, no position, no matrix entry, no seal's
    digest (a round has one only if its kind is "sealed": `drawDigest`, Fmt/Rules6Round.lean).
  `isToken V h`: h is an entry of a vocabulary of V tokens, as an element of the field: its second
    and third coordinates are the word 0, its first is a number below V.
  `stepReply V r`: THE STEP. The element that is carried from here on. None where `readReply` gives
    none or the element is no token.
  `tokOf h`: the token that a carried element is. Whatever reads the carried element as a token
    reads it through this and through nothing else.
  `replyGate V heard y`: THE GATE. True if an element has been heard, it is a token, and its number
    is y, the user's token. Numbers are compared as natural numbers: no word is made of y.
  `reqForm T r e y`: the tests 3 and 4 of the five of docs/format/FORMAT.md, 12.2, on the user's two
    files: r < e, e ≤ T, and y = 0 if e < T. Tests 1 and 2 (the files' lengths) and test 5 on the T
    tokens are not here: the same reading of the user's files owes them.
V, T, r, e and y are arguments. Which numbers of the plan and of the user's files they are is said
by whoever calls: no definition here takes a plan, picks the round out of the plan's entries, or
reads r, e and y out of the user's two files.

How it is meant to be laid (not done here). What is carried has one field for this value, an
`Option E`: `none` in front of the round, `stepReply`'s value behind it. The field's form follows a
working paper of this project on the first chain's carried state, which no file of
this library holds: there it is `walk.reply`, "from the head's link on" (the round REPLY is that
link's first). In the state as it is typed, it is `S.out.reply`
(Johnson/Desc/First/State.lean). Where `stepReply` gives none
the fold must END with a no: it must not lay that `none` into the field and go on, since there
`none` means "not yet heard".
THE RULE: all three chains' folds, and the test on the rounds without a challenge, take what is read
of the user's files WITHOUT THE REPLY. None of them reads the user's reply. The gate and `reqForm`
alone do. The text of the decision, with r, e, y, the tokens and the hashed bytes as fields of ONE
value, so that no two readers can be fed two values: not in this file.
Which round: none of these definitions picks it.

The two cases of a request. If the window's last position is covered, the token is the model's
choice there: the head's steps lay `tokOf` of the carried element at the window's last place, and
the gate holds it against the user's. If not, no step reads the carried element: the gate and the
test on the request's form bind it together.

Why `reqForm` stands here. Where the window's last position is not covered, let the prover say 1 and
the user claim 1. The gate says yes, and no step reads the token: so nothing in the fold can refuse.
The one bar is the request's form: y = 0 there. It must be tested INSIDE the verifier, where it
reads the user's two files, not by a parser in front of it, and ON THE TOKEN FILE's OWN WORD.
`WellFormed` in the type of the requests (Johnson/Flat/LedgerClaim.lean) IS NO SUCH BAR: the
builder off the two files (`insReq`, Johnson/Top/InsReq.lean) leaves the token file's word out where
the last position is not covered, so that its request has y = 0 whatever the file says; the
tests show it (Johnson/Top/InsReqRun.lean, "where the two part"). At a well-formed request `reqForm`
is true by the type and tests nothing.
From that file's head, word for word: «3. WHERE THE TWO PART. At e before the window's end and a
reply that is not 0 the reader refuses, and insReq returns the instance with y = 0: the three lists
of OnBytes/K/Tokens.lean do not hold the reply there. At a request file of another length (10
tokens, r = 3, e = 10) the reader refuses, and insReq returns an instance with the reply as token 10
of the window. So "insReq returns" says less than "the reader takes the files": every law on insReq
has the reader's return as a premise, or is an equation for all statements.»

Limits. Nothing says that a fold with this step accepts a real proof: none is written. That each
word of the element is below the field's prime is not tested here: that test stands in front of all
steps, on every item of the three views. In the typed instance the user's token is below V by its
type (`Instance.y : Fin P.V`, Inst/Model/Program.lean); the gate does not lean on that: where it
says yes, y is below V. The tests below are at made-up rounds. Nothing on soundness, on an honest
prover or on hiding.

Where the text comes from. The round's shape: docs/format/10-proof-file.md, the table's row REPLY.
The tests on the request's form: docs/format/FORMAT.md, 12.2. The carried field's form: the working
paper named above. The code calls `E.ofTriple` and `E.mk3` (OnBytes/Base.lean) and the records of
Fmt/View.lean, and nothing else. Kind K7's block (Johnson/Desc/Kinds/ReplyKind.lean) calls
`readReply`, `isToken`, `tokOf`, `replyGate` and `reqForm`.

Terms: lean/GLOSSARY.md.
-/
import Fmt.View
import OnBytes.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.Reply

/-- The one element that the round holds. None unless its items are exactly one element and it draws
no element, no position, no matrix entry and no seal's digest. -/
def readReply (r : Fmt.RoundView) : Option E :=
  match r.vals with
  | [.e x] =>
    if r.drawn.elems.isEmpty && r.drawn.poss.isEmpty && r.drawn.trits.isEmpty &&
        r.drawn.digest.isNone then
      some (E.ofTriple x)
    else none
  | _ => none

/-- The element is an entry of a vocabulary of V tokens. -/
def isToken (V : Nat) (h : E) : Bool := h.c1 == 0 && h.c2 == 0 && decide (h.c0.toNat < V)

/-- **The step at the round REPLY**: the element that is carried from here on. -/
def stepReply (V : Nat) (r : Fmt.RoundView) : Option E := (readReply r).filter (isToken V)

/-- The token that a carried element is. -/
def tokOf (h : E) : Nat := h.c0.toNat

/-- **The gate behind the last link**: an element has been heard, it is a token, and its number is
the user's token y. -/
def replyGate (V : Nat) (heard : Option E) (y : Nat) : Bool :=
  match heard with
  | some h => isToken V h && tokOf h == y
  | none => false

/-- The form of the user's two files, as far as it bears on the reply: the checked positions are r
up to and not including e, within the window of T positions; where the last position is not checked
the user's token is 0. -/
def reqForm (T r e y : Nat) : Bool := decide (r < e) && decide (e ≤ T) && (e == T || y == 0)

/-! ## Tests at made-up rounds -/

/-- A round that draws nothing, with the given items. -/
def quiet (vals : List Fmt.ItemValue) : Fmt.RoundView := ⟨vals, ⟨[], [], [], none⟩⟩

-- The honest course: token 7 of a vocabulary of 10.
#guard stepReply 10 (quiet [.e (7, 0, 0)]) == some (E.mk3 7 0 0)
#guard (stepReply 10 (quiet [.e (7, 0, 0)])).map tokOf == some 7
#guard replyGate 10 (stepReply 10 (quiet [.e (7, 0, 0)])) 7
-- The window's last position not covered: the token is 0 on both sides.
#guard replyGate 10 (stepReply 10 (quiet [.e (0, 0, 0)])) 0
-- (c1) the round's element turned, the user's token as it was: the gate says no.
#guard !replyGate 10 (stepReply 10 (quiet [.e (8, 0, 0)])) 7
-- (c2) the user's token turned, the round as it was: the gate says no.
#guard !replyGate 10 (stepReply 10 (quiet [.e (7, 0, 0)])) 6
-- (c3) both turned alike: THE GATE SAYS YES. This can be refused only where the claims that the
-- head's rounds leave are tested: at the ends of the first and of the second chain.
#guard replyGate 10 (stepReply 10 (quiet [.e (8, 0, 0)])) 8
-- (c4) no token: a coordinate beyond the first is not 0; the number is not below V.
#guard stepReply 10 (quiet [.e (7, 1, 0)]) == none
#guard stepReply 10 (quiet [.e (7, 0, 1)]) == none
#guard stepReply 10 (quiet [.e (10, 0, 0)]) == none
-- (c5) the round's shape: no item; two items; an item of another kind; a round that draws an
-- element, a position, a matrix entry, a seal's digest.
#guard stepReply 10 (quiet []) == none
#guard stepReply 10 (quiet [.e (7, 0, 0), .e (7, 0, 0)]) == none
#guard stepReply 10 (quiet [.answer (7, 0, 0)]) == none
#guard stepReply 10 ⟨[.e (7, 0, 0)], ⟨[(1, 0, 0)], [], [], none⟩⟩ == none
#guard stepReply 10 ⟨[.e (7, 0, 0)], ⟨[], [1], [], none⟩⟩ == none
#guard stepReply 10 ⟨[.e (7, 0, 0)], ⟨[], [], [1], none⟩⟩ == none
#guard stepReply 10 ⟨[.e (7, 0, 0)], ⟨[], [], [], some ByteArray.empty⟩⟩ == none
-- Nothing heard: the gate says no, also at the token 0.
#guard !replyGate 10 none 0
-- The user's token beyond the words' range: 7 + 2 ^ 64 is not 7.
#guard !replyGate 10 (stepReply 10 (quiet [.e (7, 0, 0)])) (7 + 2 ^ 64)
-- The gate tests the form by itself: an element that is no token is refused whatever y is.
#guard !replyGate 10 (some (E.mk3 12 0 0)) 12
#guard !replyGate 10 (some (E.mk3 7 1 0)) 7
-- The request's form. The last position checked: any token. Not checked: the token 0 alone.
#guard reqForm 64 60 64 1
#guard reqForm 64 15 47 0
-- THE TOOTH: the last position is not checked, and prover and user both say 1. The gate says yes;
-- the form says no.
#guard replyGate 10 (stepReply 10 (quiet [.e (1, 0, 0)])) 1
#guard !reqForm 64 15 47 1
-- No position is checked; the window is overrun (y = 0: the clause e ≤ T alone says no).
#guard !reqForm 64 47 47 0
#guard !reqForm 64 48 47 0
#guard !reqForm 64 60 65 0

end OnBytes.Desc.Reply

#print OnBytes.Desc.Reply.readReply
#print OnBytes.Desc.Reply.stepReply
#print OnBytes.Desc.Reply.replyGate
#print OnBytes.Desc.Reply.reqForm
