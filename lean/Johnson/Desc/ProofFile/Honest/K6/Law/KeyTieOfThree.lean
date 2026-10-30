-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/KeyTieOfThree.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE
VERIFIER'S LETTERS AT A STATE ARE THOSE THAT THE PROVER'S SMALL INPUT MAKES (the field "keyTie" of
K6Script, Honest/K6/Law/OutAtThread.lean), FROM THREE EQUATIONS: the request, the token, the
lookup's points.
WHAT IT IS NOT. CONDITIONAL: the three equations are premises, shown here of no state; so are the
three tests under which the verifier's letters are read (K6Front's field letters has them).
keyTie_of_three takes K6Front whole, since its caller holds it; of it the test on the points alone
is spent (the points and the token come again from the third and the second equation), and the
letter r is idle. It joins: both sides' letters are made by one text (the library's given;
Honest/K6/Ask.lean: HeadAsk.given) of the public numbers, a request, a token and two points. Nothing
on soundness, on completeness or on what a proof hides. The frame of the honest side is not
imported.
WHO IS MEANT TO PAY THE THREE. request: both are the library's requestOf, at the state and at the
first state, and that reads the state's words of the request alone: that these words are kept.
token: that the heard reply is the instance's. points: that the state's points are the functions of
the challenges heard that the prover computes: the lookups' border.
  given_is_ask      at a seat L and a state s.
  keyTie_of_three   the field's sentence at the head's seat, at a ready state (K6Front).
CALLED: given_of_parts (Law/K6GivenOfLeft.lean); of the library: given_ok.

-/
import Johnson.Desc.ProofFile.Honest.K6.Ask
import Johnson.Desc.K6.Honest.Law.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Seat Head.Law.readsOf Reply.token)
open VerifiableInference.Desc.Kinds.Head (parOf given seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (PointsOk workOf K6Front given_of_parts)

/-- **The verifier's letters are the prover's**, where the request, the token and the lookup's
points are. z, y0: what the seat reads of the state. -/
theorem given_is_ask {St : Type} (p : Head.Par) (L : Head.Seat St) (s : St) (a : HeadAsk)
    (front : List Fmt.Drawn) (z : Point × (Nat → Point)) (y0 : Nat) (hz : L.lookup s = some z)
    (hy : Reply.token L.toSeat s = some y0) (hP : @PointsOk p.sizes p.floor z.1 z.2)
    (e1 : a.request = L.request s) (e2 : a.y = y0) (e3 : a.lookup front = z) :
    given p L s = .ok (a.given p front) := by
  obtain ⟨g, hg⟩ := given_of_parts p L s z y0 hz hy hP
  obtain ⟨z', y', hz', hy', _, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok p L s g hg
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  obtain rfl : y0 = y' := Option.some.inj (hy.symm.trans hy')
  rw [hg, e]
  unfold HeadAsk.given
  rw [e1, e2, e3]

/-- **K6Script's keyTie at one state**, at the head's seat. -/
theorem keyTie_of_three (W : OnBytes.Model.Verify.Public) {r : Nat} {s : S} (R : K6Front W r s)
    (a : HeadAsk) (front : List Fmt.Drawn)
    (e1 : a.request = (seatAt W.hS (Head.Law.readsOf W)).request s)
    (e2 : Reply.token (seatAt W.hS (Head.Law.readsOf W)).toSeat s = some a.y)
    (e3 : (seatAt W.hS (Head.Law.readsOf W)).lookup s = some (a.lookup front)) :
    given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s =
      .ok (a.given (parOf W.hS (workOf W)) front) := by
  obtain ⟨z, y0, hz, hy, hP⟩ := R.letters
  exact given_is_ask _ _ s a front z y0 hz hy hP e1
    (Option.some.inj (e2.symm.trans hy)) (Option.some.inj (e3.symm.trans hz))

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.given_is_ask
#print axioms ProofFile.Honest.K6.keyTie_of_three
