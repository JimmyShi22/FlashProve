-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchFrontTests.lean: code switching: AT THE FRONT THAT IS MADE OF EACH WRITTEN ENTRY OF
THE TWO TABLES (`fxAt r`, Johnson/G/SwitchFrontMember.lean; r in `tableFullLit` or `tableSmallLit`),
LEAN's KERNEL SAYS YES TO THE CLOSED TESTS that the law of the code switch asks of a front and of
its frame.

Why. The law's public premises on the front (`FrontAtL`'s twelve public clauses) and on the typed
caller (`CallerAt`) have been turned into tests with code: `frontPubB`
(Johnson/Top/H0/K2Hands/FrontPub.lean), `keptBelowB` (Johnson/Top/H0/K2Hands/FramePin.lean),
`SwRow.keptAt` (Johnson/Top/H0/K2Caller/SlotsOfFrame.lean; by place), `codesAt`
(Johnson/Top/H0/K2Hands/CallerMade.lean), `fitAt` (Johnson/Top/H0/K2Hands/FitTest.lean). They are to
be run at a written, locally numbered frame and carried to a place's real frame by a congruence.
Here they are run.
  `wAt r`: the frame that the program's routine returns at the made statement behind the sending.
  `frontTestsB r`: that there is such a frame, and the five tests.
  `frontTests_full`, `frontTests_small`: yes at all 25 and all 5 entries: by the kernel, at the five
  different entries of each table.
  `front_tests_at`: what that says: a frame W with `K2.frameAt (fxAt r) = some W`, the front's codes
  are r's, and the five tests' yes.
  `tests_can_fail`: each of the five says no somewhere: at a wrong length, or at another entry's
  frame.
Limits. MADE FRONTS: `fxAt r` numbers the messages in front by their place in r's own list: no run's
verifier state has that front behind the first links. Nothing is carried to a real frame here. The
five tests are other files'; what their yes gives is shown in the tests' own files. Nothing
on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.SwitchFrontMember
import Johnson.Top.H0.K2Hands.FitTest
import Johnson.Top.H0.K2Hands.FramePin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Caller VerifiableInference.Desc.First.K2Hands

/-- The frame that the program's routine returns at the made statement behind the sending. -/
def wAt (r : SwRow) : Option SwitchFrame :=
  switchFrame (stB r) (oldAt r) (tgtAt r) r.lo.length (anewAt r)

/-- **The closed tests at the made front of an entry**: there is a frame; the front's public
clauses; the kept old messages' numbers lie below the number of messages in front; the kept members
by place; the two codes; the fit of the names. -/
def frontTestsB (r : SwRow) : Bool :=
  match wAt r with
  | some W =>
    frontPubB r.l.length (fxAt r) && keptBelowB (fxAt r) && r.keptAt W && codesAt r W && fitAt r W
  | none => false

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at all 25 entries of the full table.** -/
theorem frontTests_full : (tableFullLit.all frontTestsB) = true :=
  full_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- **And at all 5 of the small one.** -/
theorem frontTests_small : (tableSmallLit.all frontTestsB) = true :=
  small_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **What the yes says.** -/
theorem front_tests_at {r : SwRow} (hF : frB r = true) (h : frontTestsB r = true) :
    ∃ W, K2.frameAt (fxAt r) = some W ∧ (fxAt r).st.codes = r.cs ∧
      frontPubB r.l.length (fxAt r) = true ∧ keptBelowB (fxAt r) = true ∧ r.keptAt W = true ∧
      codesAt r W = true ∧ fitAt r W = true := by
  unfold frontTestsB at h
  cases hW : wAt r with
  | none => rw [hW] at h; cases h
  | some W =>
    rw [hW] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨W, frameIs_at hF W hW, rfl, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- At each entry of the full table. -/
theorem front_tests_full {r : SwRow} (hr : r ∈ tableFullLit) :
    ∃ W, K2.frameAt (fxAt r) = some W ∧ (fxAt r).st.codes = r.cs ∧
      frontPubB r.l.length (fxAt r) = true ∧ keptBelowB (fxAt r) = true ∧ r.keptAt W = true ∧
      codesAt r W = true ∧ fitAt r W = true :=
  front_tests_at (List.all_eq_true.1 frB_full r hr) (List.all_eq_true.1 frontTests_full r hr)

/-- At each entry of the small table. -/
theorem front_tests_small {r : SwRow} (hr : r ∈ tableSmallLit) :
    ∃ W, K2.frameAt (fxAt r) = some W ∧ (fxAt r).st.codes = r.cs ∧
      frontPubB r.l.length (fxAt r) = true ∧ keptBelowB (fxAt r) = true ∧ r.keptAt W = true ∧
      codesAt r W = true ∧ fitAt r W = true :=
  front_tests_at (List.all_eq_true.1 frB_small r hr) (List.all_eq_true.1 frontTests_small r hr)

set_option maxRecDepth 1000000 in
/-- **Each of the five can fail**: the public clauses at a wrong number of sampled messages; the
numbers' test at a statement without a message; the kept members at another entry's frame; the codes
at an entry of the small table against a frame of the full one; the fit at another entry's frame. -/
theorem tests_can_fail :
    frontPubB 0 (fxAt full0) = false ∧
      keptBelowB { fxAt full0 with st := { (fxAt full0).st with oracles := #[] } } = false ∧
      ((wAt fullOdd).map fun W => full0.keptAt W) = some false ∧
      ((wAt full0).map fun W => codesAt (smallAt 0) W) = some false ∧
      ((wAt full0).map fun W => fitAt full24 W) = some false := by decide +kernel

end Johnson.G

#print axioms Johnson.G.frontTests_full
#print axioms Johnson.G.frontTests_small
#print axioms Johnson.G.front_tests_at
#print axioms Johnson.G.front_tests_full
#print axioms Johnson.G.front_tests_small
#print axioms Johnson.G.tests_can_fail
