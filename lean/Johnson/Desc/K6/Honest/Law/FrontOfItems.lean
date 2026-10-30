-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/FrontOfItems.lean.
WHAT IT IS NOT. Every statement is CONDITIONAL. IT TAKES SENTENCES ON THE STATE AS PREMISES, NOT THE
TABLE's PROMISE: that a promise, at whichever meaning, hands these sentences at the border in front
of the sub-protocol is not shown here. No state is shown at which they hold together. AT THE FULL
SIZE ALONE: the head's segment is number 24 throughout. Nothing on soundness, on completeness or on
hiding.
WHAT IT IS. THE STATE IN FRONT OF THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (K6) IS READY
(K6Front, K6/Honest/Law/Returns.lean), FROM WHAT THE TABLE's PROMISE SAYS THERE, taken sentence by
sentence, and from tests with code on public numbers.
  K6Front.less       room for fewer slots.
  stand_at_k6        CONDITIONAL on the book-keeping's clause on where the chain stands
                     (First.shapeAt, First/Borders.lean), at the sub-protocol's place in the full
                     chain: the chain stands in the head's segment.
  headOpen_of_stand  CONDITIONAL: it stands there, and the lookup on the calls is heard: the head's
                     link is opened, with what the lookup left. (The state's two readers answer in
                     the other sorts of segment too: so the first premise is wanted.)
  fresh_of_leftSays  CONDITIONAL on the fields of Kinds/Law/K6LeftSays.lean's LeftSays and on room
                     by the numbers: the ledger in hand is well laid, and m more slots are there
                     and free.
  k6Front_of_items   MAIN. CONDITIONAL: no mark; the chain stands in the head's segment; "what the
                     lookup on the calls left"; "a token is heard, below the vocabulary's size"; the
                     state's own test on the request; the tests k6PubC (Kinds/Law/K6PubNumbers.lean)
                     and keysFitB (Kinds/Law/K6GivenOfLeft.lean) on public numbers: K6Front, with
                     just the room behind the hearing that the lookup on the digits takes. Of "a
                     token is heard, below the vocabulary's size" the first half alone is spent:
                     K6Front has no field on the size.
WHO IS MEANT TO PAY. The two tests on public numbers: in the goals' scope k6Pub_in_scope
(Kinds/Law/K6PubInScope.lean) and headKeysFit_at_place (Kinds/Law/K6KeysInScope.lean). The test on
the request: startOk_reached (Kinds/Law/K6WayUpAtSeat.lean). The other four: the promise.
LETTERS. p8, h8 stand under "there is", pinned by the two equations.
CALLED: left_says, letters_of_left, k6Pub_says, Fresh.less (Kinds/Law/Returns.lean),
here_head_of_stand (Desc/Sound/MgAt/K3DigitsPlanesIt.lean), wellLaid_of_sized
(Kinds/Law/HeadLedgerMade.lean).

-/
import Mathlib
import Johnson.Desc.K6.Honest.Law.Returns
import Johnson.Desc.Kinds.Law.K6PubNumbers
import Johnson.Desc.Sound.Border62At
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesIt
import Johnson.Desc.Kinds.Law.HeadLedgerMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork Forest.Shape Forest.Heard)
open OnBytes.Model.Forest (elems)
open VerifiableInference.OnPublicFiles (k3LeftItemAt)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open Norm (lt lPd)

/-- Room for fewer slots. -/
theorem K6Front.less {W : OnBytes.Model.Verify.Public} {m m' : Nat} {s : S} (R : K6Front W m s)
    (h : m' ≤ m) : K6Front W m' s := by
  exact ⟨R.clean, R.open_, R.start, R.letters, R.laid,
    Fresh.less R.room (Nat.add_le_add_left h _)⟩

/-- The book-keeping's clause on where the chain stands, at the place of the output head's own
rounds in the full chain. -/
theorem stand_at_k6 {s : S}
    (h : First.shapeAt Sound.linksFull
      (some { chain := 1, link := some 24, piece := 4, kind := .K6 }) s = true) :
    First.standOf s = .link .head := by
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.trans (by decide)

/-- Where the chain stands in the head's segment and the lookup on the calls is heard. -/
theorem headOpen_of_stand {s : S} {g : Forest.Heard} (hst : First.standOf s = .link .head)
    (hl : s.lookHeard? = some g) : HeadOpen s := by
  obtain ⟨o, hh⟩ := VerifiableInference.OnPublicFiles.here_head_of_stand hst
  have hl' : (if o.opened then o.lookHeard else none) = some g := by
    unfold S.lookHeard? at hl
    rw [hh] at hl
    exact hl
  by_cases hop : o.opened = true
  · rw [if_pos hop] at hl'
    exact ⟨o, hh, hop, by rw [hl']; rfl⟩
  · rw [if_neg hop] at hl'
    cases hl'

/-- What Law/K6LeftSays.lean's fields say of the ledger in hand, in the words of the hearing's law:
its arrays have their lengths, and m more slots are there and free, where the numbers leave so many.
-/
theorem fresh_of_leftSays {h3 : Forest.Shape} {first n m : Nat} {F' : Fork} {g : Forest.Heard}
    (Y : LeftSays h3 first n F' g) (hroom : first + elems h3 + m ≤ n) :
    WellLaid F' ∧ Fresh F' m := by
  have hS := Y.sized
  refine ⟨wellLaid_of_sized hS, ?_, Nat.le_refl _, hS.2.2, fun j h1 h2 => ?_⟩
  · rw [Y.next, Y.ns]
    exact hroom
  · have hnf := Y.free j h1
    unfold OnBytes.PscRun.Filled at hnf
    have hin : j < F'.gotF.size := by
      rw [hS.2.2]
      exact h2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hin] at hnf ⊢
    simpa using hnf

/-- **THE STATE IN FRONT OF K6's MEMBER IS READY, FROM WHAT THE TABLE's PROMISE SAYS THERE.**
CONDITIONAL: no mark; the chain stands in the head's segment; the two public sentences "what the
lookup on the calls left" and "a token is heard, below the vocabulary's size"; the state's own test
on the request; two tests with code on public numbers. The room that is left behind the hearing is
what the lookup on the digits takes. -/
theorem k6Front_of_items (W : OnBytes.Model.Verify.Public) {s : S} (hu : s.failed = none)
    (hst : First.standOf s = .link .head) (hleft : k3LeftItemAt W 24 s)
    (htok : tokenHeardB W.hS (readsOf W) s = true) (hstart : startOk W s = true)
    (hpub : k6PubC W = true)
    (hkeys : ∀ p3 h3, placeAt W 24 false = some p3 → p3.shape = some h3 →
      @keysFitB (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor h3 = true) :
    ∃ p8 h8, placeAt W 24 true = some p8 ∧ p8.shape = some h8 ∧ K6Front W (elems h8) s := by
  obtain ⟨p3, e3, L⟩ := hleft
  obtain ⟨h3, F', g, hs3, hF, hg, Y, _⟩ := left_says p3 s L
  obtain ⟨_, _, _, _, _, p8, h8, e8, s8, hnum⟩ := k6Pub_says W hpub
  obtain ⟨n1, n2, _⟩ := hnum p3 h3 e3 hs3
  have hled : (seatAt W.hS (readsOf W)).ledger s = F' := by
    show s.fork?.getD {} = F'
    rw [hF]
    rfl
  obtain ⟨hW, hFr⟩ := fresh_of_leftSays
    (m := takesOf (parOf W.hS (workOf W)) + elems h8) Y (by omega)
  exact ⟨p8, h8, e8, s8, hu, headOpen_of_stand hst hg, hstart,
    letters_of_left W L hs3 (hkeys p3 h3 e3 hs3) htok, by rw [hled]; exact hW,
    by rw [hled]; exact hFr⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.K6Front.less
#print axioms VerifiableInference.Desc.Kinds.Head.Law.stand_at_k6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.headOpen_of_stand
#print axioms VerifiableInference.Desc.Kinds.Head.Law.fresh_of_leftSays
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Front_of_items
