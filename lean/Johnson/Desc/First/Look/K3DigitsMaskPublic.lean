-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
digits_maskB_of_upTo: its premises are evaluated nowhere here.
Johnson/Desc/First/Look/K3DigitsMaskPublic.lean: the lookup on the DIGITS of a link's approximate
range proof: THE TEST ON PUBLIC DATA UNDER THE MASK ROW's DICTIONARY (hB of digits_maskRow,
Johnson/Desc/First/Look/K3DigitsMask.lean: maskB … x.arrays.ns) FOLLOWS FROM THE LIKE TEST AT THE
CALLS' LIST (maskCallsB, Johnson/Desc/First/Look/K3CallerAttReads.lean), and so from
masksUpTo (Johnson/Desc/First/Att/K05MasksAtt.lean). Statements and proofs. Ties of
tests: no error term. NO SOUNDNESS IS CLAIMED.

Why. The calls' list is the kept messages, then the link's own of moment 0; the digits' list is the
link's own of all moments: a first stretch of the link's list in both: so the message that holds the
mask row, which the first test finds among those of moment 0, stands in the second list under its
own number, with the same shape.

OBJECT: three functions to Bool on public data.
USER: Johnson/P5J/K03MaskBAt.lean and Johnson/P5J/K09LeftPub.lean call digits_maskB_of_upTo.
LETTERS: D, rad, i, hi, mom; x free.



  Compiled with the whole library.
Main names:
  `takeWhile_wider`: what a first stretch holds at a number, a longer first stretch holds there.
  `maskB_of_calls`: maskCallsB at the calls' list gives maskB at the link's own list up to any
    moment.
  `maskB_less`: the test at a bound gives it at every smaller bound.
  `digits_maskB_of_upTo`: masksUpTo D x x.ns = true and x.arrays.ns ≤ x.ns give hB.

Limits. One way. x.arrays.ns ≤ x.ns is a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMaskPublic
import Johnson.Desc.First.Look.K3CallerLaid
import Johnson.Desc.First.Look.K3Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P (masksUpTo)

/-- What a first stretch holds at a number, a longer first stretch holds there. -/
theorem takeWhile_wider {α : Type} (p p' : α → Bool) (hp : ∀ a, p a = true → p' a = true) :
    ∀ (l : List α) (n : ℕ) (a : α), (l.takeWhile p)[n]? = some a → (l.takeWhile p')[n]? = some a
  | [], n, a, h => by simp at h
  | y :: l, n, a, h => by
    by_cases hy : p y = true
    · rw [List.takeWhile_cons_of_pos hy] at h
      rw [List.takeWhile_cons_of_pos (hp y hy)]
      cases n with
      | zero => exact h
      | succ n =>
        rw [List.getElem?_cons_succ] at h ⊢
        exact takeWhile_wider p p' hp l n a h
    · rw [List.takeWhile_cons_of_neg hy] at h
      simp at h

/-- **The test at the calls' list gives the test at the link's own list, up to any moment.** -/
theorem maskB_of_calls {D : Sent} {rad : OracleShape → ℕ} {i hi : ℕ}
    (h : maskCallsB D (sigListCalls D rad i) i hi = true) (mom : ℕ) :
    maskB D (sigList D rad i mom) i hi = true := by
  unfold maskCallsB at h
  unfold maskB
  cases hm : (messagesAt D i).findIdx? fun y => y.shape.maskRows != 0 with
  | none =>
    simp only [hm] at h
    cases h
  | some mi =>
    simp only [hm] at h ⊢
    have e : (sigListCalls D rad i)[(keptAt D i).length + mi]? = (sigList D rad i 0)[mi]? := by
      unfold sigListCalls
      rw [List.getElem?_append_right (by simp)]
      simp
    rw [e] at h
    cases ho : (sigList D rad i 0)[mi]? with
    | none =>
      simp only [ho] at h
      cases h
    | some o =>
      simp only [ho] at h
      have e2 : (sigList D rad i mom)[mi]? = some o := by
        unfold sigList at ho ⊢
        rw [List.getElem?_map] at ho ⊢
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 ho
        rw [takeWhile_wider _ _ (fun a ha => by
          rw [decide_eq_true_eq] at ha ⊢
          omega) _ _ _ hy]
        rfl
      simp only [e2]
      exact h

/-- The test at a bound gives it at every smaller bound. -/
theorem maskB_less {D : Sent} {l : List (OracleShape × Nat)} {i hi lo : ℕ}
    (h : maskB D l i hi = true) (hl : lo ≤ hi) : maskB D l i lo = true := by
  unfold maskB at h ⊢
  cases hm : (messagesAt D i).findIdx? fun y => y.shape.maskRows != 0 with
  | none =>
    simp only [hm] at h
    cases h
  | some mi =>
    simp only [hm] at h ⊢
    cases ho : l[mi]? with
    | none =>
      simp only [ho] at h
      cases h
    | some o =>
      simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨h.1, Nat.le_trans hl h.2⟩

/-- **hB OF digits_maskRow, FROM THE ATTENTION KIND's TEST.** -/
theorem digits_maskB_of_upTo {D : Sent} {x : Place} (h : masksUpTo D x x.ns = true)
    (hns : x.arrays.ns ≤ x.ns) (rad : OracleShape → ℕ) :
    maskB D (digList x D rad) x.link x.arrays.ns = true :=
  maskB_less (maskB_of_calls (maskCallsB_of_upTo h rad) (lastMoment D x.link)) hns

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.maskB_of_calls
#print axioms VerifiableInference.Desc.First.Look.digits_maskB_of_upTo
