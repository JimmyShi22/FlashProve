-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Mask.lean: what the last chain's start's yes gives of the message at the
mask's number. Theorems.

Why. Since the start takes W's, the own group's and the mask's numbers by name, out of the first
chain's own record, a record that hands on a wrong number is read. These laws say which wrong
numbers the start refuses.

Main names:
  `numbersOk_mask`: numbersOk gives: the message at the mask's number is there, is not sampled, and
    its shape counts no answer.
  `start_mask`: the same of the start's yes, at the number that was handed in.
  `start_mask_ne_w`: so the mask's number is not W's, where the plan's shape of W counts an answer.
  `start_mask_ahead`: the start's yes gives: a mask's number was handed in just where the plan's
    shape sends masks ahead.
  `linOk_w_answers`: a shape that is lawful at the codes (linOk, which the start asks) counts one.
  `start_refuses_w_as_mask`: so the start refuses a record that hands on W's number as the mask's:
    without a premise.

Limits. Of wrong numbers only W's own is shown to be refused. That the mask's number is no member of
the own group follows from `start_mask` where every member of a group is sampled
(OnBytes.Means.SampledMembers, Johnson/Desc/Means/Entry.lean): not stated here. That the mask's
message is no member, is unspent and has the mask's whole shape is asked by the own test's front,
which is in other files. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.AtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

/-- numbersOk: the message at the mask's number is there, unsampled, and counts no answer. -/
theorem numbersOk_mask (S : Params.LinShape) (f : FirstOut) (h : numbersOk S f = true) :
    ∀ m, f.mask = some m →
      ∃ y, f.st.oracles[m]? = some y ∧ y.sampled = false ∧ y.shape.answers = 0 := by
  unfold numbersOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨_, hm⟩ := h
    intro m em
    rw [em] at hm
    cases hy : f.st.oracles[m]? with
    | none => simp [hy] at hm
    | some y =>
      simp only [hy, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
      exact ⟨y, rfl, hm.1, hm.2⟩
  · cases h

/-- **The start's yes**, at the number that was handed in. -/
theorem start_mask (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    ∀ m, mask₁ = some m →
      ∃ y, st₁.oracles[m]? = some y ∧ y.sampled = false ∧ y.shape.answers = 0 := by
  obtain ⟨f, hf, _⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨hn, ef, _, _, em, _⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  intro m hm
  have := numbersOk_mask S f hn m (em.trans hm)
  rwa [ef] at this

/-- **The mask's number is not W's**, where the plan's shape of W counts an answer. -/
theorem start_mask_ne_w (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (ha : S.w.answers ≠ 0) : mask₁ ≠ some w₁ := by
  intro e
  obtain ⟨y, hy, _, h0⟩ := start_mask _ _ _ _ _ _ _ _ _ _ _ h w₁ e
  obtain ⟨f, hf, _⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨hn, ef, ew, _⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨x, _, hx, _, x1, _⟩ := numbersOk_inv _ _ hn
  rw [ef, ew] at hx
  obtain rfl : x = y := Option.some.inj (hx.symm.trans hy)
  rw [x1] at h0
  exact ha h0

/-- A mask's number is handed in just where the shape sends masks ahead. -/
theorem firstOutFrom_ahead (S : Params.LinShape) (st : Statement) (book : TreeBook)
    (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pile = some f) :
    mask.isSome = S.masksAhead := by
  unfold firstOutFrom at h
  split at h
  · try dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.2
    · cases h
  · cases h

/-- **The start's yes ties the mask to the plan**: a mask's number was handed in just where the
shape sends masks ahead. -/
theorem start_mask_ahead (codes : Codes) (S : Params.LinShape) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow)
    (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    mask₁.isSome = S.masksAhead := by
  obtain ⟨f, hf, _⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  exact firstOutFrom_ahead _ _ _ _ _ _ _ _ _ hf

/-- A shape that is lawful at the codes counts at least one answer for W. -/
theorem linOk_w_answers (codes : Codes) (S : Params.LinShape) (h : linOk codes S = true) :
    S.w.answers ≠ 0 := by
  simp only [linOk, Bool.and_eq_true] at h
  have hS : S.ok = true := h.1.1.1.1.1.1.1
  simp only [Params.LinShape.ok, Bool.and_eq_true] at hS
  have hw : Params.LinShape.vectorMessageOk S.w = true := hS.1.1.1.1.1.1.1.2
  simp only [Params.LinShape.vectorMessageOk, Bool.and_eq_true, decide_eq_true_eq] at hw
  omega

/-- The start's yes: the shape is lawful at the codes. -/
theorem start₃E_lin (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    linOk codes S = true := by
  unfold start₃E at h
  split at h
  · cases h
  · rename_i hc
    cases hl : linOk codes S with
    | true => rfl
    | false => simp [hl] at hc

/-- **The start refuses a record that hands on W's number as the mask's**: without a premise. -/
theorem start_refuses_w_as_mask (codes : Codes) (S : Params.LinShape) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃) :
    start₃E codes S st₁ book₁ roots₁ w₁ own₁ (some w₁) pile₁ o ≠ .ok s₀ := fun h =>
  start_mask_ne_w _ _ _ _ _ _ _ _ _ _ _ h
    (linOk_w_answers codes S (start₃E_lin _ _ _ _ _ _ _ _ _ _ _ h)) rfl

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.numbersOk_mask
#print axioms VerifiableInference.Desc.Third.Law.start_mask
#print axioms VerifiableInference.Desc.Third.Law.start_mask_ne_w
#print axioms VerifiableInference.Desc.Third.Law.start_mask_ahead
#print axioms VerifiableInference.Desc.Third.Law.linOk_w_answers
#print axioms VerifiableInference.Desc.Third.Law.start_refuses_w_as_mask
