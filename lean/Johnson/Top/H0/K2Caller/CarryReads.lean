-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CarryReads.lean: the code switch: WHAT THE SENTENCE «carry» READS OF
THE VERIFIER's STATE; and that the blank plan of the smallness test in CarryClosed.lean's way in
costs nothing.
  carryRow_reads   CarryK2.lean's carryRow reads of the state THE FRONT (K2.frontAt), THE BOOK AND
                   THE ROOTS ALONE: two states with these three in common say the same sentence
  headFrontQ_tl    the head's own first step (Tw/K2C/Head.lean's headFrontQ) accepts at one plan of
                   the smallness test just where it does at another, and what it makes has one
                   front, one book and the same roots
  doorZ_head       so, in front of that step, at whatever plan it is seated: doorZ lets a state in,
                   and the sentence at it is the sentence at what the step makes
WHAT ELSE carryRow_reads IS FOR. Whoever carries «carry» over a sub-protocol that lies in the item's
span owes these three equations at the two states that the way in lets in, and no more.
LIMITS. Three laws on a reading. Nothing on whether the sentence holds. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.CarryClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK} {Y : Type} (p : K2.P2) (orc : Y → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)

/-- **The sentence reads of the verifier's state the front, the book and the roots alone.** -/
theorem carryRow_reads (t t' : VerifiableInference.Desc.First.S) (y : Y)
    (h1 : K2.frontAt p t = K2.frontAt p t') (h2 : t.book = t'.book) (h3 : t.roots = t'.roots) :
    carryRow r H p orc smp t y ↔ carryRow r H p orc smp t' y := by
  have e : ∀ fx W₀, faAt r H p orc smp (t, fx, W₀) y = faAt r H p orc smp (t', fx, W₀) y := by
    intro fx W₀
    unfold faAt K2.longFront
    simp only [h2, h3]
  unfold carryRow carryOf
  simp only [h1, e]

/-- **The head's own first step gives one front, book and roots at every plan of the smallness
test.** -/
theorem headFrontQ_tl (tl tl' : OnBytes.Model.HTailF2) (s t : VerifiableInference.Desc.First.S)
    (h : K2.headFrontQ tl s = .ok t) :
    ∃ t', K2.headFrontQ tl' s = .ok t' ∧ (∀ q, K2.frontAt q t' = K2.frontAt q t) ∧
      t'.book = t.book ∧ t'.roots = t.roots := by
  unfold K2.headFrontQ at h ⊢
  split at h
  · cases h
  rename_i hb
  split at h
  · cases h
  rename_i hd
  rw [if_neg hb, if_neg hd]
  have hb' : s.atBetween = true := by simpa using hb
  cases hx : _root_.Tw.K2.firstFront s.st s.check.frame with
  | error e =>
    rw [hx] at h
    cases h
  | ok x =>
    rw [hx] at h
    cases hf : s.failed with
    | some m =>
      simp [Except.bind, VerifiableInference.Desc.First.S.enterHead?,
        VerifiableInference.Desc.First.S.enterHead, VerifiableInference.Desc.First.S.unmarked, hb',
        hf] at h
    | none =>
      simp only [Except.bind, VerifiableInference.Desc.First.S.enterHead?,
        VerifiableInference.Desc.First.S.enterHead, VerifiableInference.Desc.First.S.unmarked, hb',
        hf, if_true] at h ⊢
      cases h
      exact ⟨_, rfl, fun q => by unfold K2.frontAt; cases q.stands <;> rfl, rfl, rfl⟩

/-- **So the blank plan in doorZ costs nothing**: in front of the head's own first step, at whatever
plan tl that step is seated: what doorZ lets in and what the step makes say the same sentence. -/
theorem doorZ_head (Z : ProofFile.Pub) (m : ℕ) (s t : VerifiableInference.Desc.First.S)
    (hs : (ProofFile.pAtK2 Z m).stands = .head) (hh : ∀ a, s.here ≠ .head a)
    (tl : OnBytes.Model.HTailF2) (h : K2.headFrontQ tl (rest s) = .ok t) :
    ∃ t', doorZ Z m s = some t' ∧ ∀ (y : Y),
      (carryRow r H (ProofFile.pAtK2 Z m) orc smp t' y ↔ carryRow r H (ProofFile.pAtK2 Z m) orc smp t y) := by
  obtain ⟨t', h1, h2, h3, h4⟩ := headFrontQ_tl tl {} (rest s) t h
  refine ⟨t', ?_, fun y => carryRow_reads _ orc smp t' t y (h2 _) h3 h4⟩
  unfold doorZ
  rw [hs]
  cases hq : s.here with
  | head a => exact absurd hq (hh a)
  | between => simp only [h1]; rfl
  | lay a => simp only [h1]; rfl
  | att a => simp only [h1]; rfl
  | fin a => simp only [h1]; rfl
  | mem a => simp only [h1]; rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.doorZ_head

#print axioms VerifiableInference.Desc.First.K2Caller.headFrontQ_tl

#print axioms VerifiableInference.Desc.First.K2Caller.carryRow_reads
