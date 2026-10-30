-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/StartThree.lean: WHAT A YES OF THE LAST CHAIN's START SAYS, AT THE PROOF FILE's
DESCRIPTION AS `ProofFile.fileDescBy` MAKES IT (Johnson/Desc/ProofFile/Frames1.lean): read off that
definition's own text, general in the two later chains' seats A and B, in the first chain and in
`get`. Statements with their proofs.

  `fileDescBy_start₃`: start₃ p s₁ s₂ = .ok s gives: the first chain's record passes `First.S.fin`;
    the shared chain has ended (A.ended s₂ = some e); and s is B's own start of (p, the record, e).
  `fileDescBy_start₃_iff`: and the other way.
  `start₃_fin`, `start₃_no_mark`, `start₃_ends`: the same of `(… ).toOption = some s`, the form in
    which the rule of composition takes the start (`atDesc`): "passes fin"; "no mark"; "has ended,
    and s is B's start". A reader `g` of the pair (public part, first record) whose second half is
    `get` of the record may stand in `get`'s place (hg).
What for. `P5J.TablesFit`'s field START; two premises (hmark, hstart) of the rule that states its
field SH₃ at texts.
Limits. Of `fileDescBy`'s value alone: that the description that is seated is such a value, and at
which A and B, is not said here. Nothing on any block. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First

variable {σ : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat)
  (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl)

/-- **What the start's yes says**, and that nothing more is asked. -/
theorem fileDescBy_start₃_iff (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ) :
    (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ = .ok s ↔
      (get s₁).fin = true ∧ ∃ e, A.ended s₂ = some e ∧ B.start p (get s₁) e = .ok s := by
  show (if !(get s₁).fin then
      (Except.error "the first chain does not stand at its end" : Except String B.σ)
    else
      match A.ended s₂ with
      | none => .error "the shared chain has not ended"
      | some e => B.start p (get s₁) e) = .ok s ↔ _
  cases hf : (get s₁).fin with
  | false =>
    constructor
    · intro h
      cases h
    · rintro ⟨h, -⟩
      cases h
  | true =>
    cases he : A.ended s₂ with
    | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨-, e, h, -⟩
        cases h
    | some e =>
      constructor
      · intro h
        exact ⟨rfl, e, rfl, h⟩
      · rintro ⟨-, e', h, h'⟩
        cases h
        exact h'

theorem fileDescBy_start₃ (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : (fileDescBy o mk Z A B get start c).start₃ p s₁ s₂ = .ok s) :
    (get s₁).fin = true ∧ ∃ e, A.ended s₂ = some e ∧ B.start p (get s₁) e = .ok s :=
  (fileDescBy_start₃_iff o mk Z A B get start c p s₁ s₂ s).1 h

theorem ok_of_toOption {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b =>
    cases h
    rfl

variable {P₀ : Type} (g : InstPub × σ → P₀ × S) (hg : ∀ p s₁, (g (p, s₁)).2 = get s₁)
include hg

/-- The start's yes: the first chain's record passes `fin`. -/
theorem start₃_fin (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : ((fileDescBy o mk Z A B get start c).start₃ p s₁ s₂).toOption = some s) :
    (g (p, s₁)).2.fin = true := by
  rw [hg]
  exact (fileDescBy_start₃ o mk Z A B get start c p s₁ s₂ s (ok_of_toOption h)).1

/-- The start's yes: no mark. -/
theorem start₃_no_mark (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : ((fileDescBy o mk Z A B get start c).start₃ p s₁ s₂).toOption = some s) :
    (g (p, s₁)).2.failed = none := by
  have hf := start₃_fin o mk Z A B get start c g hg p s₁ s₂ s h
  unfold S.fin at hf
  rw [Bool.and_eq_true, Bool.and_eq_true] at hf
  exact Option.isNone_iff_eq_none.1 hf.1.1

/-- The start's yes: the shared chain has ended, and s is B's own start. -/
theorem start₃_ends (p : InstPub) (s₁ : σ) (s₂ : A.σ) (s : B.σ)
    (h : ((fileDescBy o mk Z A B get start c).start₃ p s₁ s₂).toOption = some s) :
    ∃ e, A.ended s₂ = some e ∧ B.start p (g (p, s₁)).2 e = .ok s := by
  rw [hg]
  exact (fileDescBy_start₃ o mk Z A B get start c p s₁ s₂ s (ok_of_toOption h)).2

end ProofFile

#print axioms ProofFile.fileDescBy_start₃_iff
#print axioms ProofFile.fileDescBy_start₃
#print axioms ProofFile.start₃_fin
#print axioms ProofFile.start₃_no_mark
#print axioms ProofFile.start₃_ends
