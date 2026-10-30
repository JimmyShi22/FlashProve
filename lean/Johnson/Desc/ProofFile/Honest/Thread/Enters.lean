-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Enters.lean: THE TWO PREMISES AT THE FIRST AND THE SHARED
CHAIN's START (`Enters₁`, `Enters₂`: Honest/Thread/File.lean), CUT INTO WHAT BEARS CONTENT.
`Enters₁` says that the whole thread holds at the chain's start: seven clauses. Where `ready`
returns, at a thread that takes no tree over and has no round in front of it, whose stored columns
are the prover's own, three of the seven hold by the frame's own text (the tables at hand; the
challenges heard; how the state was made, from its first state). What is left is what the thread's
letters say AT THE START: that the first state is the one that the thread begins with; the form; the
items that are open at the start; the rider; the input. Conditional lemmas on our own definitions;
general in the description, the prover and the thread.

  `enters₁_of`, `enters₂_of`

Limits. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

section
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **THE FIRST CHAIN's START.** -/
theorem enters₁_of {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hR : ready F Bk H w₀ rc x k = .ok R)
    (hst : ∀ v, T₁.stored v = H.storedWords v.w₀ v.rc) (htk : T₁.taken = [])
    (hah : T₁.ahead = [])
    (hbeg : T₁.begun k R.own [] (F.start₁ (F.pub x)))
    (hForm : T₁.Form 0 k (F.start₁ (F.pub x)) (R.start₁ H))
    (hItems : T₁.Items (T₁.opened 0) k (F.start₁ (F.pub x)) (R.start₁ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (hr : T₁.rides 0 R.own (F.start₁ (F.pub x))) (hv : T₁.valid R.own) :
    Enters₁ F H T₁ w₀ rc x k R := by
  obtain ⟨-, tr, -, hown, -, -, -, -⟩ := ready_ok hR
  unfold Enters₁ Thr
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, ?_, hForm, hItems, ?_, hr, hv⟩
  · show H.storedWords w₀ rc i p = T₁.stored R.own i p
    rw [hst, hown]
  · have hh : T₁.hand 0 = [] := by
      unfold Thread.hand
      rw [htk]
      rfl
    rw [hh] at hσ
    cases hσ
  · unfold Thread.Fit
    rw [hah]
    rfl
  · unfold Thread.Made
    refine ⟨rfl, ?_, rfl, fun _ _ => rfl, F.start₁ (F.pub x), [], ?_, ?_, ?_⟩
    · show ([] : List Fmt.Drawn) = T₁.locOf []
      unfold Thread.locOf
      simp
    · show T₁.begun k R.own (([] : List Fmt.Drawn).take T₁.front) (F.start₁ (F.pub x))
      rw [List.take_nil]
      exact hbeg
    · rfl
    · show foldBlocks T₁.ft (T₁.bs.take 0) (F.start₁ (F.pub x))
        (([] : List Fmt.RoundView).drop T₁.front) [] = .ok (F.start₁ (F.pub x), [], [])
      rw [List.drop_nil]
      rfl

/-- **THE SHARED CHAIN's START.** -/
theorem enters₂_of {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (hR : ready F Bk H w₀ rc x k = .ok R)
    (hst : ∀ v, T₂.stored v = H.storedWords v.w₀ v.rc) (htk : T₂.taken = [])
    (hah : T₂.ahead = [])
    (hbeg : T₂.begun k R.common [] (F.start₂ (F.pub x)))
    (hForm : T₂.Form 0 k (F.start₂ (F.pub x)) (R.start₂ H))
    (hItems : T₂.Items (T₂.opened 0) k (F.start₂ (F.pub x)) (R.start₂ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (hr : T₂.rides 0 R.common (F.start₂ (F.pub x))) (hv : T₂.valid R.common) :
    Enters₂ F H T₂ w₀ rc x k R := by
  obtain ⟨-, tr, -, -, hcom, -, -, -⟩ := ready_ok hR
  unfold Enters₂ Thr
  refine ⟨⟨fun i p => ?_, fun σ hσ => ?_⟩, ?_, hForm, hItems, ?_, hr, hv⟩
  · show H.storedWords w₀ rc i p = T₂.stored R.common i p
    rw [hst, hcom]
  · have hh : T₂.hand 0 = [] := by
      unfold Thread.hand
      rw [htk]
      rfl
    rw [hh] at hσ
    cases hσ
  · unfold Thread.Fit
    rw [hah]
    rfl
  · unfold Thread.Made
    refine ⟨rfl, ?_, rfl, fun _ _ => rfl, F.start₂ (F.pub x), [], ?_, ?_, ?_⟩
    · show ([] : List Fmt.Drawn) = T₂.locOf []
      unfold Thread.locOf
      simp
    · show T₂.begun k R.common (([] : List Fmt.Drawn).take T₂.front) (F.start₂ (F.pub x))
      rw [List.take_nil]
      exact hbeg
    · rfl
    · show foldBlocks T₂.ft (T₂.bs.take 0) (F.start₂ (F.pub x))
        (([] : List Fmt.RoundView).drop T₂.front) [] = .ok (F.start₂ (F.pub x), [], [])
      rw [List.drop_nil]
      rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.enters₁_of
#print axioms ProofFile.Honest.enters₂_of
