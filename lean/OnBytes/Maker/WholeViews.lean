-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WholeViews.lean: the three views on which the verifier of a whole file
(OnBytes/Maker/Whole.lean, `reductionOfWholeFile`) runs, by name, and what a yes of that verifier says of them.

  `view₁`, `view₂`, `view₃`: the three chains' views, as functions of the stored table and the
    transcript: the very terms that stand in `reductionOfWholeFile`'s field `out`.
  `wholeIOR_out_views`: where the verifier says yes, `run` has said yes at that instance ON THESE
    THREE VIEWS.
  `wholeIOR_out_iff`: the verifier says yes exactly where its nine tests do: the three tests of
    work, the three on the parts of the draws, the one on the stored table's symbols, `silent`, and
    `run` on the three views.

What is not claimed. That these views are a reader's views of a file.


-/
import OnBytes.Maker.WholeLaws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ Compile.Joined

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh)

/-- The first chain's view. -/
def view₁ : View :=
  viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
    ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) D.key₁
    (wantsOf D.a D.depth D.ds₁
      (drawnT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ))))

/-- The second chain's. -/
def view₂ : View :=
  viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
    ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) D.key₂
    (wantsOf D.a D.depth D.ds₂
      (drawnT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ))))

/-- The third chain's. -/
def view₃ : View :=
  viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
    ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)) D.key₃
    (wantsOf D.a D.depth D.ds₃
      (drawnT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ))))

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  (x : Xi)

/-- **The verifier says yes exactly where its nine tests do.** -/
theorem wholeIOR_out_iff :
    ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true ↔
      (passT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) = true ∧
        passT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) = true ∧
        passT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)) = true) ∧
      (fullOf D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ))) = true ∧
        fullOf D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ))) = true ∧
        fullOf D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ))) = true) ∧
      carriesOf D y
        (wantsOf D.a D.depth D.ds₁
            (drawnT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ))) ++
          (wantsOf D.a D.depth D.ds₂
              (drawnT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ))) ++
            wantsOf D.a D.depth D.ds₃
              (drawnT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ))))) = true ∧
      silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
        ((chainsOf C D tF tJ t3).msg3 τ).2 = true ∧
      run x (view₁ C D tF tJ t3 y τ) (view₂ C D tF tJ t3 y τ) (view₃ C D tF tJ t3 y τ) = true := by
  unfold view₁ view₂ view₃
  simp only
  constructor
  · intro h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, f1⟩, f2⟩, f3⟩, k⟩, s⟩, r⟩ := hc
      exact ⟨⟨p1, p2, p3⟩, ⟨f1, f2, f3⟩, k, s, r⟩
    · cases h
  · rintro ⟨⟨p1, p2, p3⟩, ⟨f1, f2, f3⟩, k, s, r⟩
    rw [if_pos (by
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, f1⟩, f2⟩, f3⟩, k⟩, s⟩, r⟩)]
    rfl

/-- **Where the verifier says yes, the run has said yes on the file's three views.** -/
theorem wholeIOR_out_views
    (h : ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true) :
    run x (view₁ C D tF tJ t3 y τ) (view₂ C D tF tJ t3 y τ) (view₃ C D tF tJ t3 y τ) = true :=
  ((wholeIOR_out_iff C D tF tJ t3 y τ silent run x).1 h).2.2.2.2

end

end OnBytes.Maker
