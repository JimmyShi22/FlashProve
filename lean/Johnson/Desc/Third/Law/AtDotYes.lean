-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/AtDotYes.lean: THE PREMISES OF THE (Dot) JOINT (AtDot,
Johnson/Desc/Third/Law/AtDot.lean) AT THE RECORD THAT THE LAST CHAIN's START RETURNS, WHERE THE
CHAIN's FIRST BLOCK ("K14, second part") SAYS YES: three of the four are given by the two yeses; one
is left: the one pending row's weights are well-formed. Theorems; no definition.

Why. AtDot.omega ("Omega, in the border's copy of the shared statement, has the plan's shape") was
given by nobody: the taking-over laid the shape that it found. The last chain's text over Block's
ninth asks it: takeOver's fifth test, "Omega: it has the plan's shape", which takeOver_shape
(Johnson/Desc/Third/Law/Keeps.lean) hands back. Here it is carried to the block and to AtDot.

OBJECT   takeOver · (batchLinearConstraintsSecondPart p).decide (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean) · start₃E
         (Johnson/Desc/Third/State.lean).
USER     the field atDot of RowZeroLeft (Johnson/Desc/Third/Law/Row0AtTable.lean), which has the
         block's own yes in front.
LETTERS  none but the texts' own.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.

  shape_k14Second      the block's yes: Omega, in the border's copy of the shared statement, has the
                       plan's shape: by takeOver_shape (Johnson/Desc/Third/Law/Keeps.lean): CALLED.
  atDot_of_start_yes   **AtDot at the start's record, from the start's yes, the block's yes and the
                       weights.** By atDot_of_start (Law/AtDotStart.lean): CALLED.
What is not claimed. That the weights are well-formed: the first chain's matter. Of the form "a yes
gives". Nothing on soundness or on hiding.

-/
import Johnson.Desc.Third.Law.Alone
import Johnson.Desc.Third.Law.AtDotStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open Desc.Plain (DState)

namespace VerifiableInference.Desc.Third.Law

/-- The like of the block. -/
theorem shape_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (x : Border) (hx : s.loc.border = some x) (y : OnBytes.Oracle)
    (hy : x.shared.st.oracles[x.shared.omega]? = some y) : y.shape = p.S.omega := by
  obtain ⟨x', a, _, _, hx', ha, _, _, _⟩ := k14Second_inv p s s' rs gs h
  have ex : x' = x := Option.some.inj (hx'.symm.trans hx)
  rw [ex] at ha
  obtain ⟨y', hy', hs⟩ := takeOver_shape _ _ _ _ _ ha
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  exact hs

/-- **AtDot at the start's record, where the block says yes.** -/
theorem atDot_of_start_yes {Cl : Type} (p : P₁₄) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut)
    (s₀ s' : S₃) (hs : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s')
    (hweights : ∀ r, pile₁ = [r] → ∀ g ∈ r.g, g.ok = true) : AtDot p s₀ := by
  refine atDot_of_start p st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o s₀ hs (fun y hy => ?_) hweights
  obtain ⟨f, _, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  exact shape_k14Second p _ s' rs gs hd { g := f.g, shared := o } rfl y hy

end VerifiableInference.Desc.Third.Law
