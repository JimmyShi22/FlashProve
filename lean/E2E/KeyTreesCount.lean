-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyTreesCount.lean: THE TWO NUMERALS THAT THE KEY FILE's THREADS BEAR (E2E/KeyRest.lean: a
tree's number through the file is read at 6 and 11) ARE THE DESCRIPTION's OWN COUNTS, in scope: its
first chain declares six trees, its shared chain eleven. Two calls of the library's. Public facts:
no state, no run. NOTHING IS SHOWN OF ANY PROVER.

  **`trees_six`**, **`trees_eleven`**: `(D Xs N Pl).t₁ = 6`, `(D Xs N Pl).t₂ = 11` (`FileDescription.t₁`,
      `FileDescription.t₂`, Johnson/Desc/BlockSlot.lean: the roots that a chain's declared rounds state):
      by `t1_six`, `t2_eleven` (Johnson/RunOne/Law/K12PlaceAtName.lean)
  `sourced_one`: what the description is made of stands under "there are" twice in our premise: the
      two are one: two returns of the same calls

Limits. In scope alone: at the full size. That the threads' reading of a tree's number (the frame's
`srcAt`) is the inverse of the library's numbering at these two counts is not shown.

-/
import E2E.KeyRest
import E2E.KeyPublic
import Johnson.RunOne.Law.K12PlaceAtName

set_option autoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Source LaterPlaces madeAt fixedDigest laterPlaces lawsAsk)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- The two "there are" of the premise, joined. -/
theorem sourced_one (hs : KeySourced Z Xs N Pl) : ∃ X₀ m,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
    madeAt X₀ Z.lay fixedDigest = .ok m ∧ laterPlaces m = .ok Pl ∧
    ∀ t ∈ lawsAsk X₀ Z.lay m (keyFileDescription Xs N Pl) (dataAtFiles flashProveData Z).DK, t.2 = true := by
  obtain ⟨X₀, m, h0, hm, -, hasks⟩ := hs.named.named
  obtain ⟨X₀', m', h0', hm', -, -, hL⟩ := hs.source
  have eX : X₀' = X₀ := Except.ok.inj (h0'.symm.trans h0)
  subst eX
  have em : m' = m := Except.ok.inj (hm'.symm.trans hm)
  subst em
  exact ⟨X₀', m', h0, hm, hL, hasks⟩

/-- **The first chain declares six trees.** -/
theorem trees_six (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (D Xs N Pl).t₁ = 6 := by
  obtain ⟨X₀, m, h0, hm, hL, hasks⟩ := sourced_one hs
  exact Johnson.RunOne.Law.K12PlaceAtName.t1_six scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hL Xs N hs.named.plan hasks

/-- **The shared chain declares eleven.** -/
theorem trees_eleven (hs : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (D Xs N Pl).t₂ = 11 := by
  obtain ⟨X₀, m, h0, hm, hL, hasks⟩ := sourced_one hs
  exact Johnson.RunOne.Law.K12PlaceAtName.t2_eleven scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hL Xs N hs.named.plan hasks

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.sourced_one
#print axioms AtPublicFiles.KeyThread.trees_six
#print axioms AtPublicFiles.KeyThread.trees_eleven
