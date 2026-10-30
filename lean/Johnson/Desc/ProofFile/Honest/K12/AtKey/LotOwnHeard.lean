-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnHeard.lean: CAN THE PREMISE ON THE CHALLENGES BE MET: `HeardAtOwnTest`
(LotOwnWords.lean) where the words are read at the very list that the test's front has heard, and that list fits
declared rounds of which number `challengesOfFirstChain` draws the point.

  `point_of_fit`      where a list of challenges fits declared rounds, the challenge behind the first a rounds is
                      there and has as many elements as round number a draws
  `heard_at_own_test`   `HeardAtOwnTest` at one list on both sides

By what. `drawsFit`, `drawFit` (Honest/Frame.lean), `elems_one` (Honest/K14/MuPaid.lean).

Limits.
- That a stand's list fits is `Thr`'s clause `Fit`; that round number `challengesOfFirstChain` of the rounds in
  front is "LIN point", with the plan's count, is a public line on the description: both are the caller's.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open AtPublicFiles.KeyFile (KeyParts)
open ProofFile.Honest.K14 (firstRv rvOf elems_one)

/-- **The challenge behind the first rounds is there, with the declared count of elements.** -/
theorem point_of_fit : ∀ (front : List Fmt.DeclaredRound) (d : Fmt.DeclaredRound)
    (rest : List Fmt.DeclaredRound) (heard : List Fmt.Drawn),
    drawsFit (front ++ d :: rest) heard = true →
      heard.drop front.length ≠ [] ∧
        (Desc.K14.drawn (firstRv (heard.drop front.length))).length = d.entry.drawE
  | [], d, rest, [], h => by simp [drawsFit] at h
  | [], d, rest, x :: t, h => by
    simp only [List.nil_append, drawsFit, Bool.and_eq_true] at h
    have h1 := h.1
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
    have hlen : x.elems.length = d.entry.drawE := h1.1.1.1.1.1.1.1
    refine ⟨by simp, ?_⟩
    show (Desc.K14.drawn (rvOf x)).length = _
    rw [← elems_one x, ← hlen]
    show (x.elems.map OnBytes.E.ofTriple ++ []).length = _
    simp
  | _ :: front, d, rest, [], h => by simp [drawsFit] at h
  | _ :: front, d, rest, _ :: t, h => by
    simp only [List.cons_append, drawsFit, Bool.and_eq_true] at h
    exact point_of_fit front d rest t h.2

variable {W₀ Rc X₀ X Wk : Type}

/-- **`HeardAtOwnTest` at one list on both sides.** -/
theorem heard_at_own_test (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers)
    (front : List Fmt.DeclaredRound) (d : Fmt.DeclaredRound) (rest : List Fmt.DeclaredRound)
    (heard : List Fmt.Drawn) (hfit : drawsFit (front ++ d :: rest) heard = true)
    (hfront : front.length = N.challengesOfFirstChain)
    (hdraw : d.entry.drawE = K.send.P.par.S.kCol) : HeardAtOwnTest K N heard heard := by
  obtain ⟨h1, h2⟩ := point_of_fit front d rest heard hfit
  rw [hfront] at h1 h2
  exact ⟨rfl, rfl, rfl, h1, h2.trans hdraw⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.point_of_fit
#print axioms ProofFile.Honest.K12.AtKey.heard_at_own_test
