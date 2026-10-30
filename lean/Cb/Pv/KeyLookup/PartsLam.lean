-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsLam.lean: the errors and the numbers of values of the parts' steps are the
columns c and n of their share of the list of rounds of Cb/Pv/KeyLookup/Lam.lean.

Definitions, statements and proofs. The block is A.partsXK
(Cb/Pv/KeyLookup/PartsK.lean) at the sumcheck of Cb/Ld/LdPsc.lean; its lists are read by Err.toList
and Shape.chalList (Ior/KnowCollRulesChainErr.lean). q is the number of elements of E.

Main names:
  lamSteps q k: k times psc q [] (some (2, 2)). lamParts_is: the share lamParts q S of Lam.lean is
    lamSteps q (S.m - 1), by rfl.
  lamSteps_c, lamSteps_n: its column c is partsErrs k; its column n is partsVals q k.
  partsXK_errs, partsXK_vals: (A.partsXK wP cP (PscLtK.lib E Ex)).e.toList is the column c of
    lamParts q A.toPub, and .R.shape.chalList is its column n.
  partsXK_rounds: the block has 3 (m - 1) rounds.
  lamSteps_sent, lamSteps_short: the column sent is [1, 3, 2] a step; in short form [1, 2, 2].
  lamSteps_dropped: with a step fewer, whatever stands before and behind, the list is another one (a
    fact on lengths). lamSteps_eps: the list has exactly k rounds of the kind ε.

Limits: no premise. The column sent is not read off a shape here: Cb/Pv/KeyLookup/PartsSupp.lean
does that. The same at the short sumcheck: Cb/Pv/KeyLookup/PartsShort.lean.

-/
import Cb.Pv.KeyLookup.Lam
import Cb.Pv.KeyLookup.PartsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn

/-- Λ's stretch for k parts' steps. -/
def lamSteps (q k : ℕ) : List LRow := (List.range k).flatMap fun _ => psc q [] (some (2, 2))

theorem lamParts_is (q : ℕ) (S : Pub) : lamParts q S = lamSteps q (S.m - 1) := rfl

theorem lamSteps_succ (q k : ℕ) :
    lamSteps q (k + 1) =
      lamSteps q k ++ [⟨.eps, 1, q, 1⟩, ⟨.y, 3, q - 1, 2⟩, ⟨.vals, 2, 1, 0⟩] := by
  unfold lamSteps
  rw [List.range_succ, List.flatMap_append]
  simp [psc]

theorem lamSteps_c (q : ℕ) : ∀ k, (lamSteps q k).map (·.c) = partsErrs k
  | 0 => rfl
  | k + 1 => by rw [lamSteps_succ, partsErrs_succ, List.map_append, lamSteps_c q k]; rfl

theorem lamSteps_n (q : ℕ) : ∀ k, (lamSteps q k).map (·.n) = partsVals q k
  | 0 => rfl
  | k + 1 => by rw [lamSteps_succ, partsVals_succ, List.map_append, lamSteps_n q k]; rfl

theorem lamSteps_sent (q : ℕ) : ∀ k,
    (lamSteps q k).map (·.sent) = (List.range k).flatMap fun _ => [1, 3, 2]
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, lamSteps_sent q k, List.range_succ, List.flatMap_append]
    simp

theorem lamSteps_short (q : ℕ) : ∀ k,
    (lamSteps q k).map (fun r => r.short.sent) = (List.range k).flatMap fun _ => [1, 2, 2]
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, lamSteps_short q k, List.range_succ, List.flatMap_append]
    simp [LRow.short]

theorem lamSteps_length (q : ℕ) (k : ℕ) : (lamSteps q k).length = 3 * k := by
  have h := congrArg List.length (lamSteps_c q k)
  rw [List.length_map, partsErrs_length] at h
  exact h

/-- The tooth: a parts' step dropped, whatever stands before and behind: another list. -/
theorem lamSteps_dropped (q : ℕ) (a b : List LRow) (k : ℕ) :
    a ++ lamSteps q k ++ b ≠ a ++ lamSteps q (k + 1) ++ b := by
  intro h
  have := congrArg List.length h
  simp only [List.length_append, lamSteps_length] at this
  omega

/-- As many sumchecks as steps. -/
theorem lamSteps_eps (q : ℕ) : ∀ k, ((lamSteps q k).filter fun r => r.kind == .eps).length = k
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.filter_append, List.length_append, lamSteps_eps q k]
    rfl

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

theorem partsXK_errs :
    (A.partsXK wP cP (PscLtK.lib E Ex)).e.toList =
      (lamParts (Fintype.card E) A.toPub).map (·.c) := by
  rw [lamParts_is, lamSteps_c, ← toK_partsX A wP cP Unit Unit Unit (fun _ _ => 0)]
  exact (partsX_ll A wP cP Ex Unit Unit Unit (fun _ _ => 0)).1

theorem partsXK_vals :
    (A.partsXK wP cP (PscLtK.lib E Ex)).R.shape.chalList =
      (lamParts (Fintype.card E) A.toPub).map (·.n) := by
  rw [lamParts_is, lamSteps_n, ← toK_partsX A wP cP Unit Unit Unit (fun _ _ => 0)]
  exact (partsX_ll A wP cP Ex Unit Unit Unit (fun _ _ => 0)).2

/-- m - 1 parts' steps, three rounds each. -/
theorem partsXK_rounds : (A.partsXK wP cP (PscLtK.lib E Ex)).R.shape.length = 3 * (A.m - 1) := by
  rw [← toK_partsX A wP cP Unit Unit Unit (fun _ _ => 0)]
  exact partsX_rounds A wP cP Ex Unit Unit Unit (fun _ _ => 0)

end
end Lk6
