-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsErr.lean: the errors of the parts' chain, round by round, beside the numbers of
values of the verifier's messages, as two lists.

Definitions, statements and proofs, on the chain of Cb/Pv/KeyLookup/Parts.lean. The lists are read
off the blocks by Err.toList and Shape.chalList (Ior/KnowCollRulesChainErr.lean), in the form LL b
es vs of Cb/Ld/LdLkpAsmErrProofs.lean, whose ll_psc and ll_seq are used. An error is a count of
exceptional
values of the round's verifier message; q is the number of elements of E.

Main names:
  partsErrs k: k times pscErrs 0 2 2 = [1, 2, 0].
  partsVals q k: k times pscVals q 0 = [q, q - 1, 1]. So a step has: ε's round 1 of q; the round of
    the further variable 2 of q - 1 (its challenge is never 0); the values' round 0 of 1.
  ll_partsStep: a step has the lists [1, 2, 0] and [q, q - 1, 1].
  ll_after: D.afterA b k has b's lists, then partsErrs k and partsVals q k. ll_alone: D.aloneA k has
    these alone; at k := D.n they are n = m - 1 copies.
  partsErrs_succ, partsVals_succ, partsErrs_length, partsVals_length: a step more; 3 k entries.
  partsErrs_inj, parts_dropped: another number of steps gives another list, whatever stands before
    and behind. (These are facts on the lengths of the two lists.)
  parts_small: every error is below its number of values if 4 ≤ q.

Limits: no premise but 4 ≤ q in parts_small. This file says nothing on what the errors mean, and
nothing on a sum of the fractions.

-/
import Cb.Pv.KeyLookup.Parts
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp

/-- The errors of k parts' steps; the numbers of values beside them. -/
def partsErrs (k : ℕ) : List ℕ := (List.range k).flatMap fun _ => pscErrs 0 2 2
def partsVals (q k : ℕ) : List ℕ := (List.range k).flatMap fun _ => pscVals q 0

theorem partsErrs_succ (k : ℕ) : partsErrs (k + 1) = partsErrs k ++ [1, 2, 0] := by
  unfold partsErrs
  rw [List.range_succ, List.flatMap_append]
  simp [pscErrs]

theorem partsVals_succ (q k : ℕ) : partsVals q (k + 1) = partsVals q k ++ [q, q - 1, 1] := by
  unfold partsVals
  rw [List.range_succ, List.flatMap_append]
  simp [pscVals]

theorem partsErrs_length : ∀ k, (partsErrs k).length = 3 * k
  | 0 => rfl
  | k + 1 => by
    simp only [partsErrs_succ, List.length_append, partsErrs_length k, List.length_cons,
      List.length_nil]
    omega

theorem partsVals_length (q : ℕ) : ∀ k, (partsVals q k).length = 3 * k
  | 0 => rfl
  | k + 1 => by
    simp only [partsVals_succ, List.length_append, partsVals_length q k, List.length_cons,
      List.length_nil]
    omega

/-- Another number of steps: another list. -/
theorem partsErrs_inj {k k' : ℕ} (h : partsErrs k = partsErrs k') : k = k' := by
  have := congrArg List.length h
  rw [partsErrs_length, partsErrs_length] at this
  omega

/-- The tooth: a parts' step dropped, whatever stands before and behind: another list. -/
theorem parts_dropped (a b : List ℕ) (k : ℕ) :
    a ++ partsErrs k ++ b ≠ a ++ partsErrs (k + 1) ++ b := by
  intro h
  have := congrArg List.length h
  simp only [List.length_append, partsErrs_length] at this
  omega

section
variable {E : Type} [Field E] [Fintype E] (D : PartsP E)
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)

theorem ll_partsStep (l : ℕ) :
    LL (D.stepA Ex Wp Kc msg l) [1, 2, 0] [Fintype.card E, Fintype.card E - 1, 1] := by
  cases l with
  | zero => exact ll_psc (D.lv 0).T 0 2 rfl Ex Kc
  | succ l => exact ll_psc (D.lv (l + 1)).T 0 2 rfl Ex Kc

theorem ll_mapA {X X' : Type} (φ : X → X') : LL (mapA Kc M Ex Wp φ) [] [] := ⟨rfl, rfl⟩

theorem ll_after {X : Type} (b : BkA Kc M X (E × (D.lv 0).T.St) Ex Wp) (e v : List ℕ)
    (hb : LL b e v) :
    ∀ k, LL (D.afterA msg b k) (e ++ partsErrs k) (v ++ partsVals (Fintype.card E) k)
  | 0 => by
    have e0 : partsErrs 0 = [] := rfl
    have v0 : partsVals (Fintype.card E) 0 = [] := rfl
    rw [e0, v0, List.append_nil, List.append_nil]
    exact hb
  | k + 1 => by
    have h := ll_seq (ll_after b e v hb k) (ll_partsStep D Ex M Wp Kc msg k)
    rw [partsErrs_succ, partsVals_succ, ← List.append_assoc, ← List.append_assoc]
    exact h

theorem ll_alone (k : ℕ) :
    LL (D.aloneA Ex Wp Kc msg k) (partsErrs k) (partsVals (Fintype.card E) k) :=
  ll_after D Ex M Wp Kc msg _ [] [] (ll_mapA Ex M Wp Kc id) k

end

/-- Pairwise below: every error of k steps is below its number of values, if 4 ≤ q. -/
theorem parts_small (q : ℕ) (hq : 4 ≤ q) :
    ∀ k, List.Forall₂ (fun e v => e < v) (partsErrs k) (partsVals q k)
  | 0 => List.Forall₂.nil
  | k + 1 => by
    rw [partsErrs_succ, partsVals_succ]
    refine List.rel_append (parts_small q hq k) ?_
    exact .cons (by omega) (.cons (by omega) (.cons (by omega) .nil))

/-- At three parts: two steps, six rounds. -/
example : partsErrs (3 - 1) = [1, 2, 0, 1, 2, 0] := by decide

end Lk6
