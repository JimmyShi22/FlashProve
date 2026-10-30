-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsStd.lean: where the own mask entries of the parts' steps stand, as a function
of one numbering of mask entries; and the formats of their rounds against the list of rounds.

Definitions, statements and proofs. The verifier's output as a plain function of the flat transcript
(A.partsRun, Cb/Pv/KeyLookup/PartsRun.lean) has two letters wP, cP for the places. Here they get a
value: step l takes five entries in a row from the number b + 5 l on.

Main names:
  Parts.wStd ms b, Parts.cStd ms b: ms : ℕ → J numbers the mask entries; b is the number of the
    first entry of step 0. Step l: the constant of its polynomial in the further variable at
    b + 5 l, the coefficients of the first and second power at b + 5 l + 1 and + 2, the entry of the
    first value (the root's) at + 3, that of the second (the rest's) at + 4.
  Parts.placesOf w c k: the places of k steps, step by step, in that order.
  Parts.places_std: the places of k steps at wStd, cStd are ms b, ms (b + 1), .., ms (b + 5 k - 1),
    in order: each number from b to b + 5 k - 1 once. The places themselves are pairwise different
    if ms is one-to-one on the numbers below some N ≥ b + 5 k (places_nodup). (On all of ℕ no ms is
    one-to-one: J is finite in every use.)
  Parts.rowFm: the format of a round of a sumcheck, read off a row of the list of rounds in short
    form: as many scalars as the row says; no drawn element in a values' round, else one; the draw
    is not 0 in the round of the further variable. NOT the format of a row of kind join or zero.
  Parts.fmK_lam: the formats Parts.fmK k of k steps are lamSteps q k under rowFm, for every q.

Limits: no premise but that ms is one-to-one below N, in places_nodup. Nothing is said on the number
b: that the steps before the parts' steps take the entries below b is not this file's matter.

-/
import Cb.Pv.KeyLookup.PartsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Parts
open Cb Cb.LdLkp Flat

section
variable {E : Type} [Field E] [Fintype E] {J : Type}

/-- The three coefficients' places at step l. -/
def wStd (ms : ℕ → J) (b l : ℕ) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 2])) : J :=
  match (i : Fin 2 ⊕ Unit) with
  | .inr _ => ms (b + 5 * l)
  | .inl t => ms (b + 5 * l + 1 + t.val)

/-- The two values' places at step l. -/
def cStd (ms : ℕ → J) (b l : ℕ) (v : Bool) : J := ms (b + 5 * l + (if v then 4 else 3))

/-- The places of k steps, step by step. -/
def placesOf (w : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J) (c : ℕ → Bool → J) (k : ℕ) :
    List J :=
  (List.range k).flatMap fun l => [w l i0, w l i1, w l i2, c l false, c l true]

theorem places_std (ms : ℕ → J) (b : ℕ) : ∀ k,
    placesOf (wStd (E := E) ms b) (cStd ms b) k = (List.range (5 * k)).map fun t => ms (b + t)
  | 0 => rfl
  | k + 1 => by
    have e : 5 * (k + 1) = 5 * k + 1 + 1 + 1 + 1 + 1 := by ring
    unfold placesOf
    rw [List.range_succ, List.flatMap_append, e]
    simp only [List.range_succ, List.map_append, List.append_assoc]
    have h := places_std ms b k
    unfold placesOf at h
    rw [h]
    simp [wStd, cStd, i0, i1, i2, Nat.add_assoc]

theorem places_nodup (ms : ℕ → J) (N : ℕ) (hm : ∀ s t, s < N → t < N → ms s = ms t → s = t)
    (b k : ℕ) (hN : b + 5 * k ≤ N) : (placesOf (wStd (E := E) ms b) (cStd ms b) k).Nodup := by
  rw [places_std]
  refine List.Nodup.map_on (fun s hs t ht h => ?_) List.nodup_range
  have h1 := List.mem_range.1 hs
  have h2 := List.mem_range.1 ht
  exact Nat.add_left_cancel (hm _ _ (by omega) (by omega) h)

end

/-- The format of a round of a sumcheck, read off its row in short form. NOT the format of a row of
kind join or zero. -/
def rowFm (r : LRow) : Fm := ⟨r.short.sent, if r.kind == .vals then 0 else 1, r.kind == .y⟩

theorem fmK_lam (q : ℕ) : ∀ k, fmK k = (lamSteps q k).map rowFm
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, ← fmK_lam q k]
    rfl

end Parts
end Lk6

#print axioms Lk6.Parts.places_std
#print axioms Lk6.Parts.places_nodup
#print axioms Lk6.Parts.fmK_lam
