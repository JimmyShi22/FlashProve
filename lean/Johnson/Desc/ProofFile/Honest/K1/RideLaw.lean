-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/RideLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: THE RIDING ARM OF STEP (4) OF THE ORDER (the head of Honest/K1/Coins.lean): the
mask entries of a message whose table rides. A definition, statements and proofs.

  ride_coin     these entries are Ride.lay of the message's R.count coins, which begin at maskStart
  pairs_length, pairs_get   a list of pairs, by index
  fresh_one     the format's model prover's row (Fmt.M1.FoldOwn.freshRow, Fmt/M1Fold.lean) at one
                row (h = 0), written out
  sig           AT ONE ROW: which coin stands at the place p: the places follow the table's columns
                (variable by variable, degrees 1 and 2; the constant last), the coins the
                polynomial's own order (the constant in front of the last variable's two)
  lay_one, lay_one_beyond   at one row and 1 ≤ k: the place p ≤ 2 k holds the coin number sig k p;
                beyond: 0
  sig_lt, sig_inj, sig_onto   sig k maps the places 0 ... 2 k into the numbers 0 ... 2 k, one to one
                and onto

Limits. AT MORE THAN ONE ROW (h > 0) THERE IS NO LAW HERE ON HOW THE COINS ARE LAID: there a
coefficient stands at more than one place; that the laying is one to one, on the coins below
`Ride.count`, at every ride with h ≤ k, is lay_fixes (RideFixes.lean of this folder); that it is
additive in the coins is lay_add (Johnson/SendSim/At/RideLay.lean). What is WRITTEN where: no
sentence on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import OnBytes.Slice.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- **The riding arm.** -/
theorem ride_coin (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k r j : Nat) (R : Ride)
    (hr : ride k = some R) (hρ : r < (shapeAt P k).maskRows)
    (hj : j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (rowsR P ride data cs k).mask r j =
      R.lay (fun i => if i < R.count then ce cs (maskStart P ride k + i) else 0) r j := by
  simp only [rowsR, hr]
  rw [if_pos ⟨hρ, hj⟩]
  simp only [maskStart, hr]

/-! ## One row -/

theorem pairs_length {α : Type} (f g : Nat → α) :
    ∀ n, ((List.range n).flatMap fun i => [f i, g i]).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, pairs_length f g n]
    rfl

theorem pairs_get {α : Type} (f g : Nat → α) : ∀ (n p : Nat), p < 2 * n →
    ((List.range n).flatMap fun i => [f i, g i])[p]? =
      some (if p % 2 = 0 then f (p / 2) else g (p / 2))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, p, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hp : p < 2 * n
    · rw [List.getElem?_append_left (by rw [pairs_length]; exact hp)]
      exact pairs_get f g n p hp
    · rw [List.getElem?_append_right (by rw [pairs_length]; omega), pairs_length]
      rcases (by omega : p = 2 * n ∨ p = 2 * n + 1) with e | e
      · subst e
        rw [Nat.sub_self, Nat.mul_mod_right, if_pos rfl, Nat.mul_div_cancel_left _ (by decide)]
        rfl
      · subst e
        rw [Nat.add_sub_cancel_left, (by omega : (2 * n + 1) % 2 = 1),
          (by omega : (2 * n + 1) / 2 = n), if_neg (by decide)]
        rfl

/-- The model prover's row at one row, written out. -/
theorem fresh_one (f : Fmt.Fld) (k : Nat) (U : Fmt.M1.FoldOwn.Hide) (b : Nat) (hk : 1 ≤ k) :
    Fmt.M1.FoldOwn.freshRow f k 0 U b =
      U.w 1 1 :: U.w 1 2 ::
        (((List.range (k - 1)).flatMap fun i => [U.w (2 + i) 1, U.w (2 + i) 2]) ++ [U.w0]) := by
  unfold Fmt.M1.FoldOwn.freshRow
  rw [if_pos (show 0 < k from hk), if_pos (show 0 < k from hk)]
  rfl

/-- **At one row: which coin stands at the place p.** -/
def sig (k p : Nat) : Nat :=
  if p + 2 < 2 * k then p else if p + 2 = 2 * k then 2 * k - 1 else if p + 1 = 2 * k then 2 * k
  else 2 * k - 2

theorem lay_one (k p : Nat) (c : Nat → GE) (hk : 1 ≤ k) (hp : p ≤ 2 * k) :
    (⟨k, 0⟩ : Ride).lay c 0 p = c (sig k p) := by
  show toE ((Fmt.M1.FoldOwn.freshRow .two k 0 (hideOfCoins k c) 0).getD p Fmt.Fld.zeroE) = _
  rw [fresh_one _ _ _ _ hk]
  match p, hp with
  | 0, _ =>
    show toE (ofE (c (if 1 < k then 2 * (1 - 1) + (1 - 1) else 2 * (k - 1) + 1))) = _
    rw [toE_ofE]
    congr 1
    unfold sig
    split_ifs <;> omega
  | 1, _ =>
    show toE (ofE (c (if 1 < k then 2 * (1 - 1) + (2 - 1) else 2 * (k - 1) + 2))) = _
    rw [toE_ofE]
    congr 1
    unfold sig
    split_ifs <;> omega
  | q + 2, hq =>
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem?_getD]
    by_cases h : q < 2 * (k - 1)
    · rw [List.getElem?_append_left (by rw [pairs_length]; exact h), pairs_get _ _ _ _ h,
        Option.getD_some]
      by_cases h2 : q % 2 = 0
      · rw [if_pos h2]
        show toE (ofE (c (if 2 + q / 2 < k then 2 * (2 + q / 2 - 1) + (1 - 1)
          else 2 * (k - 1) + 1))) = _
        rw [toE_ofE]
        congr 1
        unfold sig
        split_ifs <;> omega
      · rw [if_neg h2]
        show toE (ofE (c (if 2 + q / 2 < k then 2 * (2 + q / 2 - 1) + (2 - 1)
          else 2 * (k - 1) + 2))) = _
        rw [toE_ofE]
        congr 1
        unfold sig
        split_ifs <;> omega
    · rw [List.getElem?_append_right (by rw [pairs_length]; omega), pairs_length,
        (by omega : q - 2 * (k - 1) = 0)]
      show toE (ofE (c (2 * (k - 1)))) = _
      rw [toE_ofE]
      congr 1
      unfold sig
      split_ifs <;> omega

theorem lay_one_beyond (k p : Nat) (c : Nat → GE) (hk : 1 ≤ k) (hp : 2 * k < p) :
    (⟨k, 0⟩ : Ride).lay c 0 p = 0 := by
  show toE ((Fmt.M1.FoldOwn.freshRow .two k 0 (hideOfCoins k c) 0).getD p Fmt.Fld.zeroE) = _
  rw [fresh_one _ _ _ _ hk, List.getD_eq_default _ _ (by
    simp only [List.length_cons, List.length_append, pairs_length, List.length_nil]
    omega)]
  exact toE_zeroE

theorem sig_lt (k p : Nat) (hk : 1 ≤ k) (hp : p ≤ 2 * k) : sig k p ≤ 2 * k := by
  unfold sig
  split_ifs <;> omega

theorem sig_inj (k p q : Nat) (hk : 1 ≤ k) (hp : p ≤ 2 * k) (hq : q ≤ 2 * k)
    (h : sig k p = sig k q) : p = q := by
  unfold sig at h
  split_ifs at h <;> omega

theorem sig_onto (k n : Nat) (hk : 1 ≤ k) (hn : n ≤ 2 * k) : ∃ p, p ≤ 2 * k ∧ sig k p = n := by
  by_cases h1 : n + 2 < 2 * k
  · exact ⟨n, hn, by unfold sig; rw [if_pos h1]⟩
  · rcases (by omega : n = 2 * k - 2 ∨ n = 2 * k - 1 ∨ n = 2 * k) with e | e | e
    · exact ⟨2 * k, Nat.le_refl _, by unfold sig; split_ifs <;> omega⟩
    · exact ⟨2 * k - 2, by omega, by unfold sig; split_ifs <;> omega⟩
    · exact ⟨2 * k - 1, by omega, by unfold sig; split_ifs <;> omega⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ride_coin
#print axioms ProofFile.Honest.K1.pairs_length
#print axioms ProofFile.Honest.K1.pairs_get
#print axioms ProofFile.Honest.K1.fresh_one
#print axioms ProofFile.Honest.K1.lay_one
#print axioms ProofFile.Honest.K1.lay_one_beyond
#print axioms ProofFile.Honest.K1.sig_lt
#print axioms ProofFile.Honest.K1.sig_inj
#print axioms ProofFile.Honest.K1.sig_onto
#print axioms ProofFile.Honest.K1.sig
