-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/RideLay.lean: each entry of a table that is sent along (Ride.lay) is the sum of
the table's coins at a public list of numbers, for all k and h, every row and every entry. So
Ride.lay is additive in the coins, and the premises RidesAdd and RidesZero hold for every ride.
Terms: Johnson/SendSim/At/Sim.lean; RidesAdd, RidesZero: Johnson/SendSim/At/Bridge.lean. Limits of
the folder: Johnson/SendSim/Defs.lean.

What this file proves. None of the statements listed here has a premise. Lists and finite sums over
the definition of the format's model prover's packing (Fmt.M1.FoldOwn.freshRow); no distribution is
named.
  ridesAdd, ridesZero   For every ride: the entries of each table that is sent along are additive in
                  its coins (RidesAdd), and are 0 if its coins are all 0 (RidesZero).
  lay_add         R.lay (c + c') r j = R.lay c r j + R.lay c' r j, for all R, c, c', r and j.
  lay_eq          R.lay c r j is the sum of the coins c at entry j of plan R.k R.h r, and 0 beyond
                  the plan's length.
  row_eq          Row b of the packing, read in the field, is the list of the plan's sums.

Limits. Nothing is said on how many entries a coin contributes to, or on whether Ride.lay is
injective.

How it fits. Johnson/SendSim/At/Paid.lean uses ridesAdd and ridesZero to drop the two premises from
four statements of Johnson/SendSim/At/Bridge.lean, so the file serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The proofs
rest on toE_addE, toE_ofE and toE_zeroE (OnBytes/Slice/Field.lean). Ride.lay and hideOfCoins are
defined in Johnson/Desc/ProofFile/Honest/K1/Coins.lean, freshRow in Fmt/M1Fold.lean.

The other names.
  ixOf            the number of the coin that is the coefficient at variable l and degree t.
  sumAt           the sum of the coins at a list of numbers; sumAt_add, sumAt_nil, sumAt_one,
                  sumAt_append.
  firstPlan, plan   for a row: the public lists of numbers, entry by entry.
  toE_w, toE_w0, toE_fold, toE_first, getD_map_toE   read in the field: a coefficient made of coins
                  (hideOfCoins) is the coin; the row's first entry; an entry of a list, or the zero
                  beyond its end.
-/
import Johnson.SendSim.At.Rows

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Fmt.M1.FoldOwn (freshRow reaches)

/-- The number, among a table's 2k + 1 coins, of the coin that is the coefficient at variable l and
degree t (hideOfCoins, Johnson/Desc/ProofFile/Honest/K1/Coins.lean). -/
def ixOf (k l t : ℕ) : ℕ := if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t

/-- The sum of the coins c at a list I of numbers. -/
def sumAt (c : ℕ → GE) (I : List ℕ) : GE := (I.map c).sum

theorem sumAt_nil (c : ℕ → GE) : sumAt c [] = 0 := rfl

theorem sumAt_one (c : ℕ → GE) (n : ℕ) : sumAt c [n] = c n := by simp [sumAt]

theorem sumAt_append (c : ℕ → GE) (I J : List ℕ) : sumAt c (I ++ J) = sumAt c I + sumAt c J := by
  simp [sumAt]

theorem sumAt_add (c c' : ℕ → GE) : ∀ I : List ℕ, sumAt (c + c') I = sumAt c I + sumAt c' I
  | [] => by simp [sumAt]
  | n :: I => by
    have ih := sumAt_add c c' I
    unfold sumAt at ih ⊢
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]
    ring

/-- The numbers of the coins whose sum is the first entry of row b. -/
def firstPlan (k h b : ℕ) : List ℕ :=
  (List.range h).foldl (fun s i => if reaches h b (i + 1) then s ++ [ixOf k (i + 1) 1] else s)
    [if h < k then ixOf k (h + 1) 1 else 2 * (k - 1)]

/-- For row b of a table with the numbers k and h: for each entry, the public list of the numbers of
the coins whose sum is that entry. -/
def plan (k h b : ℕ) : List (List ℕ) :=
  firstPlan k h b ::
    ((List.range h).map fun i => if reaches h b (i + 1) then [ixOf k (i + 1) 2] else []) ++
    (if h < k then
        [ixOf k (h + 1) 2] ::
          ((List.range (k - h - 1)).flatMap fun i =>
            [[ixOf k (h + 2 + i) 1], [ixOf k (h + 2 + i) 2]]) ++
          [[2 * (k - 1)]]
      else [])

theorem toE_w (k : ℕ) (c : ℕ → GE) (l t : ℕ) : toE ((hideOfCoins k c).w l t) = c (ixOf k l t) :=
  toE_ofE _

theorem toE_w0 (k : ℕ) (c : ℕ → GE) : toE (hideOfCoins k c).w0 = c (2 * (k - 1)) := toE_ofE _

theorem toE_fold (k h b : ℕ) (c : ℕ → GE) : ∀ (L : List ℕ) (s : Fmt.M1.E) (I : List ℕ),
    toE s = sumAt c I →
    toE (L.foldl (fun s i => if reaches h b (i + 1) then
        Fmt.Fld.two.addE s ((hideOfCoins k c).w (i + 1) 1) else s) s) =
      sumAt c (L.foldl (fun s i => if reaches h b (i + 1) then s ++ [ixOf k (i + 1) 1] else s) I)
  | [], _, _, h0 => h0
  | i :: L, s, I, h0 => by
    rw [List.foldl_cons, List.foldl_cons]
    refine toE_fold k h b c L _ _ ?_
    by_cases hr : reaches h b (i + 1) = true
    · rw [if_pos hr, if_pos hr, toE_addE, h0, toE_w, sumAt_append, sumAt_one]
    · rw [if_neg hr, if_neg hr, h0]

/-- The first entry of row b of the packing, read in the field, is the sum of the coins at firstPlan
k h b. -/
theorem toE_first (k h b : ℕ) (c : ℕ → GE) :
    toE ((List.range h).foldl (fun s i => if reaches h b (i + 1) then
        Fmt.Fld.two.addE s ((hideOfCoins k c).w (i + 1) 1) else s)
      (if h < k then (hideOfCoins k c).w (h + 1) 1 else (hideOfCoins k c).w0)) =
      sumAt c (firstPlan k h b) := by
  refine toE_fold k h b c _ _ _ ?_
  rw [sumAt_one]
  by_cases hk : h < k
  · rw [if_pos hk, if_pos hk, toE_w]
  · rw [if_neg hk, if_neg hk, toE_w0]

/-- Row b of the packing freshRow, at the coefficients made of the coins c, read in the field, is
the list of the sums of c at the entries of plan k h b. -/
theorem row_eq (k h b : ℕ) (c : ℕ → GE) :
    (freshRow .two k h (hideOfCoins k c) b).map toE = (plan k h b).map (sumAt c) := by
  unfold freshRow plan
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons, toE_first, List.map_map,
    List.map_map]
  refine congrArg₂ (· ++ ·) (congrArg (List.cons _) ?_) ?_
  · refine List.map_congr_left fun i _ => ?_
    show toE (if _ then _ else _) = sumAt c (if _ then _ else _)
    by_cases hr : reaches h b (i + 1) = true
    · rw [if_pos hr, if_pos hr, toE_w, sumAt_one]
    · rw [if_neg hr, if_neg hr, toE_zeroE, sumAt_nil]
  · by_cases hk : h < k
    · rw [if_pos hk, if_pos hk]
      simp only [List.map_cons, List.map_append, List.map_flatMap, List.map_nil, toE_w, toE_w0,
        sumAt_one]
    · rw [if_neg hk, if_neg hk]
      rfl

theorem getD_map_toE (L : List Fmt.M1.E) (j : ℕ) :
    toE (L.getD j Fmt.Fld.zeroE) = (L.map toE).getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[j]? with
  | none => exact toE_zeroE
  | some x => rfl

/-- R.lay c r j is the sum of the coins c at entry j of plan R.k R.h r, and 0 if the plan has no
entry j. -/
theorem lay_eq (R : Ride) (c : ℕ → GE) (r j : ℕ) :
    R.lay c r j = ((plan R.k R.h r).map (sumAt c)).getD j 0 := by
  unfold Ride.lay
  rw [getD_map_toE, row_eq]

/-- Ride.lay is additive in the coins, at every row and every entry. -/
theorem lay_add (R : Ride) (c c' : ℕ → GE) (r j : ℕ) :
    R.lay (c + c') r j = R.lay c r j + R.lay c' r j := by
  rw [lay_eq, lay_eq, lay_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_map]
  cases (plan R.k R.h r)[j]? with
  | none => exact (add_zero _).symm
  | some I => exact sumAt_add c c' I

/-- RidesAdd holds for every ride. -/
theorem ridesAdd (ride : Nat → Option Ride) : RidesAdd ride :=
  fun _ R _ c c' r j _ => lay_add R c c' r j

/-- RidesZero holds for every ride. -/
theorem ridesZero (ride : Nat → Option Ride) : RidesZero ride :=
  ridesZero_of_add ride (ridesAdd ride)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.row_eq
#print axioms OnBytes.SendSim.At.lay_add
#print axioms OnBytes.SendSim.At.ridesAdd
#print axioms OnBytes.SendSim.At.ridesZero
