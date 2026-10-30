-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Rows.lean: the six fields of the honest sender's rows (rowsR) as functions of the
coins. Each entry is 0, an entry of the data, one coin, or, in a table that is sent along, Ride.lay
of the table's coins. So the rows at a sum of two values of the coins are the rows at the first
value plus the rows at no data at the second; for the field mask this is under three public
premises.
Terms: Johnson/SendSim/At/Sim.lean; RidesAdd, RidesZero: Johnson/SendSim/At/Bridge.lean. Limits of
the folder: Johnson/SendSim/Defs.lean.

What this file proves, by unfolding rowsR and by cases.
  mainE_eq, mainF_eq, mainTlE_eq, mainTlF_eq, mask_eq, maskTl_eq   The six fields written out. Each
              is proved by rfl, so the right-hand sides are rowsR's own definition.
  mainE_add, mainF_add, mainTlE_add, mainTlF_add, maskTl_add   For all data and all coins c and c',
              the field at the data and addC c c' is the field at the data and c plus the field at
              no data and c'. No premise.
  mask_add    The same for the field mask, if the job fits its place (sendFits), k < P.sent.size and
              RidesAdd (the entries of a table that is sent along, in its 2 ^ h rows, are additive
              in its coins) holds. RidesAdd holds for every ride (ridesAdd,
              Johnson/SendSim/At/RideLay.lean).
  mask_zadd   With RidesZero (a table that is sent along has entries 0 in its 2 ^ h rows if its
              coins are all 0) in place of RidesAdd: the field mask at the data and c is that field
              at the data and zc plus that field at no data and c.
  ridesZero_of_add, rows_of_ride   RidesAdd implies RidesZero. If the job fits its place, a table
              that is sent along has 2 ^ h mask rows.

How it fits. rowsR is defined in Johnson/Desc/ProofFile/Honest/K1/Coins.lean.
Johnson/SendSim/At/Additive.lean, Johnson/SendSim/At/Split.lean, Johnson/SendSim/At/Cells.lean,
Johnson/SendSim/At/MendsOf.lean and Johnson/SendSim/At/Single.lean build on these. Through
entry_split (Johnson/SendSim/At/Split.lean) they serve rowsExact
(Johnson/SendSim/At/RowsExact.lean); through additiveOf (Johnson/SendSim/At/Additive.lean) they
serve rowsFresh (Johnson/SendSim/At/RowsFresh.lean).

The other names.
  addC, zc    the sum of two values of the coins, coin by coin; the value that is 0 at every coin.
              ce_add, cf_add, ce_zc, cf_zc and zc_add compute with them.
  padIx, coinIx   rowsR's two local tests on an entry of a main row, as definitions: is it a pad's
              entry, and is it a coin.
  rideC       the coins of a table that is sent along, by number; rideC_add, rideC_zc: at a sum, at
              zc.
-/
import Johnson.Desc.ProofFile.Honest.K1.RideOne
import Johnson.SendSim.At.Bridge

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- The sum of two values of the coins, coin by coin. -/
def addC {d : Due} (c c' : Cs d) : Cs d := ⟨c.f + c'.f, c.e + c'.e⟩

/-- The value of the coins that is 0 at every coin. -/
def zc (d : Due) : Cs d := ⟨fun _ => 0, fun _ => 0⟩

theorem ce_add {d : Due} (c c' : Cs d) (n : ℕ) : ce (addC c c') n = ce c n + ce c' n := by
  unfold ce
  by_cases h : n < d.e
  · rw [dif_pos h, dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem cf_add {d : Due} (c c' : Cs d) (n : ℕ) : cf (addC c c') n = cf c n + cf c' n := by
  unfold cf
  by_cases h : n < d.f
  · rw [dif_pos h, dif_pos h, dif_pos h]
    rfl
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem ce_zc (d : Due) (n : ℕ) : ce (zc d) n = 0 := by
  unfold ce
  split <;> rfl

theorem cf_zc (d : Due) (n : ℕ) : cf (zc d) n = 0 := by
  unfold cf
  split <;> rfl

theorem zc_add {d : Due} (c : Cs d) : addC (zc d) c = c := by
  cases c
  simp [addC, zc]
  constructor <;> funext i <;> simp

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- rowsR's local test whether entry j of main row r of oracle message k is a pad's entry. If so, it
gives the entry's number among the pad's coins. -/
def padIx (k r j : ℕ) : Option ℕ :=
  if (stp P ride k).pad != 0 && r + 1 == (shapeAt P k).mainRows &&
      decide ((P.codes.base.getD (shapeAt P k).code default).ell - (stp P ride k).pad ≤ j) &&
      decide (j < (P.codes.base.getD (shapeAt P k).code default).ell) then
    some (j - ((P.codes.base.getD (shapeAt P k).code default).ell - (stp P ride k).pad)) else none

/-- rowsR's local test whether entry j of main row r of oracle message k is a coin. If so, it gives
the coin's number among the coins of the oracle message's main rows. -/
def coinIx (k r j : ℕ) : Option ℕ :=
  if (stp P ride k).word != 0 then
    (if j < (P.codes.base.getD (shapeAt P k).code default).ell then
      some ((stp P ride k).tails + r * (P.codes.base.getD (shapeAt P k).code default).ell + j)
    else none)
  else (padIx P ride k r j).map ((stp P ride k).tails + ·)

variable (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k : ℕ)

/-- The field mainE of rowsR, written out. The next five lemmas do the same for the other fields;
each is proved by rfl. -/
theorem mainE_eq (r j : ℕ) :
    (rowsR P ride data c k).mainE r j =
      if !((shapeAt P k).mainDeg == 3) || decide ((shapeAt P k).mainRows ≤ r) ||
          decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) then 0 else
        match coinIx P ride k r j with
        | some i => ce c ((startR P ride k).e + i)
        | none =>
          match data k r j with
          | some (.inr x) => x
          | some (.inl x) => algebraMap GF GE x
          | none => 0 := rfl

theorem mainF_eq (r j : ℕ) :
    (rowsR P ride data c k).mainF r j =
      if ((shapeAt P k).mainDeg == 3) || decide ((shapeAt P k).mainRows ≤ r) ||
          decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) then 0 else
        match coinIx P ride k r j with
        | some i => cf c ((startR P ride k).f + i)
        | none =>
          match data k r j with
          | some (.inl x) => x
          | _ => 0 := rfl

theorem mainTlE_eq (r q : ℕ) :
    (rowsR P ride data c k).mainTlE r q =
      if ((shapeAt P k).mainDeg == 3) && decide (r < (shapeAt P k).mainRows) &&
          decide (q < (P.codes.base.getD (shapeAt P k).code default).r) then
        ce c ((startR P ride k).e + r * (P.codes.base.getD (shapeAt P k).code default).r + q)
      else 0 := rfl

theorem mainTlF_eq (r q : ℕ) :
    (rowsR P ride data c k).mainTlF r q =
      if !((shapeAt P k).mainDeg == 3) && decide (r < (shapeAt P k).mainRows) &&
          decide (q < (P.codes.base.getD (shapeAt P k).code default).r) then
        cf c ((startR P ride k).f + r * (P.codes.base.getD (shapeAt P k).code default).r + q)
      else 0 := rfl

/-- The coins of a table R that is sent along as oracle message k, by number: the first R.count mask
coins of that oracle message, and 0 from R.count on. -/
def rideC (R : Ride) (i : ℕ) : GE := if i < R.count then ce c (maskStart P ride k + i) else 0

theorem mask_eq (r j : ℕ) :
    (rowsR P ride data c k).mask r j =
      match ride k with
      | some R =>
        if r < (shapeAt P k).maskRows ∧ j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell
        then R.lay (rideC P ride c k R) r j else 0
      | none =>
        if r < (shapeAt P k).maskRows ∧ j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell
        then ce c (maskStart P ride k + j * (shapeAt P k).maskRows + r) else 0 := rfl

theorem maskTl_eq (r q : ℕ) :
    (rowsR P ride data c k).maskTl r q =
      if r < (shapeAt P k).maskRows ∧ q < (P.codes.mask.getD (shapeAt P k).maskCode default).r then
        ce c (maskStart P ride k + (stp P ride k).mask +
          r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q)
      else 0 := rfl

/-! ## At a sum of two values of the coins -/

variable (c' : Cs (dueR P ride))

/-- The field mainE at the data and addC c c' is that field at the data and c plus that field at no
data and c'. The next four lemmas say the same of mainF, mainTlE, mainTlF and maskTl. -/
theorem mainE_add (r j : ℕ) :
    (rowsR P ride data (addC c c') k).mainE r j =
      (rowsR P ride data c k).mainE r j + (rowsR P ride (fun _ _ _ => none) c' k).mainE r j := by
  rw [mainE_eq, mainE_eq, mainE_eq]
  split
  · rw [add_zero]
  · cases coinIx P ride k r j with
    | some i => exact ce_add c c' _
    | none => exact (add_zero _).symm

theorem mainF_add (r j : ℕ) :
    (rowsR P ride data (addC c c') k).mainF r j =
      (rowsR P ride data c k).mainF r j + (rowsR P ride (fun _ _ _ => none) c' k).mainF r j := by
  rw [mainF_eq, mainF_eq, mainF_eq]
  split
  · rw [add_zero]
  · cases coinIx P ride k r j with
    | some i => exact cf_add c c' _
    | none => exact (add_zero _).symm

theorem mainTlE_add (r q : ℕ) :
    (rowsR P ride data (addC c c') k).mainTlE r q =
      (rowsR P ride data c k).mainTlE r q +
        (rowsR P ride (fun _ _ _ => none) c' k).mainTlE r q := by
  rw [mainTlE_eq, mainTlE_eq, mainTlE_eq]
  split
  · exact ce_add c c' _
  · rw [add_zero]

theorem mainTlF_add (r q : ℕ) :
    (rowsR P ride data (addC c c') k).mainTlF r q =
      (rowsR P ride data c k).mainTlF r q +
        (rowsR P ride (fun _ _ _ => none) c' k).mainTlF r q := by
  rw [mainTlF_eq, mainTlF_eq, mainTlF_eq]
  split
  · exact cf_add c c' _
  · rw [add_zero]

theorem maskTl_add (r q : ℕ) :
    (rowsR P ride data (addC c c') k).maskTl r q =
      (rowsR P ride data c k).maskTl r q +
        (rowsR P ride (fun _ _ _ => none) c' k).maskTl r q := by
  rw [maskTl_eq, maskTl_eq, maskTl_eq]
  split
  · exact ce_add c c' _
  · rw [add_zero]

theorem rideC_add (R : Ride) :
    rideC P ride (addC c c') k R = rideC P ride c k R + rideC P ride c' k R := by
  funext i
  show rideC P ride (addC c c') k R i = rideC P ride c k R i + rideC P ride c' k R i
  unfold rideC
  split
  · exact ce_add c c' _
  · rw [add_zero]

/-- If the job fits its place (sendFits) and k < P.sent.size, a table that is sent along as oracle
message k has 2 ^ h mask rows. -/
theorem rows_of_ride (hf : sendFits P ride = true) (hk : k < P.sent.size) (R : Ride)
    (hr : ride k = some R) : (shapeAt P k).maskRows = 2 ^ R.h := by
  have h := fits_ride P ride k R hf hk hr
  simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

/-- If the job fits its place (sendFits), RidesAdd holds and k < P.sent.size, the field mask at the
data and addC c c' is that field at the data and c plus that field at no data and c'. -/
theorem mask_add (hf : sendFits P ride = true) (hR : RidesAdd ride) (hk : k < P.sent.size)
    (r j : ℕ) :
    (rowsR P ride data (addC c c') k).mask r j =
      (rowsR P ride data c k).mask r j + (rowsR P ride (fun _ _ _ => none) c' k).mask r j := by
  rw [mask_eq, mask_eq, mask_eq]
  cases hr : ride k with
  | none =>
    simp only
    split
    · exact ce_add c c' _
    · rw [add_zero]
  | some R =>
    simp only
    split
    · rename_i hg
      rw [rideC_add]
      exact hR k R hr _ _ r j (by rw [← rows_of_ride P ride k hf hk R hr]; exact hg.1)
    · rw [add_zero]

/-- RidesAdd implies RidesZero. -/
theorem ridesZero_of_add (hR : RidesAdd ride) : RidesZero ride := fun k R hr r j h => by
  have e := hR k R hr 0 0 r j h
  rw [add_zero] at e
  exact left_eq_add.mp e

theorem rideC_zc (R : Ride) : rideC P ride (zc _) k R = 0 := by
  funext i
  show rideC P ride (zc _) k R i = 0
  unfold rideC
  rw [ce_zc, ite_self]

/-- If the job fits its place (sendFits), RidesZero holds and k < P.sent.size, the field mask at the
data and c is that field at the data and coins that are all 0 plus that field at no data and c. -/
theorem mask_zadd (hf : sendFits P ride = true) (hZ : RidesZero ride) (hk : k < P.sent.size)
    (r j : ℕ) :
    (rowsR P ride data c k).mask r j =
      (rowsR P ride data (zc _) k).mask r j + (rowsR P ride (fun _ _ _ => none) c k).mask r j := by
  rw [mask_eq, mask_eq, mask_eq]
  cases hr : ride k with
  | none =>
    simp only [ce_zc, ite_self, zero_add]
  | some R =>
    simp only
    split
    · rename_i hg
      rw [rideC_zc, hZ k R hr r j (by rw [← rows_of_ride P ride k hf hk R hr]; exact hg.1),
        zero_add]
    · rw [add_zero]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.mask_zadd
#print axioms OnBytes.SendSim.At.mainE_add
#print axioms OnBytes.SendSim.At.mask_add
