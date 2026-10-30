-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Single.lean: if the job fits its place, a family of message coins that is 0
except at one coin contributes only to rows and answers of that coin's oracle message and, where
that oracle message is not sent along, only to the entry at which the coin's slot is located.
Terms: Johnson/SendSim/At/Sim.lean; maskTailNo: Johnson/SendSim/At/Fresh.lean; sender, put, slot,
name, number: Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Algebra; no distribution is named. In each, the job fits its place
(sendFits), u is a name in CoinN, and the family of message coins has one value at u and 0
elsewhere.
  lay_other_msg  lay of that family is 0 in every row of another oracle message than u's.
  lay_cell       In a row ρ of an oracle message that is not sent along (ride ρ.1 = none), lay of
                 that family is 0 at every entry at which u's slot is not located.
  wt_other_msg   That family contributes 0 to every answer of another oracle message than u's.

How it fits. Johnson/SendSim/At/ClearOfMask.lean uses the three lemmas,
Johnson/SendSim/At/ClearOfFold.lean lay_other_msg and wt_other_msg, and
Johnson/SendSim/At/FoldAny.lean lay_other_msg, to prove Sender.Clear (Johnson/SendSim/Pads.lean), so
the model's premise MendsOff, for rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny
(Johnson/SendSim/At/FreshWideProofs.lean). The proofs rest on rd_single and wt_eq
(Johnson/SendSim/At/PadsOf.lean), form_none (Johnson/SendSim/At/FormOne.lean), coinNo_put_zero
(Johnson/SendSim/At/Cells.lean) and ridesZero (Johnson/SendSim/At/RideLay.lean).

The other names.
  tbOf, rowOf, tbOf_or   the array of a row (main or mask); the row's number in it.
  entry_rd       an entry of a row's message is a coordinate of the array's entry as rdAt reads it.
  rideC_put_zero   put s is 0 at the coins of a table that is sent along as oracle message k, if s
                 is 0 at all names of k.
  no_maskTail, no_mask   the numbers of an entry of a mask row's tail (maskTailNo) and of a mask
                 coin.
-/
import Johnson.SendSim.At.MendsOf
import Johnson.SendSim.At.RideLay
import Johnson.SendSim.At.Fresh

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride}

/-- The array of a row's message: main for a main row, mask for a mask row. -/
def tbOf (ρ : RowN P) : Rd :=
  match ρ.2 with
  | .inl _ => .main
  | .inr _ => .mask

/-- The row's number among its oracle message's main rows, or among its mask rows. -/
def rowOf (ρ : RowN P) : ℕ :=
  match ρ.2 with
  | .inl x => x.1.val
  | .inr x => x.1.val

theorem tbOf_or (ρ : RowN P) : tbOf ρ = .main ∨ tbOf ρ = .mask := by
  obtain ⟨k, v⟩ := ρ
  rcases v with v | v
  · exact .inl rfl
  · exact .inr rfl

/-- An entry of a row's message (entry) is some coordinate of the entry of the row's array as rdAt
reads it, in the extension field. -/
theorem entry_rd (V : ℕ → Rows) (ρ : RowN P) (j : ℕ) :
    ∃ t : Fin 3, entry P V ρ j =
      crd t (rdAt (V ρ.1) ((shapeAt P ρ.1).mainDeg == 3) (tbOf ρ) (rowOf ρ) j) := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · refine ⟨co t.val, ?_⟩
      show (if (shapeAt P k).mainDeg == 3 then _ else _) = crd _ (Rows.main _ _ _ _)
      unfold Rows.main
      rw [if_pos h3, if_pos h3]
      rfl
    · refine ⟨0, ?_⟩
      show (if (shapeAt P k).mainDeg == 3 then _ else _) = crd _ (Rows.main _ _ _ _)
      unfold Rows.main
      rw [if_neg h3, if_neg h3, crd_cast, if_pos rfl]
      rfl
  · exact ⟨t, rfl⟩

/-- If s is 0 at every name of oracle message k, which is a table R that is sent along, then put s
is 0 at that table's coins. -/
theorem rideC_put_zero (s : CoinN P ride → GF) (k : Fin P.sent.size) (R : Ride)
    (hr : ride k = some R) (h0 : ∀ n : CoinN P ride, n.1 = k → s n = 0) :
    rideC P ride (put P ride s) k R = 0 := by
  funext i
  show rideC P ride (put P ride s) k R i = 0
  unfold rideC
  split
  · rename_i hi
    have hy : (Seat.mask i).ok P.codes (shapeAt P k) (ride k) := by
      show i < (stepsOf P.codes (shapeAt P k) (ride k)).mask
      simpa [stepsOf, hr] using hi
    have h := coinNo_put_zero P ride s k (.mask i) hy rfl fun n hn _ => h0 n hn
    unfold coinNo Seat.no at h
    simp only [Seat.inE, if_true] at h
    rwa [mask_no] at h
  · rfl

variable [inst : DecidableEq (CoinN P ride)]

/-- If the job fits its place (sendFits), lay of one value at the name u is 0 in every row of
another oracle message than u's. -/
theorem lay_other_msg (hf : sendFits P ride = true) (u : CoinN P ride) (a : GF) (ρ : RowN P)
    (j : ℕ) (h : ρ.1 ≠ u.1) : layN (Pi.single u a : CoinN P ride → GF) ρ j = 0 := by
  cases hr : ride ρ.1 with
  | none =>
    obtain ⟨t, e⟩ := entry_rd (rowsR P ride (fun _ _ _ => none) (put P ride (Pi.single u a))) ρ j
    unfold layN
    rw [e, rd_single hf u a ρ.1 hr (tbOf ρ) (tbOf_or ρ) (rowOf ρ) j fun hh => h hh.1, crd_zero]
  | some R =>
    obtain ⟨k, v⟩ := ρ
    rcases v with ⟨r, t⟩ | ⟨r, t⟩
    · exfalso
      have hfit := fits_ride P ride k R hf k.isLt hr
      simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
      have := r.isLt
      omega
    · show crd t
        ((rowsR P ride (fun _ _ _ => none) (put P ride (Pi.single u a)) k).mask r.val j) = 0
      rw [mask_eq]
      simp only [hr]
      rw [rideC_put_zero _ k R hr fun n hn => by
        rw [Pi.single_apply, if_neg fun e => h (by rw [← e]; exact hn.symm)]]
      split
      · rename_i hg
        rw [ridesZero ride k R hr r.val j
          (by rw [← rows_of_ride P ride k hf k.isLt R hr]; exact hg.1), crd_zero]
      · exact crd_zero t

/-- If the job fits its place (sendFits) and the oracle message of the row ρ is not sent along, lay
of one value at the name u is 0 at entry j of ρ unless u's slot is located there. -/
theorem lay_cell (hf : sendFits P ride = true) (u : CoinN P ride) (a : GF) (ρ : RowN P) (j : ℕ)
    (hr : ride ρ.1 = none)
    (h : (seatC P ride u).1.place P.codes (shapeAt P ρ.1) (ride ρ.1) ≠ (tbOf ρ, rowOf ρ, j)) :
    layN (Pi.single u a : CoinN P ride → GF) ρ j = 0 := by
  obtain ⟨t, e⟩ := entry_rd (rowsR P ride (fun _ _ _ => none) (put P ride (Pi.single u a))) ρ j
  unfold layN
  rw [e, rd_single hf u a ρ.1 hr (tbOf ρ) (tbOf_or ρ) (rowOf ρ) j fun hh => h hh.2, crd_zero]

/-- If the job fits its place (sendFits), one value at the name u contributes 0 to every answer of
another oracle message than u's. -/
theorem wt_other_msg (ds : List Fmt.Drawn) (hf : sendFits P ride = true) (u : CoinN P ride)
    (x : GF) (b : AnsN P) (h : b.1 ≠ u.1) :
    (sender P ride).wt (wOf P ds) (Pi.single u x : CoinN P ride → GF) b = 0 := by
  obtain ⟨k, i, s⟩ := b
  have hr : ride k = none := fits_noRide P ride k hf k.isLt (by have := i.isLt; omega)
  rw [wt_eq P ride ds hf, form_none P.codes (shapeAt P k) _ _ _ _
    (fun r' j' => rd_single hf u x k hr .main (.inl rfl) r' j' fun hh => h hh.1)
    (fun r' j' => rd_single hf u x k hr .mask (.inr rfl) r' j' fun hh => h hh.1),
    mul_zero, crd_zero]

omit inst in
theorem no_maskTail (k r q : ℕ) :
    (Seat.maskTail r q).no P ride k = maskTailNo P ride k r q := by
  simp only [Seat.no, Seat.inE, Seat.off, maskTailNo, maskStart, if_true, Nat.add_assoc]

omit inst in
theorem no_mask (k i : ℕ) : (Seat.mask i).no P ride k = maskStart P ride k + i := mask_no P ride k i

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.lay_other_msg
#print axioms OnBytes.SendSim.At.lay_cell
#print axioms OnBytes.SendSim.At.wt_other_msg
