-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Split.lean: if the job fits its place and RidesZero holds, the message of each of
the honest sender's rows is dataOf data plus the instance's lay of the coins readC c; and, with no
premise, the row's tail is the tail in readC c.
Terms: Johnson/SendSim/At/Sim.lean; sender, readC, dataOf, put, slot, number, RidesZero:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Algebra; no distribution is named.
  entry_split  If the job fits its place (sendFits) and RidesZero (a table that is sent along has
               entries 0 in its 2 ^ h rows if its coins are all 0) holds, then for all data, coins
               c, rows ρ and j: entry (rowsR data c) ρ j = dataOf data ρ j + lay (readC c).1 ρ j.
  tail_split   For all data, c, ρ and every q below the tail's length: tailEntry (rowsR data c) ρ q
               = (readC c).2 ρ q. No premise.
  entry_read   At no data, a row's entries are the same at the coins c and at put (readC c).1. No
               premise. mainE_read, mainF_read and mask_read say it of the three fields of rowsR
               that hold rows' messages.

Limits. RidesZero is a premise of entry_split; it holds for every ride (ridesZero,
Johnson/SendSim/At/RideLay.lean).

How it fits. Johnson/SendSim/At/Symbols.lean uses entry_split and tail_split, and
Johnson/SendSim/At/Answers.lean uses entry_split, to connect the sender's symbols and answers with
the instance's. That gives shownTie (Johnson/SendSim/At/Shown.lean), which serves rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The proofs
rest on coinNo_put_read (Johnson/SendSim/At/Names.lean), entry_zadd
(Johnson/SendSim/At/Additive.lean) and the six fields of rowsR as written out in
Johnson/SendSim/At/Rows.lean.

The other names.
  coinIx_seat  where rowsR's test coinIx finds a coin at an entry of a main row, that coin is at a
               slot that is within the sizes and not in a tail, with the number that the test gives.
  ce_put_read, cf_put_read, ce_mask_read   at the number of such a slot, and of a mask coin, put
               (readC c).1 and c have the same coin.
  mask_no      the number of mask coin i is maskStart P ride k + i.
-/
import Johnson.SendSim.At.Additive
import Johnson.SendSim.At.Names

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- If rowsR's test coinIx gives the number i at entry j of main row r, with r and j within the
sizes, then some slot that is within the sizes and not in a tail, in the main rows' field, has the
number i among the oracle message's coins. -/
theorem coinIx_seat (k r j i : ℕ) (h : coinIx P ride k r j = some i)
    (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    ∃ x : Seat, x.ok P.codes (shapeAt P k) (ride k) ∧ inMsg x = true ∧
      x.inE (shapeAt P k) = ((shapeAt P k).mainDeg == 3) ∧
      x.off P.codes (shapeAt P k) (ride k) = i := by
  unfold coinIx at h
  by_cases hw : ((stp P ride k).word != 0) = true
  · rw [if_pos hw, if_pos hj] at h
    refine ⟨.word r j, ⟨by simpa [stp] using hw, hr, hj⟩, rfl, rfl, ?_⟩
    exact Option.some.inj h
  · rw [if_neg hw] at h
    unfold padIx at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hc
      refine ⟨.pad (j - ((P.codes.base.getD (shapeAt P k).code default).ell - (stp P ride k).pad)),
        ?_, rfl, rfl, Option.some.inj h⟩
      show _ < (stp P ride k).pad
      omega
    · cases h

variable (c : Cs (dueR P ride))

theorem ce_put_read (k : Fin P.sent.size) (x : Seat)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg x = true)
    (hE : x.inE (shapeAt P k) = true) :
    ce (put P ride (readC P ride c).1)
        ((startR P ride k).e + x.off P.codes (shapeAt P k) (ride k)) =
      ce c ((startR P ride k).e + x.off P.codes (shapeAt P k) (ride k)) := by
  have h := coinNo_put_read P ride c k x hx hm
  unfold coinNo Seat.no at h
  simpa only [hE, if_true] using h

theorem cf_put_read (k : Fin P.sent.size) (x : Seat)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg x = true)
    (hE : x.inE (shapeAt P k) = false) :
    cf (put P ride (readC P ride c).1)
        ((startR P ride k).f + x.off P.codes (shapeAt P k) (ride k)) =
      cf c ((startR P ride k).f + x.off P.codes (shapeAt P k) (ride k)) := by
  have h := coinNo_put_read P ride c k x hx hm
  unfold coinNo Seat.no at h
  simp only [hE, Bool.false_eq_true, if_false] at h
  exact Code.Cubic.algebraMap_injective h

/-- At no data, the field mainE of rowsR is the same at the coins put (readC c).1 and at c. The next
two lemmas say the same of the fields mainF and mask. -/
theorem mainE_read (k : Fin P.sent.size) (r j : ℕ) :
    (rowsR P ride (fun _ _ _ => none) (put P ride (readC P ride c).1) k).mainE r j =
      (rowsR P ride (fun _ _ _ => none) c k).mainE r j := by
  rw [mainE_eq, mainE_eq]
  split
  · rfl
  · rename_i hg
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false,
      not_le] at hg
    cases hi : coinIx P ride k r j with
    | none => rfl
    | some i =>
      obtain ⟨x, hx, hm, hE, ho⟩ := coinIx_seat P ride k r j i hi hg.1.2 hg.2
      have := ce_put_read P ride c k x hx hm (hE.trans hg.1.1)
      rw [ho] at this
      exact this

theorem mainF_read (k : Fin P.sent.size) (r j : ℕ) :
    (rowsR P ride (fun _ _ _ => none) (put P ride (readC P ride c).1) k).mainF r j =
      (rowsR P ride (fun _ _ _ => none) c k).mainF r j := by
  rw [mainF_eq, mainF_eq]
  split
  · rfl
  · rename_i hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true, not_le] at hg
    cases hi : coinIx P ride k r j with
    | none => rfl
    | some i =>
      obtain ⟨x, hx, hm, hE, ho⟩ := coinIx_seat P ride k r j i hi hg.1.2 hg.2
      have := cf_put_read P ride c k x hx hm (hE.trans hg.1.1)
      rw [ho] at this
      exact this

/-- The number of mask coin i of oracle message k is maskStart P ride k + i. -/
theorem mask_no (k i : ℕ) :
    (startR P ride k).e + (Seat.mask i).off P.codes (shapeAt P k) (ride k) =
      maskStart P ride k + i := by
  show _ + (_ + i) = _ + _ + i
  rw [Nat.add_assoc]

theorem ce_mask_read (k : Fin P.sent.size) (i : ℕ) (hi : i < (stp P ride k).mask) :
    ce (put P ride (readC P ride c).1) (maskStart P ride k + i) =
      ce c (maskStart P ride k + i) := by
  have := ce_put_read P ride c k (.mask i) hi rfl rfl
  rwa [mask_no] at this

theorem mask_read (k : Fin P.sent.size) (r j : ℕ) :
    (rowsR P ride (fun _ _ _ => none) (put P ride (readC P ride c).1) k).mask r j =
      (rowsR P ride (fun _ _ _ => none) c k).mask r j := by
  rw [mask_eq, mask_eq]
  cases hr : ride k with
  | none =>
    simp only
    split
    · rename_i hg
      have hi : j * (shapeAt P k).maskRows + r < (stp P ride k).mask := by
        have e : (stp P ride k).mask =
            (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
          simp [stp, stepsOf, hr]
        rw [e, Nat.mul_comm (shapeAt P k).maskRows]
        exact lt_mul j r _ _ hg.2 hg.1
      have := ce_mask_read P ride c k _ hi
      rwa [← Nat.add_assoc] at this
    · rfl
  | some R =>
    simp only
    split
    · refine congrArg (fun F => R.lay F r j) (funext fun i => ?_)
      unfold rideC
      split
      · rename_i hi
        exact ce_mask_read P ride c k i (by simpa [stp, stepsOf, hr] using hi)
      · rfl
    · rfl

/-- At no data, each entry of each row's message is the same at the coins put (readC c).1 as at the
sender's coins c. -/
theorem entry_read (ρ : RowN P) (j : ℕ) :
    entry P (rowsR P ride (fun _ _ _ => none) (put P ride (readC P ride c).1)) ρ j =
      entry P (rowsR P ride (fun _ _ _ => none) c) ρ j := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · show (if (shapeAt P k).mainDeg == 3 then _ else _) = if (shapeAt P k).mainDeg == 3 then _ else _
    rw [mainE_read, mainF_read]
  · show crd t _ = crd t _
    rw [mask_read]

variable (data : Nat → Nat → Nat → Option (GF ⊕ GE))

/-- If the job fits its place (sendFits) and RidesZero holds, an entry of a row's message in rowsR
at the data and c is dataOf data plus the instance's lay at (readC c).1. -/
theorem entry_split (hf : sendFits P ride = true) (hR : RidesZero ride) (ρ : RowN P) (j : ℕ) :
    entry P (rowsR P ride data c) ρ j =
      dataOf P ride data ρ j + (sender P ride).lay (readC P ride c).1 ρ j := by
  show _ = entry P (rowsR P ride data (zc _)) ρ j +
    entry P (rowsR P ride (fun _ _ _ => none) (put P ride (readC P ride c).1)) ρ j
  rw [entry_read, ← entry_zadd P ride data c hf hR]

/-- An entry of a row's tail in rowsR at the data and c, below the tail's length, is that entry of
the tail in readC c. No premise. -/
theorem tail_split (ρ : RowN P) (q : Fin (codeAt P ρ).r) :
    tailEntry P (rowsR P ride data c) ρ q.val = (readC P ride c).2 ρ q := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · have hq : q.val < (P.codes.base.getD (shapeAt P k).code default).r := q.isLt
    show (if (shapeAt P k).mainDeg == 3 then _ else _) =
      coinAt P ride c k (Seat.tail r.val q.val, t.val)
    unfold coinAt
    show _ = if ((shapeAt P k).mainDeg == 3) = true then _ else _
    rw [mainTlE_eq, mainTlF_eq]
    by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · simp only [h3, r.isLt, hq, decide_true, Bool.and_self, if_true, Seat.no, Seat.inE, Seat.off,
        Nat.add_assoc]
    · simp only [h3, r.isLt, hq, decide_true, Bool.and_self, if_true, Seat.no, Seat.inE, Seat.off,
        Nat.add_assoc, Bool.not_false, Bool.false_eq_true, if_false, Bool.not_eq_true] at *
  · have hq : q.val < (P.codes.mask.getD (shapeAt P k).maskCode default).r := q.isLt
    show crd t _ = coinAt P ride c k (Seat.maskTail r.val q.val, t.val)
    unfold coinAt
    rw [maskTl_eq, if_pos ⟨r.isLt, hq⟩]
    show _ = if true = true then _ else _
    rw [if_pos rfl, co_fin]
    refine congrArg (fun n => crd t (ce c n)) ?_
    simp only [Seat.no, Seat.inE, Seat.off, maskStart, stp, if_true, Nat.add_assoc]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.entry_split
#print axioms OnBytes.SendSim.At.tail_split
