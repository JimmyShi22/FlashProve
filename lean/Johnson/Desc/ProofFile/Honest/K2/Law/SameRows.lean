-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SameRows.lean: TWO TEXTS LAY THE COINS OF AN ORACLE MESSAGE
INTO ITS ROWS: the code switch's (`messageRows` under `rowsAll`, Honest/K2/Sending.lean) and the
shared sending's (`K1.rowsR`, Honest/K1/Coins.lean). HERE THEY ARE SHOWN TO LAY THE SAME ROWS. The
definitions that the statements speak of, statements and proofs.

  `asShared`, `dataShared`   the switch's main rows as the shared sending takes them: by the rows'
                 field
  `coinAtShared`, `sharedRows`   the body of `K1.rowsR`, of a shape, a riding table, a start and
                 coins at any count
  `rowsR_shared`, `sharedRows_cast`   it IS that body; it does not see under which term the count is
                 written
  `rows_ext`, `zeroG_eq`   rows are equal where their six functions are; the zero with code is 0
  `laid_shared`  ONE MESSAGE: the rows laid of a cut at a are the shared rows at the start a
  `rowsAll_shared`   THE SENDING: where `rowsAll` returns V, at a sending without a masking word and
                 at the shared sending's own table for a fresh mask: V k = `K1.rowsR` ... k for
                 every message k of the sending, the coins being the same under the other count
  `rowsAll_shared_paid`   the same, with the two counts' equation paid by `sendingDue_shared`

Limits. The equation is on the rows, as functions at all rows and places. It is stated at messages
of the sending: beyond them `rowsAll` yields a message of zeros, and nothing is said. `NoWord` is a
premise. `dataShared` never yields "none": a law on `K1.rowsR` at every data covers it, not the
other way round. The fresh mask's table is a premise's letter: every table that is the shared
sending's `K1.Ride.lay` entry for entry. What is WRITTEN where: no sentence on what a coin is for.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (zeroG)
open Johnson.Prover.Send (Rows)
open Reads

/-! ## 1 What the statements speak of -/

/-- One message's main rows as the shared sending takes them: by the rows' field; of a row over the
base field the first coordinate. It never yields "none". -/
def asShared (s : OnBytes.OracleShape) (data : Nat → Nat → Cb.Gl.E) (r j : Nat) :
    Option (Cb.Gl.F ⊕ Cb.Gl.E) :=
  if s.mainDeg == 3 then some (.inr (data r j)) else some (.inl (data r j).c0)

/-- A sending's. -/
def dataShared (sent : Array OnBytes.OracleNotice) (data : Nat → Nat → Nat → Cb.Gl.E) (k : Nat) :
    Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E) :=
  asShared (sent.getD k default).shape (data k)

/-- The shared sending's number, among a message's main coins, of the entry at place j of main row
r; none: the caller's data. `K1.rowsR`'s own lines, under a name. -/
def coinAtShared (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (ρ : Option K1.Ride)
    (r j : Nat) : Option Nat :=
  let C := codes.base.getD s.code default
  let n := K1.stepsOf codes s ρ
  let padAt (r j : Nat) : Option Nat :=
    if n.pad != 0 && r + 1 == s.mainRows && decide (C.ell - n.pad ≤ j) && decide (j < C.ell) then
      some (j - (C.ell - n.pad)) else none
  if n.word != 0 then (if j < C.ell then some (n.tails + r * C.ell + j) else none)
  else (padAt r j).map (n.tails + ·)

/-- **The body of `K1.rowsR`**: of the codes, a shape, a riding table or none, the counts in front,
the caller's data for the message, and coins at any count. -/
def sharedRows {d : Due} (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (ρ : Option K1.Ride)
    (a : Due) (D : Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs d) : Rows :=
  let C := codes.base.getD s.code default
  let Z := codes.mask.getD s.maskCode default
  let n := K1.stepsOf codes s ρ
  let overE := s.mainDeg == 3
  let m0 := a.e + if overE then n.main else 0
  { mainE := fun r j => if !overE || decide (s.mainRows ≤ r) || decide (C.ell ≤ j) then 0 else
      match coinAtShared codes s ρ r j with
      | some i => K1.ce c (a.e + i)
      | none =>
        match D r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
        | none => 0
    mainF := fun r j => if overE || decide (s.mainRows ≤ r) || decide (C.ell ≤ j) then 0 else
      match coinAtShared codes s ρ r j with
      | some i => K1.cf c (a.f + i)
      | none =>
        match D r j with
        | some (.inl x) => x
        | _ => 0
    mainTlE := fun r q => if overE && decide (r < s.mainRows) && decide (q < C.r) then
      K1.ce c (a.e + r * C.r + q) else 0
    mainTlF := fun r q => if !overE && decide (r < s.mainRows) && decide (q < C.r) then
      K1.cf c (a.f + r * C.r + q) else 0
    mask := fun r j =>
      match ρ with
      | some R => if r < s.maskRows ∧ j < Z.ell then
          R.lay (fun i => if i < R.count then K1.ce c (m0 + i) else 0) r j else 0
      | none => if r < s.maskRows ∧ j < Z.ell then K1.ce c (m0 + j * s.maskRows + r) else 0
    maskTl := fun r q =>
      if r < s.maskRows ∧ q < Z.r then K1.ce c (m0 + n.mask + r * Z.r + q) else 0 }

/-- It is that body. -/
theorem rowsR_shared (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) (k : Nat) :
    K1.rowsR P ride data c k =
      sharedRows P.codes (Johnson.Prover.Send.shapeAt P k) (ride k) (K1.startR P ride k) (data k)
        c :=
  rfl

/-- It does not see under which term the count is written. -/
theorem sharedRows_cast {d d' : Due} (h : d = d') (codes : OnBytes.Codes)
    (s : OnBytes.OracleShape) (ρ : Option K1.Ride) (a : Due)
    (D : Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs d) :
    sharedRows codes s ρ a D (h ▸ c) = sharedRows codes s ρ a D c := by
  subst h
  rfl

/-- Rows are equal where their six functions are. -/
theorem rows_ext : ∀ (X Y : Rows), X.mainE = Y.mainE → X.mainF = Y.mainF →
    X.mainTlE = Y.mainTlE → X.mainTlF = Y.mainTlF → X.mask = Y.mask → X.maskTl = Y.maskTl → X = Y
  | ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl, rfl => rfl

/-- The zero that is written so that it has code is the field's 0. -/
theorem zeroG_eq : zeroG = 0 :=
  OnBytes.Slice.toE_zeroE

/-! ## 2 One message -/

/-- **The rows laid of a cut at a are the shared rows at the start a.** -/
theorem laid_shared {table : FreshTable} {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    {fold : Option Nat} {data : Nat → Nat → Cb.Gl.E} {d a N : Due} {c : Cs d} {c' : Cs N}
    {cF : Array Cb.Gl.F} {cE cM cT : Array Cb.Gl.E} (H : ShapeFits codes s fold)
    (hw : s.mainRows = 0 ∨ s.answers ≠ 0)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (hcut : c.cut a N = some c')
    (hF : (⟨N, c'⟩ : Stretch).fs 0 (countF codes s) = .ok cF)
    (hE : (⟨N, c'⟩ : Stretch).es 0 (fromE codes s) = .ok cE)
    (hM : (⟨N, c'⟩ : Stretch).es (fromE codes s) (inMaskOf codes s fold) = .ok cM)
    (hT : (⟨N, c'⟩ : Stretch).es (fromE codes s + inMaskOf codes s fold)
      (s.maskRows * (codes.mask.getD s.maskCode default).r) = .ok cT) :
    laidRows table codes s fold data cF cE cM cT =
      sharedRows codes s (rideAs s fold) a (asShared s data) c := by
  -- what each array holds, by the number of the sending's coin
  have vF : ∀ i, i < countF codes s → cF.getD i (OnBytes.Slice.toF 0) = K1.cf c (a.f + i) := by
    intro i hi
    have h := fAt_cf (cut_fAt hcut (fs_at hF hi (OnBytes.Slice.toF 0)))
    rw [Nat.zero_add] at h
    exact h.symm
  have vE : ∀ i, i < fromE codes s → cE.getD i zeroG = K1.ce c (a.e + i) := by
    intro i hi
    have h := eAt_ce (cut_eAt hcut (es_at hE hi zeroG))
    rw [Nat.zero_add] at h
    exact h.symm
  have vM : ∀ i, i < inMaskOf codes s fold →
      cM.getD i zeroG = K1.ce c (a.e + (fromE codes s + i)) := fun i hi =>
    (eAt_ce (cut_eAt hcut (es_at hM hi zeroG))).symm
  have vT : ∀ i, i < s.maskRows * (codes.mask.getD s.maskCode default).r →
      cT.getD i zeroG = K1.ce c (a.e + (fromE codes s + inMaskOf codes s fold + i)) := fun i hi =>
    (eAt_ce (cut_eAt hcut (es_at hT hi zeroG))).symm
  -- the shared sending's numbers, in the switch's
  have hw0 : ((K1.stepsOf codes s (rideAs s fold)).word != 0) = false := by
    rw [steps_word hw]
    rfl
  have hmain := steps_main H hw
  have hmask := steps_mask codes s fold
  have hlen := padOf_length H
  have htails : (K1.stepsOf codes s (rideAs s fold)).tails =
      s.mainRows * (codes.base.getD s.code default).r := rfl
  have tailLt : ∀ b q, b < s.mainRows → q < (codes.base.getD s.code default).r →
      b * (codes.base.getD s.code default).r + q <
        s.mainRows * (codes.base.getD s.code default).r := by
    intro b q hb hq
    calc b * (codes.base.getD s.code default).r + q
        < b * (codes.base.getD s.code default).r + (codes.base.getD s.code default).r :=
          Nat.add_lt_add_left hq _
      _ = (b + 1) * (codes.base.getD s.code default).r := (Nat.succ_mul _ _).symm
      _ ≤ s.mainRows * (codes.base.getD s.code default).r := Nat.mul_le_mul_right _ hb
  have maskTailLt : ∀ r q, r < s.maskRows → q < (codes.mask.getD s.maskCode default).r →
      r * (codes.mask.getD s.maskCode default).r + q <
        s.maskRows * (codes.mask.getD s.maskCode default).r := by
    intro r q hr hq
    calc r * (codes.mask.getD s.maskCode default).r + q
        < r * (codes.mask.getD s.maskCode default).r + (codes.mask.getD s.maskCode default).r :=
          Nat.add_lt_add_left hq _
      _ = (r + 1) * (codes.mask.getD s.maskCode default).r := (Nat.succ_mul _ _).symm
      _ ≤ s.maskRows * (codes.mask.getD s.maskCode default).r := Nat.mul_le_mul_right _ hr
  -- a pad's coin has a number below the pad's count
  have padLt : ∀ b j t, b < s.mainRows → j < (codes.base.getD s.code default).ell →
      padAtOf codes s b j = some t → t < (padOf codes s).length := by
    intro b j t hb hj ht
    rw [padAtOf_eq H hb hj] at ht
    rcases ite_eq ht with ⟨q, e⟩ | ⟨_, e⟩
    · simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at q
      have := Option.some.inj e
      have := H.pad
      omega
    · cases e
  -- the shared sending's number of the coin at a place of a main row
  have coinAt : ∀ b j, b < s.mainRows → j < (codes.base.getD s.code default).ell →
      coinAtShared codes s (rideAs s fold) b j =
        (padAtOf codes s b j).map (s.mainRows * (codes.base.getD s.code default).r + ·) := by
    intro b j hb hj
    rw [padAtOf_eq H hb hj]
    exact if_neg (by rw [hw0]; exact Bool.false_ne_true)
  apply rows_ext
  · -- the main rows over the extension field
    funext b j
    by_cases hin : (s.mainDeg == 3) = true ∧ b < s.mainRows ∧
        j < (codes.base.getD s.code default).ell
    · obtain ⟨h3, hb, hj⟩ := hin
      have l1 : (!(s.mainDeg == 3 && (decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell)))) = false := by
        rw [h3, decide_eq_true hb, decide_eq_true hj]
        rfl
      have r1 : (!(s.mainDeg == 3) || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = false := by
        rw [h3, decide_eq_false (Nat.not_le.2 hb), decide_eq_false (Nat.not_le.2 hj)]
        rfl
      show (if (!(s.mainDeg == 3 && (decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell)))) = true then zeroG else
        match padAtOf codes s b j with
        | some t => cE.getD (s.mainRows * (codes.base.getD s.code default).r + t) zeroG
        | none => data b j) =
        (if (!(s.mainDeg == 3) || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true then 0 else
        match coinAtShared codes s (rideAs s fold) b j with
        | some i => K1.ce c (a.e + i)
        | none =>
          match asShared s data b j with
          | some (.inr x) => x
          | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
          | none => 0)
      rw [if_neg (by rw [l1]; exact Bool.false_ne_true),
        if_neg (by rw [r1]; exact Bool.false_ne_true), coinAt b j hb hj]
      cases ht : padAtOf codes s b j with
      | some t =>
        have := padLt b j t hb hj ht
        exact vE _ (by unfold fromE inMainOf; rw [if_pos h3]; omega)
      | none =>
        show data b j = match asShared s data b j with
          | some (.inr x) => x
          | some (.inl x) => algebraMap Cb.Gl.F Cb.Gl.E x
          | none => 0
        unfold asShared
        rw [if_pos h3]
    · have l1 : (!(s.mainDeg == 3 && (decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell)))) = true := by
        cases h3 : (s.mainDeg == 3) with
        | false => rfl
        | true =>
          by_cases hb : b < s.mainRows
          · have hj : ¬ j < (codes.base.getD s.code default).ell := fun hj => hin ⟨h3, hb, hj⟩
            rw [decide_eq_true hb, decide_eq_false hj]
            rfl
          · rw [decide_eq_false hb]
            rfl
      have r1 : (!(s.mainDeg == 3) || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true := by
        cases h3 : (s.mainDeg == 3) with
        | false => rfl
        | true =>
          by_cases hb : b < s.mainRows
          · have hj : (codes.base.getD s.code default).ell ≤ j :=
              Nat.not_lt.1 fun hj => hin ⟨h3, hb, hj⟩
            rw [decide_eq_true hj, Bool.or_true]
          · rw [decide_eq_true (Nat.not_lt.1 hb), Bool.or_true, Bool.true_or]
      show (if (!(s.mainDeg == 3 && (decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell)))) = true then zeroG else _) =
        (if (!(s.mainDeg == 3) || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true then 0 else _)
      rw [if_pos l1, if_pos r1]
      exact zeroG_eq
  · -- the main rows over the base field
    funext b j
    by_cases hin : (s.mainDeg == 3) = false ∧ b < s.mainRows ∧
        j < (codes.base.getD s.code default).ell
    · obtain ⟨h3, hb, hj⟩ := hin
      have h3' : ¬ (s.mainDeg == 3) = true := by
        rw [h3]
        exact Bool.false_ne_true
      have l1 : (s.mainDeg == 3 || !(decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell))) = false := by
        rw [h3, decide_eq_true hb, decide_eq_true hj]
        rfl
      have r1 : (s.mainDeg == 3 || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = false := by
        rw [h3, decide_eq_false (Nat.not_le.2 hb), decide_eq_false (Nat.not_le.2 hj)]
        rfl
      show (if (s.mainDeg == 3 || !(decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell))) = true then OnBytes.Slice.toF 0 else
        match padAtOf codes s b j with
        | some t =>
          cF.getD (s.mainRows * (codes.base.getD s.code default).r + t) (OnBytes.Slice.toF 0)
        | none => (data b j).c0) =
        (if (s.mainDeg == 3 || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true then 0 else
        match coinAtShared codes s (rideAs s fold) b j with
        | some i => K1.cf c (a.f + i)
        | none =>
          match asShared s data b j with
          | some (.inl x) => x
          | _ => 0)
      rw [if_neg (by rw [l1]; exact Bool.false_ne_true),
        if_neg (by rw [r1]; exact Bool.false_ne_true), coinAt b j hb hj]
      cases ht : padAtOf codes s b j with
      | some t =>
        have := padLt b j t hb hj ht
        exact vF _ (by unfold countF inMainOf; rw [if_neg h3']; omega)
      | none =>
        show (data b j).c0 = match asShared s data b j with
          | some (.inl x) => x
          | _ => 0
        unfold asShared
        rw [if_neg h3']
    · have l1 : (s.mainDeg == 3 || !(decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell))) = true := by
        cases h3 : (s.mainDeg == 3) with
        | true => rfl
        | false =>
          by_cases hb : b < s.mainRows
          · have hj : ¬ j < (codes.base.getD s.code default).ell := fun hj => hin ⟨h3, hb, hj⟩
            rw [decide_eq_true hb, decide_eq_false hj]
            rfl
          · rw [decide_eq_false hb]
            rfl
      have r1 : (s.mainDeg == 3 || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true := by
        cases h3 : (s.mainDeg == 3) with
        | true => rfl
        | false =>
          by_cases hb : b < s.mainRows
          · have hj : (codes.base.getD s.code default).ell ≤ j :=
              Nat.not_lt.1 fun hj => hin ⟨h3, hb, hj⟩
            rw [decide_eq_true hj, Bool.or_true]
          · rw [decide_eq_true (Nat.not_lt.1 hb), Bool.or_true, Bool.true_or]
      show (if (s.mainDeg == 3 || !(decide (b < s.mainRows) &&
          decide (j < (codes.base.getD s.code default).ell))) = true then OnBytes.Slice.toF 0
          else _) =
        (if (s.mainDeg == 3 || decide (s.mainRows ≤ b) ||
          decide ((codes.base.getD s.code default).ell ≤ j)) = true then 0 else _)
      rw [if_pos l1, if_pos r1]
      exact OnBytes.Slice.toF_zero
  · -- the main rows' tails over the extension field
    funext b q
    show (if (s.mainDeg == 3 && (decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r))) = true then
        cE.getD (b * (codes.base.getD s.code default).r + q) zeroG else zeroG) =
      (if (s.mainDeg == 3 && decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r)) = true then
        K1.ce c (a.e + b * (codes.base.getD s.code default).r + q) else 0)
    rw [← Bool.and_assoc]
    by_cases hin : (s.mainDeg == 3 && decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r)) = true
    · rw [if_pos hin, if_pos hin, Nat.add_assoc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
      have := tailLt b q hin.1.2 hin.2
      exact vE _ (by unfold fromE inMainOf; rw [if_pos hin.1.1]; omega)
    · rw [if_neg hin, if_neg hin]
      exact zeroG_eq
  · -- the main rows' tails over the base field
    funext b q
    show (if (!(s.mainDeg == 3) && (decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r))) = true then
        cF.getD (b * (codes.base.getD s.code default).r + q) (OnBytes.Slice.toF 0)
        else OnBytes.Slice.toF 0) =
      (if (!(s.mainDeg == 3) && decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r)) = true then
        K1.cf c (a.f + b * (codes.base.getD s.code default).r + q) else 0)
    rw [← Bool.and_assoc]
    by_cases hin : (!(s.mainDeg == 3) && decide (b < s.mainRows) &&
        decide (q < (codes.base.getD s.code default).r)) = true
    · rw [if_pos hin, if_pos hin, Nat.add_assoc]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hin
      have := tailLt b q hin.1.2 hin.2
      have h3' : ¬ (s.mainDeg == 3) = true := by
        rw [hin.1.1]
        exact Bool.false_ne_true
      exact vF _ (by unfold countF inMainOf; rw [if_neg h3']; omega)
    · rw [if_neg hin, if_neg hin]
      exact OnBytes.Slice.toF_zero
  · -- the mask rows
    funext r i
    have hm0 : (a.e + if (s.mainDeg == 3) = true then
        (K1.stepsOf codes s (rideAs s fold)).main else 0) = a.e + fromE codes s := by
      rw [hmain]
      rfl
    by_cases hin : r < s.maskRows ∧ i < (codes.mask.getD s.maskCode default).ell
    · have l1 : (!(decide (r < s.maskRows) &&
          decide (i < (codes.mask.getD s.maskCode default).ell))) = false := by
        rw [decide_eq_true hin.1, decide_eq_true hin.2]
        rfl
      cases fold with
      | none =>
        show (if (!(decide (r < s.maskRows) &&
            decide (i < (codes.mask.getD s.maskCode default).ell))) = true then zeroG else
            cM.getD (i * s.maskRows + r) zeroG) =
          (if r < s.maskRows ∧ i < (codes.mask.getD s.maskCode default).ell then
            K1.ce c ((a.e + if (s.mainDeg == 3) = true then
              (K1.stepsOf codes s (rideAs s none)).main else 0) + i * s.maskRows + r) else 0)
        rw [if_neg (by rw [l1]; exact Bool.false_ne_true), if_pos hin, hm0, Nat.add_assoc,
          Nat.add_assoc]
        refine vM _ ?_
        show i * s.maskRows + r < s.maskRows * (codes.mask.getD s.maskCode default).ell
        calc i * s.maskRows + r < i * s.maskRows + s.maskRows := Nat.add_lt_add_left hin.1 _
          _ = (i + 1) * s.maskRows := (Nat.succ_mul _ _).symm
          _ ≤ (codes.mask.getD s.maskCode default).ell * s.maskRows :=
            Nat.mul_le_mul_right _ hin.2
          _ = s.maskRows * (codes.mask.getD s.maskCode default).ell := Nat.mul_comm _ _
      | some n =>
        show (if (!(decide (r < s.maskRows) &&
            decide (i < (codes.mask.getD s.maskCode default).ell))) = true then zeroG else
            table n (OnBytes.ceilLog2 s.maskRows) (cM.getD · zeroG) r i) =
          (if r < s.maskRows ∧ i < (codes.mask.getD s.maskCode default).ell then
            (⟨n, OnBytes.ceilLog2 s.maskRows⟩ : K1.Ride).lay
              (fun t => if t < 2 * n + 1 then K1.ce c ((a.e + if (s.mainDeg == 3) = true then
                (K1.stepsOf codes s (rideAs s (some n))).main else 0) + t) else 0) r i else 0)
        rw [if_neg (by rw [l1]; exact Bool.false_ne_true), if_pos hin, hm0, htab]
        congr 1
        funext t
        by_cases ht : t < 2 * n + 1
        · rw [if_pos ht, Nat.add_assoc]
          exact vM t ht
        · rw [if_neg ht, es_beyond hM (Nat.not_lt.1 ht) zeroG]
          exact zeroG_eq
    · have l1 : (!(decide (r < s.maskRows) &&
          decide (i < (codes.mask.getD s.maskCode default).ell))) = true := by
        by_cases hr : r < s.maskRows
        · have hi : ¬ i < (codes.mask.getD s.maskCode default).ell := fun hi => hin ⟨hr, hi⟩
          rw [decide_eq_true hr, decide_eq_false hi]
          rfl
        · rw [decide_eq_false hr]
          rfl
      cases fold with
      | none =>
        show (if (!(decide (r < s.maskRows) &&
            decide (i < (codes.mask.getD s.maskCode default).ell))) = true then zeroG else _) =
          (if r < s.maskRows ∧ i < (codes.mask.getD s.maskCode default).ell then _ else 0)
        rw [if_pos l1, if_neg hin]
        exact zeroG_eq
      | some n =>
        show (if (!(decide (r < s.maskRows) &&
            decide (i < (codes.mask.getD s.maskCode default).ell))) = true then zeroG else _) =
          (if r < s.maskRows ∧ i < (codes.mask.getD s.maskCode default).ell then _ else 0)
        rw [if_pos l1, if_neg hin]
        exact zeroG_eq
  · -- the mask rows' tails
    funext r q
    show (if (decide (r < s.maskRows) &&
        decide (q < (codes.mask.getD s.maskCode default).r)) = true then
        cT.getD (r * (codes.mask.getD s.maskCode default).r + q) zeroG else zeroG) =
      (if r < s.maskRows ∧ q < (codes.mask.getD s.maskCode default).r then
        K1.ce c ((a.e + if (s.mainDeg == 3) = true then
          (K1.stepsOf codes s (rideAs s fold)).main else 0) +
          (K1.stepsOf codes s (rideAs s fold)).mask +
          r * (codes.mask.getD s.maskCode default).r + q) else 0)
    by_cases hin : r < s.maskRows ∧ q < (codes.mask.getD s.maskCode default).r
    · have l1 : (decide (r < s.maskRows) &&
          decide (q < (codes.mask.getD s.maskCode default).r)) = true := by
        rw [decide_eq_true hin.1, decide_eq_true hin.2]
        rfl
      rw [if_pos l1, if_pos hin, hmain, hmask, vT _ (maskTailLt r q hin.1 hin.2)]
      congr 1
      show _ = a.e + fromE codes s + _ + _ + _
      omega
    · have l1 : ¬ (decide (r < s.maskRows) &&
          decide (q < (codes.mask.getD s.maskCode default).r)) = true := by
        intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact hin h
      rw [if_neg l1, if_neg hin]
      exact zeroG_eq

/-! ## 3 The sending -/

/-- **The two texts lay the same rows.** hd: the two counts are one: `sendingDue_shared` pays it. -/
theorem rowsAll_shared {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (hw : NoWord sent) (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (h : rowsAll table codes sent fresh data c = .ok V)
    (hd : sendingDue codes sent fresh = K1.dueR (sendingPar codes sent) (rideOf sent fresh))
    {k : Nat} (hk : k < sent.size) :
    V k = K1.rowsR (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data) (hd ▸ c)
      k := by
  have hf := rowsAll_fits h
  obtain ⟨c', hc', hm⟩ := rowsAll_at h hk
  obtain ⟨_, _, _, cF, cE, cM, cT, hF, hE, hM, hT, hR⟩ := messageRows_laid hm
  rw [rowsR_shared, sharedRows_cast, sendingPar_shape, rideOf_as,
    ← dueBefore_shared hf hw k (Nat.le_of_lt hk), hR]
  exact laid_shared (shapeFits_of hf hk) (hw k hk) htab hc' hF hE hM hT

/-- **The same, with the counts' equation paid.** -/
theorem rowsAll_shared_paid {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)}
    {data : Nat → Nat → Nat → Cb.Gl.E} {c : Cs (sendingDue codes sent fresh)} {V : Nat → Rows}
    (hw : NoWord sent) (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j)
    (h : rowsAll table codes sent fresh data c = .ok V) {k : Nat} (hk : k < sent.size) :
    V k = K1.rowsR (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data)
      (sendingDue_shared (rowsAll_fits h) hw ▸ c) k :=
  rowsAll_shared hw htab h _ hk

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.rowsR_shared
#print axioms ProofFile.Honest.K2.sharedRows_cast
#print axioms ProofFile.Honest.K2.rows_ext
#print axioms ProofFile.Honest.K2.zeroG_eq
#print axioms ProofFile.Honest.K2.laid_shared
#print axioms ProofFile.Honest.K2.rowsAll_shared
#print axioms ProofFile.Honest.K2.rowsAll_shared_paid
#print axioms ProofFile.Honest.K2.asShared
#print axioms ProofFile.Honest.K2.dataShared
#print axioms ProofFile.Honest.K2.coinAtShared
#print axioms ProofFile.Honest.K2.sharedRows
