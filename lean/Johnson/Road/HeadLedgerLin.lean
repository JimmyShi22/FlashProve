-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLedgerLin.lean: the values of the lines of a normalisation's ledger: the part that
does not depend on a sub-proof.

Two texts describe the 17 identities of a normalisation's ledger with five limbs. The verifier in
OnBytes/ builds them as affine forms, from the forms of a row's 99 cells, of nine sums and of seven
products (row5, ledCarry5, ledLines5 in OnBytes/Model/Ledger.lean). The library defines them on the
values of the 99 bytes (Ledger.idn in Inst/Model/Common/Ledger.lean), and again with letters in the
place of the seven products (Ledger.idnP in Inst/Model/Common/LedgerForms.lean). This file shows
that the value of each of the verifier's forms is the library's idnP of the values.

How to read the statements. A form has a value in a world (Aff.value in
OnBytes/Model/HideLaws.lean). D n stands for the value of byte n. The one hypothesis on D is that,
for n below 99, D n is the value of the form of cell n, plus 128. No other byte is read.

Main definitions: dgs, dg (the digits of a row as forms); ledRoots (the eight lines after the
carries, written out); slack (how idnP changes with the sums and the products).
Main theorems: getD_cells, dg_value, dig_value (digits); row5_Dg, row5_Vlo to row5_rq, row5_s0,
row5_a, row5_b, row5_sig, row5_R, row5_kap, row5_c (each number of a row is the library's);
ledCarry5_value, ledLines5_list, ledRoots_length, ledRoots_value (each line is the library's idnP);
ledProducts5_value, ledProducts5_zero (the order of the seven products); idnP_slack, slack_zero.

What is not claimed. Nothing is said about where the forms of the cells come from, about what the
sums and the products hold, or about what a verifier's acceptance shows. An identity in a field says
nothing about whole numbers by itself. The program does not import this file.
-/
import OnBytes.Model.Ledger
import OnBytes.Model.HideLaws
import Johnson.Road.FormsKeysKit
import Inst.Model.Common.LedgerForms

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff LedK Row5 row5 ledDig ledCarry5 ledLines5)
open Inst.Model (NormPar)

/-! ## Arrays -/

/-- A member of an array that is made from a function. -/
theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (h : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD, h]

section Values

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-! ## The four operations on forms -/

/-- The value of a constant. -/
theorem led_c (v : E) : (LedK.c v : Aff).value ρ W = ρ.val v := Aff.value_ofConst ρ W v
/-- The value of a sum. -/
theorem led_add (a b : Aff) : (LedK.add a b).value ρ W = a.value ρ W + b.value ρ W :=
  Aff.value_add ρ W a b
/-- The value of a difference. -/
theorem led_sub (a b : Aff) : (LedK.sub a b).value ρ W = a.value ρ W - b.value ρ W :=
  Aff.value_sub ρ W a b
/-- The value of a multiple. -/
theorem led_mul (a : Aff) (k : E) : (LedK.mul a k).value ρ W = ρ.val k * a.value ρ W :=
  Aff.value_scale ρ W a k

/-- The value of the number that n digits spell. -/
theorem ledDig_value (hρ : Numerals ρ) (Dg : Array Aff) (first n : ℕ) :
    (ledDig Dg first n).value ρ W =
      ∑ j ∈ range n, (256 : K) ^ j * (Dg.getD (first + j) (LedK.c zeroE)).value ρ W := by
  induction n with
  | zero =>
    have e : ledDig Dg first 0 = (LedK.c zeroE : Aff) := rfl
    rw [e, led_c, ρ.zero, Finset.sum_range_zero]
  | succ n ih =>
    have e : ledDig Dg first (n + 1) = LedK.add (ledDig Dg first n)
        (LedK.mul (Dg.getD (first + n) (LedK.c zeroE)) (Model.ofNat (256 ^ n))) := by
      unfold Model.ledDig
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, led_add, led_mul, ih, Finset.sum_range_succ, hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat]

/-! ## The digits of a row -/

/-- The 99 digits of a row as forms: each is its cell plus 128. -/
def dgs (cell : ℕ → Aff) : Array Aff :=
  Array.ofFn (n := 99) fun j => LedK.add (cell j.val) (LedK.c (Model.ofNat 128))

/-- Digit n of a row as a form. -/
def dg (cell : ℕ → Aff) (n : ℕ) : Aff := (dgs cell).getD n (LedK.c zeroE)

/-- A digit of a row of any length is its cell plus 128. -/
theorem getD_cells {N : ℕ} (cell : ℕ → Aff) (d : Aff) {n : ℕ} (hn : n < N) :
    (Array.ofFn (n := N) fun j => LedK.add (cell j.val) (LedK.c (Model.ofNat 128))).getD n d =
      LedK.add (cell n) (LedK.c (Model.ofNat 128)) :=
  getD_ofFn _ _ hn

variable {cell : ℕ → Aff} {D : ℕ → K}

/-- A digit's value. -/
theorem dg_value (hρ : Numerals ρ) (hD : ∀ n, n < 99 → (cell n).value ρ W + 128 = D n) {n : ℕ}
    (hn : n < 99) : (dg cell n).value ρ W = D n := by
  have e : dg cell n = LedK.add (cell n) (LedK.c (Model.ofNat 128)) := by
    unfold dg dgs
    exact getD_cells cell _ hn
  rw [e, led_add, led_c, hρ.ofNat, Nat.cast_ofNat, hD n hn]

/-- The number that n digits of a row spell is the library's. -/
theorem dig_value (hρ : Numerals ρ) (hD : ∀ n, n < 99 → (cell n).value ρ W + 128 = D n)
    {first n : ℕ} (h : first + n ≤ 99) :
    (ledDig (dgs cell) first n).value ρ W = Inst.Model.Ledger.b256 D first n := by
  rw [ledDig_value hρ]
  unfold Inst.Model.Ledger.b256
  refine sum_congr rfl fun j hj => ?_
  have hj' : first + j < 99 := by
    have := mem_range.mp hj
    omega
  have e : dg cell (first + j) = (dgs cell).getD (first + j) (LedK.c zeroE) := by
    unfold dg
    rfl
  rw [← e, dg_value hρ hD hj']

/-! ## The numbers of a row -/

section Row

variable (hρ : Numerals ρ) (hD : ∀ n, n < 99 → (cell n).value ρ W + 128 = D n)
include hρ hD

/-- The value of a digit of a row. -/
theorem row5_Dg {n : ℕ} (hn : n < 99) :
    ((row5 cell).Dg.getD n (LedK.c zeroE)).value ρ W = D n := by
  have e1 : (row5 cell).Dg = dgs cell := rfl
  have e2 : dg cell n = (dgs cell).getD n (LedK.c zeroE) := by
    unfold dg
    rfl
  rw [e1, ← e2, dg_value hρ hD hn]
/-! Each number that a row composes from its digits has the value of the library's number of the
same name; a is the library's sa, b its sb, kap its kc. -/

theorem row5_Vlo : (row5 cell).Vlo.value ρ W = Inst.Model.Ledger.Vlo D :=
  dig_value hρ hD (first := 0) (n := 6) (by omega)
theorem row5_Vhi : (row5 cell).Vhi.value ρ W = Inst.Model.Ledger.Vhi D :=
  dig_value hρ hD (first := 6) (n := 4) (by omega)
theorem row5_l1 : (row5 cell).l1.value ρ W = Inst.Model.Ledger.l1 D :=
  dig_value hρ hD (first := 64) (n := 5) (by omega)
theorem row5_h1 : (row5 cell).h1.value ρ W = Inst.Model.Ledger.h1 D :=
  dig_value hρ hD (first := 69) (n := 5) (by omega)
theorem row5_Blo : (row5 cell).Blo.value ρ W = Inst.Model.Ledger.Blo D :=
  dig_value hρ hD (first := 74) (n := 3) (by omega)
theorem row5_Bhi : (row5 cell).Bhi.value ρ W = Inst.Model.Ledger.Bhi D :=
  dig_value hρ hD (first := 77) (n := 2) (by omega)
theorem row5_Rlo : (row5 cell).Rlo.value ρ W = Inst.Model.Ledger.Rlo D :=
  dig_value hρ hD (first := 80) (n := 3) (by omega)
theorem row5_Rhi : (row5 cell).Rhi.value ρ W = Inst.Model.Ledger.Rhi D :=
  dig_value hρ hD (first := 83) (n := 3) (by omega)
theorem row5_q1 : (row5 cell).q1.value ρ W = Inst.Model.Ledger.q1 D :=
  dig_value hρ hD (first := 86) (n := 3) (by omega)
theorem row5_rr : (row5 cell).rr.value ρ W = Inst.Model.Ledger.rr D :=
  dig_value hρ hD (first := 89) (n := 5) (by omega)
theorem row5_rq : (row5 cell).rq.value ρ W = Inst.Model.Ledger.rq D :=
  dig_value hρ hD (first := 94) (n := 5) (by omega)
theorem row5_s0 : (row5 cell).s0.value ρ W = Inst.Model.Ledger.s0 D := by
  have e : (row5 cell).s0 = dg cell 59 := by
    unfold Model.row5 dg dgs
    dsimp only
  rw [e, dg_value hρ hD (n := 59) (by omega)]
  rfl

theorem row5_a : (row5 cell).a.value ρ W = Inst.Model.Ledger.sa D := by
  have e : (row5 cell).a = LedK.add (LedK.add (LedK.add (LedK.mul (dg cell 58) (Model.ofNat 2))
      (dg cell 59)) (LedK.mul (dg cell 60) (Model.ofNat 256)))
      (LedK.mul (dg cell 61) (Model.ofNat 65536)) := rfl
  have d58 := dg_value hρ hD (n := 58) (by omega)
  have d59 := dg_value hρ hD (n := 59) (by omega)
  have d60 := dg_value hρ hD (n := 60) (by omega)
  have d61 := dg_value hρ hD (n := 61) (by omega)
  rw [e, led_add, led_add, led_add, led_mul, led_mul, led_mul, d58, d59, d60, d61, hρ.ofNat,
    hρ.ofNat, hρ.ofNat]
  unfold Inst.Model.Ledger.sa
  norm_num

theorem row5_b : (row5 cell).b.value ρ W = Inst.Model.Ledger.sb D := by
  have e : (row5 cell).b = LedK.add (dg cell 62) (LedK.mul (dg cell 63) (Model.ofNat 256)) := rfl
  have d62 := dg_value hρ hD (n := 62) (by omega)
  have d63 := dg_value hρ hD (n := 63) (by omega)
  rw [e, led_add, led_mul, d62, d63, hρ.ofNat]
  unfold Inst.Model.Ledger.sb
  norm_num

theorem row5_sig : (row5 cell).sig.value ρ W = Inst.Model.Ledger.sig D := by
  have e : (row5 cell).sig =
      LedK.add (row5 cell).a (LedK.mul (row5 cell).b (Model.ofNat (2 ^ 24))) := rfl
  rw [e, led_add, led_mul, row5_a hρ hD, row5_b hρ hD, hρ.ofNat]
  unfold Inst.Model.Ledger.sig
  norm_num

theorem row5_R : (row5 cell).R.value ρ W = Inst.Model.Ledger.R D := by
  have e : (row5 cell).R =
      LedK.add (row5 cell).Rlo (LedK.mul (row5 cell).Rhi (Model.ofNat (2 ^ 24))) := rfl
  rw [e, led_add, led_mul, row5_Rlo hρ hD, row5_Rhi hρ hD, hρ.ofNat]
  unfold Inst.Model.Ledger.R
  norm_num

theorem row5_kap : (row5 cell).kap.value ρ W = Inst.Model.Ledger.kc D := by
  have e : (row5 cell).kap = LedK.sub (dg cell 79) (LedK.c (Model.ofNat 4)) := rfl
  have d79 := dg_value hρ hD (n := 79) (by omega)
  rw [e, led_sub, led_c, d79, hρ.ofNat]
  unfold Inst.Model.Ledger.kc
  norm_num

/-- The ten carries. -/
theorem row5_c {s : ℕ} (hs : s < 10) :
    ((row5 cell).c.getD s (LedK.c zeroE)).value ρ W = Inst.Model.Ledger.cs D s := by
  have e : (row5 cell).c.getD s (LedK.c zeroE) =
      if s == 0 then (LedK.c zeroE : Aff) else if s == 9 then dg cell 9
      else LedK.sub (ledDig (dgs cell) (10 + 6 * (s - 1)) 6) (LedK.c (Model.ofNat (2 ^ 47))) :=
    getD_ofFn (n := 10) (fun s : Fin 10 =>
      if s.val == 0 then (LedK.c zeroE : Aff) else if s.val == 9 then dg cell 9
      else LedK.sub (ledDig (dgs cell) (10 + 6 * (s.val - 1)) 6)
        (LedK.c (Model.ofNat (2 ^ 47)))) _ hs
  rw [e]
  unfold Inst.Model.Ledger.cs
  by_cases h0 : s = 0
  · have b0 : (s == 0) = true := by simp [h0]
    rw [if_pos b0, if_pos h0, led_c, ρ.zero]
  · have b0 : ¬ (s == 0) = true := by simp [h0]
    by_cases h9 : s = 9
    · have b9 : (s == 9) = true := by simp [h9]
      rw [if_neg b0, if_pos b9, if_neg h0, if_pos h9]
      exact dg_value hρ hD (by omega)
    · have b9 : ¬ (s == 9) = true := by simp [h9]
      rw [if_neg b0, if_neg b9, if_neg h0, if_neg h9, led_sub, led_c,
        dig_value hρ hD (by omega), hρ.ofNat]
      norm_num

end Row

/-! ## The lines -/

/-- The value of the carries' line s is the library's identity number s, for s from 0 to 8 (these
nine hold no product, so idnP is the identity itself). The form Ws stands for the sum W_s. -/
theorem ledCarry5_value (hρ : Numerals ρ) (hD : ∀ n, n < 99 → (cell n).value ρ W + 128 = D n)
    {s : ℕ} (hs : s < 9) (Ws : Aff) (np : NormPar) (w pv : ℕ → K) (hw : Ws.value ρ W = w s) :
    (ledCarry5 (row5 cell) s Ws).value ρ W = Inst.Model.Ledger.idnP np w D pv s := by
  have e : ledCarry5 (row5 cell) s Ws =
      LedK.sub (LedK.sub (LedK.add Ws ((row5 cell).c.getD s (LedK.c zeroE))) (dg cell s))
        (LedK.mul ((row5 cell).c.getD (s + 1) (LedK.c zeroE)) (Model.ofNat 256)) :=
    if_neg (by omega)
  rw [e, led_sub, led_sub, led_add, led_mul, row5_c hρ hD (s := s) (by omega),
    row5_c hρ hD (s := s + 1) (by omega), dg_value hρ hD (n := s) (by omega), hw, hρ.ofNat,
    Inst.Model.Ledger.idnP_j1 np w D pv hs]
  norm_num

/-- The eight lines after the carries, written out. P holds the forms of the seven products. -/
def ledRoots (r : Row5 Aff) (P : Array Aff) (eps : E) (two : Aff) : List Aff :=
  [LedK.sub (LedK.sub (P.getD 1 (LedK.c zeroE)) r.Blo) (LedK.mul r.Bhi (Model.ofNat (2 ^ 23))),
    LedK.add (LedK.sub (LedK.sub (LedK.sub (LedK.add r.Vlo (LedK.c eps))
      (P.getD 0 (LedK.c zeroE))) (LedK.mul r.Blo (Model.ofNat (2 ^ 25)))) r.l1)
      (LedK.mul r.kap (Model.ofNat (2 ^ 48))),
    LedK.sub (LedK.sub (LedK.sub r.Vhi r.Bhi) (P.getD 2 (LedK.c zeroE))) r.kap,
    LedK.sub (LedK.add r.l1 r.h1) (LedK.mul r.sig (Model.ofNat 2)),
    LedK.sub (LedK.add (P.getD 4 (LedK.c zeroE)) (P.getD 5 (LedK.c zeroE))) r.q1,
    P.getD 6 (LedK.c zeroE),
    LedK.sub (LedK.sub (LedK.sub (LedK.sub (LedK.add two r.sig) r.s0)
      (LedK.mul (P.getD 3 (LedK.c zeroE)) (Model.ofNat 2))) (LedK.mul r.q1 (Model.ofNat (2 ^ 25))))
      (LedK.mul r.rr (Model.ofNat 2)),
    LedK.add (LedK.sub (LedK.add r.rr r.rq) r.sig) (LedK.c oneE)]

/-- With seven products the verifier's eight lines are these. -/
theorem ledLines5_list (r : Row5 Aff) (P : Array Aff) (hP : P.size = 7) (eps : E) (two : Aff) :
    (ledLines5 r P eps two).toList = ledRoots r P eps two := by
  have hb : ¬ (P.size != 7) = true := by simp [hP]
  have e : ledLines5 r P eps two = (ledRoots r P eps two).toArray := if_neg hb
  exact congrArg Array.toList e

/-- The list has eight members. -/
theorem ledRoots_length (r : Row5 Aff) (P : Array Aff) (eps : E) (two : Aff) :
    (ledRoots r P eps two).length = 8 := rfl

/-- The value of member number k of the list ledRoots is the library's identity number 9 + k with
letters for the products (idnP), for k from 0 to 7. By ledLines5_list the list holds the verifier's
lines if P has seven members; that is not asked here. -/
theorem ledRoots_value (hρ : Numerals ρ) (hD : ∀ n, n < 99 → (cell n).value ρ W + 128 = D n)
    (P : Array Aff) (eps : E) (two : Aff) (np : NormPar) (w pv : ℕ → K)
    (heps : ρ.val eps = (np.eps : K)) (htwo : two.value ρ W = 2 ^ (np.M + 1))
    (hpv : ∀ j, j < 7 → (P.getD j (LedK.c zeroE)).value ρ W = pv j) {k : ℕ} (hk : k < 8) :
    ((ledRoots (row5 cell) P eps two).getD k {}).value ρ W =
      Inst.Model.Ledger.idnP np w D pv (9 + k) := by
  have p0 := hpv 0 (by omega)
  have p1 := hpv 1 (by omega)
  have p2 := hpv 2 (by omega)
  have p3 := hpv 3 (by omega)
  have p4 := hpv 4 (by omega)
  have p5 := hpv 5 (by omega)
  have p6 := hpv 6 (by omega)
  have c23 : ρ.val (Model.ofNat (2 ^ 23)) = (2 : K) ^ 23 := by rw [hρ.ofNat]; norm_num
  have c25 : ρ.val (Model.ofNat (2 ^ 25)) = (2 : K) ^ 25 := by rw [hρ.ofNat]; norm_num
  have c48 : ρ.val (Model.ofNat (2 ^ 48)) = (2 : K) ^ 48 := by rw [hρ.ofNat]; norm_num
  have c2 : ρ.val (Model.ofNat 2) = (2 : K) := by rw [hρ.ofNat]; norm_num
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show (LedK.sub (LedK.sub (P.getD 1 (LedK.c zeroE)) (row5 cell).Blo)
      (LedK.mul (row5 cell).Bhi (Model.ofNat (2 ^ 23)))).value ρ W =
      pv 1 - Inst.Model.Ledger.Blo D - 2 ^ 23 * Inst.Model.Ledger.Bhi D
    rw [led_sub, led_sub, led_mul, p1, row5_Blo hρ hD, row5_Bhi hρ hD, c23]
  · show (LedK.add (LedK.sub (LedK.sub (LedK.sub (LedK.add (row5 cell).Vlo (LedK.c eps))
      (P.getD 0 (LedK.c zeroE))) (LedK.mul (row5 cell).Blo (Model.ofNat (2 ^ 25))))
      (row5 cell).l1) (LedK.mul (row5 cell).kap (Model.ofNat (2 ^ 48)))).value ρ W =
      Inst.Model.Ledger.Vlo D + (np.eps : K) - pv 0 - 2 ^ 25 * Inst.Model.Ledger.Blo D -
        Inst.Model.Ledger.l1 D + 2 ^ 48 * Inst.Model.Ledger.kc D
    rw [led_add, led_sub, led_sub, led_sub, led_add, led_c, led_mul, led_mul, p0, heps,
      row5_Vlo hρ hD, row5_Blo hρ hD, row5_l1 hρ hD, row5_kap hρ hD, c25, c48]
  · show (LedK.sub (LedK.sub (LedK.sub (row5 cell).Vhi (row5 cell).Bhi)
      (P.getD 2 (LedK.c zeroE))) (row5 cell).kap).value ρ W =
      Inst.Model.Ledger.Vhi D - Inst.Model.Ledger.Bhi D - pv 2 - Inst.Model.Ledger.kc D
    rw [led_sub, led_sub, led_sub, p2, row5_Vhi hρ hD, row5_Bhi hρ hD, row5_kap hρ hD]
  · show (LedK.sub (LedK.add (row5 cell).l1 (row5 cell).h1)
      (LedK.mul (row5 cell).sig (Model.ofNat 2))).value ρ W =
      Inst.Model.Ledger.l1 D + Inst.Model.Ledger.h1 D - 2 * Inst.Model.Ledger.sig D
    rw [led_sub, led_add, led_mul, row5_l1 hρ hD, row5_h1 hρ hD, row5_sig hρ hD, c2]
  · show (LedK.sub (LedK.add (P.getD 4 (LedK.c zeroE)) (P.getD 5 (LedK.c zeroE)))
      (row5 cell).q1).value ρ W = pv 4 + pv 5 - Inst.Model.Ledger.q1 D
    rw [led_sub, led_add, p4, p5, row5_q1 hρ hD]
  · exact p6
  · show (LedK.sub (LedK.sub (LedK.sub (LedK.sub (LedK.add two (row5 cell).sig) (row5 cell).s0)
      (LedK.mul (P.getD 3 (LedK.c zeroE)) (Model.ofNat 2)))
      (LedK.mul (row5 cell).q1 (Model.ofNat (2 ^ 25))))
      (LedK.mul (row5 cell).rr (Model.ofNat 2))).value ρ W =
      2 ^ (np.M + 1) + Inst.Model.Ledger.sig D - Inst.Model.Ledger.s0 D - 2 * pv 3 -
        2 ^ 25 * Inst.Model.Ledger.q1 D - 2 * Inst.Model.Ledger.rr D
    rw [led_sub, led_sub, led_sub, led_sub, led_add, led_mul, led_mul, led_mul, p3, htwo,
      row5_sig hρ hD, row5_s0 hρ hD, row5_q1 hρ hD, row5_rr hρ hD, c2, c25]
  · show (LedK.add (LedK.sub (LedK.add (row5 cell).rr (row5 cell).rq) (row5 cell).sig)
      (LedK.c oneE)).value ρ W =
      Inst.Model.Ledger.rr D + Inst.Model.Ledger.rq D - Inst.Model.Ledger.sig D + 1
    rw [led_add, led_sub, led_add, led_c, row5_rr hρ hD, row5_rq hρ hD, row5_sig hρ hD, ρ.one]

/-! ## The batched products -/

/-- The verifier's sum of the seven products under weights, from the four factors a, b, Rlo, Rhi,
reads as the sum of weight times the library's product number j. So the verifier's order of the
seven products is the library's. -/
theorem ledProducts5_value (ρ : Reading K) (om : Array E) (first : ℕ) (a b l h : E) :
    ρ.val (Model.ledProducts5 om first a b l h) = ∑ j ∈ range 7,
      ρ.val (om.getD (first + j) zeroE) *
        Inst.Model.Ledger.prodsOf (ρ.val a) (ρ.val b) (ρ.val l) (ρ.val h) j := by
  have e : Model.ledProducts5 om first a b l h =
      addE (addE (addE (addE (addE (addE (mulE (mulE (om.getD (first + 0) zeroE) a) a)
        (mulE (mulE (om.getD (first + 1) zeroE) a) b))
        (mulE (mulE (om.getD (first + 2) zeroE) b) b))
        (mulE (mulE (om.getD (first + 3) zeroE) l) a))
        (mulE (mulE (om.getD (first + 4) zeroE) l) b))
        (mulE (mulE (om.getD (first + 5) zeroE) h) a))
        (mulE (mulE (om.getD (first + 6) zeroE) h) b) := rfl
  have p0 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 0 = x ^ 2 := fun _ _ _ _ => rfl
  have p1 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 1 = x * y := fun _ _ _ _ => rfl
  have p2 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 2 = y ^ 2 := fun _ _ _ _ => rfl
  have p3 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 3 = z * x := fun _ _ _ _ => rfl
  have p4 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 4 = z * y := fun _ _ _ _ => rfl
  have p5 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 5 = t * x := fun _ _ _ _ => rfl
  have p6 : ∀ x y z t : K, Inst.Model.Ledger.prodsOf x y z t 6 = t * y := fun _ _ _ _ => rfl
  rw [e]
  simp only [ρ.add, ρ.mul, Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6]
  ring

/-- The same for weights that are read from the array's beginning. -/
theorem ledProducts5_zero (ρ : Reading K) (om : Array E) (a b l h : E) :
    ρ.val (Model.ledProducts5 om 0 a b l h) = ∑ j ∈ range 7,
      ρ.val (om.getD j zeroE) *
        Inst.Model.Ledger.prodsOf (ρ.val a) (ρ.val b) (ρ.val l) (ρ.val h) j := by
  have e := ledProducts5_value ρ om 0 a b l h
  simp only [Nat.zero_add] at e
  exact e

end Values

/-! ## How an identity changes with the sums and the products -/

section Slack

variable {K : Type} [CommRing K]

/-- What identity number k gains if the nine sums grow by dw and the seven products by dp. -/
def slack (dw dp : ℕ → K) (k : ℕ) : K :=
  if k < 9 then dw k
  else match k with
    | 9 => dp 1
    | 10 => -dp 0
    | 11 => -dp 2
    | 13 => dp 4 + dp 5
    | 14 => dp 6
    | 15 => -(2 * dp 3)
    | _ => 0

/-- Past the last identity nothing is gained. -/
theorem slack_of_le (dw dp : ℕ → K) {k : ℕ} (hk : 17 ≤ k) : slack dw dp k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
  unfold slack
  rw [if_neg (by omega)]
  rfl

/-- The library's identity with letters for the products, at two sets of sums and products. -/
theorem idnP_slack (np : NormPar) (w w' D pv pv' : ℕ → K) (k : ℕ) :
    Inst.Model.Ledger.idnP np w D pv k = Inst.Model.Ledger.idnP np w' D pv' k +
      slack (fun s => w s - w' s) (fun j => pv j - pv' j) k := by
  by_cases hk9 : k < 9
  · have e : slack (fun s => w s - w' s) (fun j => pv j - pv' j) k = w k - w' k := if_pos hk9
    rw [Inst.Model.Ledger.idnP_j1 np w D pv hk9, Inst.Model.Ledger.idnP_j1 np w' D pv' hk9, e]
    ring
  · by_cases hk17 : 17 ≤ k
    · rw [Inst.Model.Ledger.idnP_of_le np w D pv hk17,
        Inst.Model.Ledger.idnP_of_le np w' D pv' hk17, slack_of_le _ _ hk17, add_zero]
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show pv 1 - Inst.Model.Ledger.Blo D - 2 ^ 23 * Inst.Model.Ledger.Bhi D =
          pv' 1 - Inst.Model.Ledger.Blo D - 2 ^ 23 * Inst.Model.Ledger.Bhi D + (pv 1 - pv' 1)
        ring
      · show Inst.Model.Ledger.Vlo D + (np.eps : K) - pv 0 - 2 ^ 25 * Inst.Model.Ledger.Blo D -
            Inst.Model.Ledger.l1 D + 2 ^ 48 * Inst.Model.Ledger.kc D =
          Inst.Model.Ledger.Vlo D + (np.eps : K) - pv' 0 - 2 ^ 25 * Inst.Model.Ledger.Blo D -
            Inst.Model.Ledger.l1 D + 2 ^ 48 * Inst.Model.Ledger.kc D + -(pv 0 - pv' 0)
        ring
      · show Inst.Model.Ledger.Vhi D - Inst.Model.Ledger.Bhi D - pv 2 - Inst.Model.Ledger.kc D =
          Inst.Model.Ledger.Vhi D - Inst.Model.Ledger.Bhi D - pv' 2 - Inst.Model.Ledger.kc D +
            -(pv 2 - pv' 2)
        ring
      · exact (add_zero _).symm
      · show pv 4 + pv 5 - Inst.Model.Ledger.q1 D =
          pv' 4 + pv' 5 - Inst.Model.Ledger.q1 D + (pv 4 - pv' 4 + (pv 5 - pv' 5))
        ring
      · show pv 6 = pv' 6 + (pv 6 - pv' 6)
        ring
      · show 2 ^ (np.M + 1) + Inst.Model.Ledger.sig D - Inst.Model.Ledger.s0 D - 2 * pv 3 -
            2 ^ 25 * Inst.Model.Ledger.q1 D - 2 * Inst.Model.Ledger.rr D =
          2 ^ (np.M + 1) + Inst.Model.Ledger.sig D - Inst.Model.Ledger.s0 D - 2 * pv' 3 -
            2 ^ 25 * Inst.Model.Ledger.q1 D - 2 * Inst.Model.Ledger.rr D + -(2 * (pv 3 - pv' 3))
        ring
      · exact (add_zero _).symm

/-- Nothing is gained if the nine sums and the seven products do not change. -/
theorem slack_zero {dw dp : ℕ → K} (hw : ∀ s, s < 9 → dw s = 0) (hp : ∀ j, j < 7 → dp j = 0)
    (k : ℕ) : slack dw dp k = 0 := by
  by_cases hk9 : k < 9
  · have e : slack dw dp k = dw k := if_pos hk9
    rw [e, hw k hk9]
  · by_cases hk17 : 17 ≤ k
    · exact slack_of_le _ _ hk17
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp 1 (by omega)
      · show -dp 0 = 0
        rw [hp 0 (by omega), neg_zero]
      · show -dp 2 = 0
        rw [hp 2 (by omega), neg_zero]
      · rfl
      · show dp 4 + dp 5 = 0
        rw [hp 4 (by omega), hp 5 (by omega), add_zero]
      · exact hp 6 (by omega)
      · show -(2 * dp 3) = 0
        rw [hp 3 (by omega), mul_zero, neg_zero]
      · rfl

end Slack

#print axioms row5_c
#print axioms row5_R
#print axioms ledCarry5_value
#print axioms ledLines5_list
#print axioms ledRoots_value
#print axioms ledProducts5_zero
#print axioms idnP_slack
#print axioms slack_zero

/-! ## An evaluation, on made-up numbers

The verifier's functions also work on field elements. Here they are run on 99 made-up cells, nine
made-up sums and seven made-up products, and the library's idnP is run on the same whole numbers.
The 17 results agree, and a third guard holds that they are not all 0. The run does not touch the
forms (it uses field elements), the bytes 80 to 85 (no line with letters reads them) or the routine
that makes the claims. -/

/-- Made-up cells, each from -125 to 125. -/
def cellZ (n : ℕ) : ℤ := (((n * 37 + 11) % 251 : ℕ) : ℤ) - 125
/-- Made-up sums. -/
def sumZ (s : ℕ) : ℤ := ((s * 1000003 + 17 : ℕ) : ℤ) - 2500000
/-- Made-up products. They are not products of numbers of the row. -/
def prodZ (j : ℕ) : ℤ := ((j * 7919 + 5 : ℕ) : ℤ)
/-- The bytes of the made-up cells. -/
def byteZ (n : ℕ) : ℤ := cellZ n + 128
/-- The three numbers of a normalisation. -/
def parZ : NormPar := ⟨44, 30, 53687⟩
/-- The row of the made-up cells, on field elements. -/
def rowZ : Row5 E := row5 fun n => Model.ofInt (cellZ n)

#guard (List.range 17).any fun k => Inst.Model.Ledger.idnP parZ sumZ byteZ prodZ k != 0

#guard (List.range 9).all fun s =>
  isZeroE (subE (ledCarry5 rowZ s (Model.ofInt (sumZ s)))
    (Model.ofInt (Inst.Model.Ledger.idnP parZ sumZ byteZ prodZ s)))

#guard (List.range 8).all fun k =>
  isZeroE (subE
    ((ledLines5 rowZ ((Array.range 7).map fun j => Model.ofInt (prodZ j)) (Model.ofInt parZ.eps)
      (Model.ofNat (2 ^ (parZ.M + 1)))).getD k zeroE)
    (Model.ofInt (Inst.Model.Ledger.idnP parZ sumZ byteZ prodZ (9 + k))))

end OnBytes.Road.Hd
