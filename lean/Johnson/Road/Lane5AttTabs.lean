-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttTabs.lean

The tables of the attention sub-proof's lookup calls, the verifier's beside the library's.

The lookup tests that a key is a row of THE VERIFIER's table of the call. The library's relation of
an attention segment (Inst.Model.AttSeg.RFraw) asks that a key is an entry of THE LIBRARY's table
(Inst.Model.AttSeg.lut: tau1, tau2, tau3, tau4 of Inst/Model/Tables.lean). This file says that they
are the same tables, in the sense "Hd.IsLut" of Johnson/Road/HeadTabs.lean, which the head's and the
layers' files use too: as many rows; the word in row u is the residue of a natural number that, as
an integer, is the library's row u; the same for the padding row. The laws IsLut.inLut, of_inLut and
pad_value there carry that to every reading of the verifier's field elements.

Rows (for every row number t):
* "rowKR_eq": rowKR sh t is row t of tau1 sh. "rowWH_eq": rowWH t is row t of tau4. No condition.
* "rowKFD_eq": rowKFD Tt (shdOf Tt.size Sm sh) sh t is row t of tau2 sh Tt.size tb, IF
    the verifier's bound Sm on a score is the library's constant 128 * 2047^2 (so at ldh = 7 alone);
    sh ≤ 12 (the verifier's own test af-policy-sh has 4 ≤ sh ≤ 12);
    the table of exponentials has an entry (the verifier's C - 2^sh is a cut-off subtraction);
    tb.Exp is Tt at the rows below Tt.size.
  It is arithmetic in letters: no entry of a table is computed.
Calls (a record Call with that table):
* "isLut_KR", "isLut_WH", "isLut_KFD"; the kind r16 is Hd.isLut_R16 as it stands, since tau3 is R16
  by definition. isLut_KFD asks besides: 2^16 rows (kFD = 16: the library's tau2 has 2^16 rows);
  fewer than 2^16 entries of Tt, each at most 2^12 (so that a row is below the field's prime, and
  the word is the residue).
What layCall returns:
* "lutK": the library's table for a kind of call, a shift, a number of live rows.
* "isLut_layCall".

On kFD = 16. The verifier's test af-policy-kF asks 2^kFD rows to hold the live and the dead rows. At
ldh = 7 the number nHD of dead rows alone is not above 2^15 at every admitted shift: at sh = 4 it is
4 * 536,346,752 / 65,520 + 1 = 32,745, below 32,768. With the 2,307 live rows of the table at
S = 12, rx = 8 the sum is above 2^15 at every admitted shift, so that the test admits kFD = 16 alone
there.
That is arithmetic by hand; here kFD = 16 is a hypothesis.

Not claimed: what the lookup shows; which call of a shape has which kind and shift
(Johnson/Road/Lane5AttCalls.lean).
-/
import Johnson.Road.HeadTabs
import Johnson.Road.Lane5AttPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model (Call)
open Attention (rowKR rowWH rowKFD shdOf tableOf)

/-! ## Rows -/

/-- Row t of the verifier's table of kind KR is row t of the library's tau1. -/
theorem rowKR_eq (sh t : ℕ) : ((rowKR sh t : ℕ) : ℤ) = (tau1 sh).row t := by
  show ((t % 256 + t / 256 * 2 ^ 20 + (if t ≥ 2 ^ sh then 2 ^ 40 else 0) : ℕ) : ℤ) =
    ((t % 256 : ℕ) : ℤ) + 2 ^ 20 * ((t / 256 : ℕ) : ℤ) + (if 2 ^ sh ≤ t then 2 ^ 40 else 0)
  by_cases h : 2 ^ sh ≤ t
  · rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    push_cast
    ring

theorem rowKR_lt (sh : ℕ) {t : ℕ} (ht : t < 65536) : rowKR sh t < 2 ^ 41 := by
  have e : rowKR sh t = t % 256 + t / 256 * 2 ^ 20 + (if t ≥ 2 ^ sh then 2 ^ 40 else 0) := rfl
  rw [e]
  split_ifs <;> omega

/-- Row t of the verifier's table of kind WH is row t of the library's tau4. -/
theorem rowWH_eq (t : ℕ) : ((rowWH t : ℕ) : ℤ) = tau4.row t := by
  show ((t % 256 + t / 256 * 2 ^ 20 : ℕ) : ℤ) =
    ((t % 256 : ℕ) : ℤ) + 2 ^ 20 * ((t / 256 : ℕ) : ℤ)
  push_cast
  ring

theorem rowWH_lt {t : ℕ} (ht : t < 65536) : rowWH t < 2 ^ 41 := by
  have e : rowWH t = t % 256 + t / 256 * 2 ^ 20 := rfl
  rw [e]
  omega

section KFD

variable {sh Sm : ℕ} (hsh : sh ≤ 12) (hS : (Sm : ℤ) = Smax)

include hsh in
theorem pow_sh_le : 2 ^ sh ≤ 4096 :=
  le_trans (Nat.pow_le_pow_right (by norm_num) hsh) (by norm_num)

include hsh in
/-- The verifier's step between dead rows is the library's. -/
theorem rho_eq : ((65536 - 2 ^ sh : ℕ) : ℤ) = stp sh := by
  have h := pow_sh_le hsh
  unfold stp
  rw [Nat.cast_sub (by omega)]
  push_cast
  norm_num

include hsh hS in
/-- The verifier's number of dead rows is the library's. -/
theorem nHD_eq (u0 : ℕ) : (shdOf u0 Sm sh).nHD = nd sh := by
  have h := pow_sh_le hsh
  have hρ : 0 < 65536 - 2 ^ sh := by omega
  show (4 * Sm + 1 + (65536 - 2 ^ sh) - 1) / (65536 - 2 ^ sh) = (4 * Smax / stp sh).toNat + 1
  have e1 : 4 * Sm + 1 + (65536 - 2 ^ sh) - 1 = 4 * Sm + (65536 - 2 ^ sh) := by omega
  have e2 : 4 * Smax / stp sh = ((4 * Sm / (65536 - 2 ^ sh) : ℕ) : ℤ) := by
    rw [← hS, ← rho_eq hsh]
    norm_cast
  rw [e1, Nat.add_div_right _ hρ, e2, Int.toNat_natCast]

include hsh hS in
/-- **Row t of the verifier's table of kind KFD is row t of the library's tau2.** -/
theorem rowKFD_eq {Tt : Array ℕ} (h0 : 0 < Tt.size) {tb : Tables}
    (hE : ∀ ι : ℕ, ι < Tt.size → tb.Exp ι = ((Tt.getD ι 0 : ℕ) : ℤ)) (t : ℕ) :
    ((rowKFD Tt (shdOf Tt.size Sm sh) sh t : ℕ) : ℤ) = (tau2 sh Tt.size tb).row t := by
  have hp := pow_sh_le hsh
  have hρ := rho_eq hsh
  have hn := nHD_eq hsh hS Tt.size
  have hC : ((Tt.size * 2 ^ sh - 2 ^ sh : ℕ) : ℤ) = cutC sh Tt.size - 2 ^ sh := by
    unfold cutC
    rw [Nat.cast_sub (Nat.le_mul_of_pos_left _ h0)]
    push_cast
    ring
  have h2 : stp sh / 2 = (((65536 - 2 ^ sh) / 2 : ℕ) : ℤ) := by
    rw [← hρ]
    norm_cast
  show ((if t < Tt.size then t * 2 ^ sh + Tt.getD t 0 * 2 ^ 33
      else if t < Tt.size + (shdOf Tt.size Sm sh).nHD then
        Tt.size * 2 ^ sh - 2 ^ sh + (65536 - 2 ^ sh) * (t - Tt.size) + 2 ^ 32
      else Tt.size * 2 ^ sh - 2 ^ sh +
        (65536 - 2 ^ sh) * (t - Tt.size - (shdOf Tt.size Sm sh).nHD) + (65536 - 2 ^ sh) / 2 +
        2 ^ 32 : ℕ) : ℤ) =
    (if t < Tt.size then 2 ^ sh * (t : ℤ) + 2 ^ 33 * tb.Exp t
      else if t < Tt.size + nd sh then
        cutC sh Tt.size - 2 ^ sh + stp sh * ((t : ℤ) - (Tt.size : ℤ)) + 2 ^ 32
      else cutC sh Tt.size - 2 ^ sh + stp sh * ((t : ℤ) - ((Tt.size + nd sh : ℕ) : ℤ)) +
        stp sh / 2 + 2 ^ 32)
  rw [hn]
  by_cases c1 : t < Tt.size
  · rw [if_pos c1, if_pos c1, hE t c1]
    push_cast
    ring
  · rw [if_neg c1, if_neg c1]
    by_cases c2 : t < Tt.size + nd sh
    · rw [if_pos c2, if_pos c2, Nat.cast_add, Nat.cast_add, Nat.cast_mul, hC, hρ,
        Nat.cast_sub (Nat.le_of_not_lt c1)]
      norm_num
    · rw [if_neg c2, if_neg c2, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul, hC, hρ,
        h2, Nat.sub_sub, Nat.cast_sub (Nat.le_of_not_lt c2)]
      norm_num

include hsh in
theorem rowKFD_lt {Tt : Array ℕ} (hu : Tt.size < 65536)
    (hT : ∀ ι : ℕ, ι < Tt.size → Tt.getD ι 0 ≤ 4096) {t : ℕ} (ht : t < 65536) :
    rowKFD Tt (shdOf Tt.size Sm sh) sh t < 2 ^ 47 := by
  have hp := pow_sh_le hsh
  have a1 : t * 2 ^ sh ≤ 65536 * 4096 := Nat.mul_le_mul ht.le hp
  have a2 : Tt.size * 2 ^ sh ≤ 65536 * 4096 := Nat.mul_le_mul hu.le hp
  have a3 : ∀ m : ℕ, m ≤ 65536 → (65536 - 2 ^ sh) * m ≤ 65536 * 65536 := fun m hm =>
    Nat.mul_le_mul (Nat.sub_le _ _) hm
  have e : rowKFD Tt (shdOf Tt.size Sm sh) sh t =
      (if t < Tt.size then t * 2 ^ sh + Tt.getD t 0 * 2 ^ 33
      else if t < Tt.size + (shdOf Tt.size Sm sh).nHD then
        Tt.size * 2 ^ sh - 2 ^ sh + (65536 - 2 ^ sh) * (t - Tt.size) + 2 ^ 32
      else Tt.size * 2 ^ sh - 2 ^ sh +
        (65536 - 2 ^ sh) * (t - Tt.size - (shdOf Tt.size Sm sh).nHD) + (65536 - 2 ^ sh) / 2 +
        2 ^ 32) := rfl
  rw [e]
  have a4 : Tt.size * 2 ^ sh - 2 ^ sh ≤ 65536 * 4096 := le_trans (Nat.sub_le _ _) a2
  have a5 : (65536 - 2 ^ sh) / 2 ≤ 65536 := le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
  generalize Tt.size * 2 ^ sh - 2 ^ sh = A at a4 ⊢
  generalize (65536 - 2 ^ sh) / 2 = H at a5 ⊢
  by_cases c1 : t < Tt.size
  · rw [if_pos c1]
    have b := hT t c1
    generalize t * 2 ^ sh = G at a1 ⊢
    omega
  · rw [if_neg c1]
    by_cases c2 : t < Tt.size + (shdOf Tt.size Sm sh).nHD
    · rw [if_pos c2]
      have b := a3 (t - Tt.size) (by omega)
      generalize (65536 - 2 ^ sh) * (t - Tt.size) = G at b ⊢
      omega
    · rw [if_neg c2]
      have b := a3 (t - Tt.size - (shdOf Tt.size Sm sh).nHD) (by omega)
      generalize (65536 - 2 ^ sh) * (t - Tt.size - (shdOf Tt.size Sm sh).nHD) = G at b ⊢
      omega

end KFD

/-! ## Calls -/

/-- A row of a table that tableOf makes. -/
theorem tableOf_at {c : Call} {k : ℕ} {row : ℕ → ℕ} (hτ : c.tau = tableOf k row) {t : ℕ}
    (ht : t < 2 ^ k) (hb : row t < 18446744069414584321) :
    c.tauAt t = Model.fOfNat (row t) := by
  have hτ' : c.tau = some ((Array.range (2 ^ k)).map fun t => UInt64.ofNat (row t)) := hτ
  rw [Hd.tauAt_some hτ', Hd.getD_map_rangeT _ _ _ _ ht]
  exact Hd.word_eq_fOfNat hb

/-- A call with the table of kind KR for the shift sh has the library's tau1 sh. -/
theorem isLut_KR {c : Call} {sh : ℕ} (hτ : c.tau = tableOf 16 (rowKR sh)) (hk : c.k = 16)
    (h0 : c.t0 = 0) : Hd.IsLut c (tau1 sh) where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    have hb := rowKR_lt sh hu'
    exact ⟨rowKR sh u, tableOf_at hτ hu' (by omega), rowKR_eq sh u⟩
  pad := by
    have hb := rowKR_lt sh (t := 0) (by norm_num)
    refine ⟨rowKR sh 0, by rw [h0]; exact tableOf_at hτ (by norm_num) (by omega), ?_⟩
    rw [rowKR_eq]
    show ((0 % 256 : ℕ) : ℤ) + 2 ^ 20 * ((0 / 256 : ℕ) : ℤ) + (if 2 ^ sh ≤ 0 then 2 ^ 40 else 0) = 0
    rw [if_neg (by have := Nat.two_pow_pos sh; omega)]
    norm_num

/-- A call with the table of kind WH has the library's tau4. -/
theorem isLut_WH {c : Call} (hτ : c.tau = tableOf 16 rowWH) (hk : c.k = 16) (h0 : c.t0 = 0) :
    Hd.IsLut c tau4 where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    have hb := rowWH_lt hu'
    exact ⟨rowWH u, tableOf_at hτ hu' (by omega), rowWH_eq u⟩
  pad := by
    have hb := rowWH_lt (t := 0) (by norm_num)
    exact ⟨rowWH 0, by rw [h0]; exact tableOf_at hτ (by norm_num) (by omega), rfl⟩

/-- **A call with the table of kind KFD has the library's tau2.** -/
theorem isLut_KFD {c : Call} {sh Sm : ℕ} {Tt : Array ℕ} {tb : Tables} (hsh : sh ≤ 12)
    (hS : (Sm : ℤ) = Smax) (h0 : 0 < Tt.size) (hu : Tt.size < 65536)
    (hT : ∀ ι : ℕ, ι < Tt.size → Tt.getD ι 0 ≤ 4096)
    (hE : ∀ ι : ℕ, ι < Tt.size → tb.Exp ι = ((Tt.getD ι 0 : ℕ) : ℤ))
    (hτ : c.tau = tableOf 16 (rowKFD Tt (shdOf Tt.size Sm sh) sh)) (hk : c.k = 16)
    (ht0 : c.t0 = Tt.size) : Hd.IsLut c (tau2 sh Tt.size tb) where
  rows := by rw [hk]; rfl
  row u hu' := by
    have hu2 : u < 65536 := hu'
    have hb := rowKFD_lt (Sm := Sm) hsh hu hT hu2
    exact ⟨_, tableOf_at hτ hu2 (by omega), rowKFD_eq hsh hS h0 hE u⟩
  pad := by
    have hb := rowKFD_lt (Sm := Sm) hsh hu hT hu
    refine ⟨_, by rw [ht0]; exact tableOf_at hτ hu (by omega), ?_⟩
    rw [rowKFD_eq hsh hS h0 hE]
    show (if Tt.size < Tt.size then 2 ^ sh * ((Tt.size : ℕ) : ℤ) + 2 ^ 33 * tb.Exp Tt.size
      else if Tt.size < Tt.size + nd sh then
        cutC sh Tt.size - 2 ^ sh + stp sh * (((Tt.size : ℕ) : ℤ) - (Tt.size : ℤ)) + 2 ^ 32
      else cutC sh Tt.size - 2 ^ sh +
        stp sh * (((Tt.size : ℕ) : ℤ) - ((Tt.size + nd sh : ℕ) : ℤ)) + stp sh / 2 + 2 ^ 32) =
      cutC sh Tt.size - 2 ^ sh + 2 ^ 32
    have hnd : 0 < nd sh := Nat.succ_pos _
    rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_add_of_pos_right hnd)]
    ring

/-! ## What layCall returns -/

/-- The library's table for a kind of call, a shift, a number of live rows and table functions. -/
def lutK (tb : Tables) (u0 : ℕ) : Attention.Table → ℕ → Lut
  | .kr, sh => tau1 sh
  | .kfd, sh => tau2 sh u0 tb
  | .r16, _ => tau3
  | .wh, _ => tau4

/-- **The call that layCall returns has the library's table of its kind and shift.** -/
theorem isLut_layCall {cf : Attention.Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {x : Attention.Listed}
    {k : Attention.ACall} (h : Attention.layCall cf HA Sm Tt x = Except.ok k) {tb : Tables}
    (hkF : cf.kFD = 16) (hsh : x.2.2.1 ≤ 12) (hS : (Sm : ℤ) = Smax) (h0 : 0 < Tt.size)
    (hu : Tt.size < 65536) (hT : ∀ ι : ℕ, ι < Tt.size → Tt.getD ι 0 ≤ 4096)
    (hE : ∀ ι : ℕ, ι < Tt.size → tb.Exp ι = ((Tt.getD ι 0 : ℕ) : ℤ)) :
    k.kind = x.2.1 ∧ k.sh = x.2.2.1 ∧ Hd.IsLut k.call (lutK tb Tt.size k.kind k.sh) := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  refine ⟨rfl, rfl, ?_⟩
  cases kind with
  | kr => exact isLut_KR rfl rfl rfl
  | wh => exact isLut_WH rfl rfl rfl
  | r16 => exact Hd.isLut_R16 rfl rfl rfl
  | kfd =>
    refine isLut_KFD hsh hS h0 hu hT hE ?_ hkF rfl
    show tableOf cf.kFD _ = tableOf 16 _
    rw [hkF]

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.rowKFD_eq
#print axioms OnBytes.Road.L5.isLut_KR
#print axioms OnBytes.Road.L5.isLut_WH
#print axioms OnBytes.Road.L5.isLut_KFD
#print axioms OnBytes.Road.L5.isLut_layCall
