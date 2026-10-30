-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyBytes.lean: the 21 ledger bytes of the six hidden numbers of a position.

The implementation's protocol text does not give their order. It is: after the NR = 99 bytes of the
normalisation's ledger come 21 more, low byte first: NR + 0 .. 4: c; NR + 5: b; NR + 6 .. 10: u;
NR + 11 .. 15: k; NR + 16, 17: z; NR + 18 .. 20: zs (the six names:
Inst/Model/Head/PolicyDefs.lean). That protocol text is an earlier one, not in this repository.
  `hidByte h n t`     byte n (99 ≤ n < 120) of position t, as a value in [0, 255] (the cell of a
                      byte is the value − 128); 0 for every other n
  `honByte_reads`, `honByte_off`      for the honest numbers of
                      Inst/Model/Head/PolicyHonest.lean: they are recovered from their bytes
                      (under `PolOK`, `Fit`, at every position); off the counted positions the bytes
                      are 0 (no other hypothesis)

Notation:
  `Hid` (Inst/Model/Head/PolicyDefs.lean): the six hidden numbers of a position: c, b, u, k, z, zs.
Limits: integers only. No cell of the trace is defined here, and no affine form of the protocol
reads these bytes here.
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicyHonest
import Inst.Model.Common.LedgerHonest

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model Inst.Model.Ledger

/-- byte n of position t -/
def hidByte (h : Hid) (n t : ℕ) : ℤ :=
  if n < 99 then 0
  else if n < 104 then byteAt (h.c t) (n - 99)
  else if n < 105 then byteAt (h.b t) (n - 104)
  else if n < 110 then byteAt (h.u t) (n - 105)
  else if n < 115 then byteAt (h.k t) (n - 110)
  else if n < 117 then byteAt (h.z t) (n - 115)
  else if n < 120 then byteAt (h.zs t) (n - 117)
  else 0

theorem hidByte_bounds (h : Hid) (n t : ℕ) : 0 ≤ hidByte h n t ∧ hidByte h n t ≤ 255 := by
  unfold hidByte
  split_ifs <;> first | exact byteAt_bounds _ _ | norm_num

/-- numbers that are not negative and within `Hid.Bytes` are recovered from their bytes -/
theorem hidByte_reads {h : Hid} {t : ℕ}
    (h0 : 0 ≤ h.c t ∧ 0 ≤ h.b t ∧ 0 ≤ h.u t ∧ 0 ≤ h.k t ∧ 0 ≤ h.z t ∧ 0 ≤ h.zs t) (h1 : h.Bytes t) :
    b256 (fun n => hidByte h n t) 99 5 = h.c t ∧
    b256 (fun n => hidByte h n t) 104 1 = h.b t ∧
    b256 (fun n => hidByte h n t) 105 5 = h.u t ∧
    b256 (fun n => hidByte h n t) 110 5 = h.k t ∧
    b256 (fun n => hidByte h n t) 115 2 = h.z t ∧
    b256 (fun n => hidByte h n t) 117 3 = h.zs t := by
  obtain ⟨c0, b0, u0, k0, z0, s0⟩ := h0
  obtain ⟨c1, b1, u1, k1, z1, s1⟩ := h1
  refine ⟨b256_of_bytes_lt (fun j hj => ?_) c0 (by norm_num; exact c1),
    b256_of_bytes_lt (fun j hj => ?_) b0 (by norm_num; exact b1),
    b256_of_bytes_lt (fun j hj => ?_) u0 (by norm_num; exact u1),
    b256_of_bytes_lt (fun j hj => ?_) k0 (by norm_num; exact k1),
    b256_of_bytes_lt (fun j hj => ?_) z0 (by norm_num; exact z1),
    b256_of_bytes_lt (fun j hj => ?_) s0 (by norm_num; exact s1)⟩
  · show hidByte h (99 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · show hidByte h (104 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · show hidByte h (105 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), Nat.add_sub_cancel_left]
  · show hidByte h (110 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega), Nat.add_sub_cancel_left]
  · show hidByte h (115 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · show hidByte h (117 + j) t = _
    unfold hidByte
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem hidByte_zero {h : Hid} {t : ℕ}
    (h0 : h.c t = 0 ∧ h.b t = 0 ∧ h.u t = 0 ∧ h.k t = 0 ∧ h.z t = 0 ∧ h.zs t = 0) (n : ℕ) :
    hidByte h n t = 0 := by
  obtain ⟨c0, b0, u0, k0, z0, s0⟩ := h0
  unfold hidByte
  rw [c0, b0, u0, k0, z0, s0]
  split_ifs <;> simp [byteAt]

section
variable {P : Params} {lg : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x : Instance P}

/-- under `PolOK` and `Fit`, the honest numbers are recovered from their bytes, at every position -/
theorem honByte_reads (hp : PolOK lg pol x) (hf : Fit P lg pol) (t : ℕ) :
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 99 5 = (Honest.honH lg pol x).c t ∧
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 104 1 = (Honest.honH lg pol x).b t ∧
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 105 5 = (Honest.honH lg pol x).u t ∧
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 110 5 = (Honest.honH lg pol x).k t ∧
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 115 2 = (Honest.honH lg pol x).z t ∧
    b256 (fun n => hidByte (Honest.honH lg pol x) n t) 117 3 = (Honest.honH lg pol x).zs t :=
  hidByte_reads (Honest.honest_bytes hp hf t).1 (Honest.honest_bytes hp hf t).2

/-- off the counted positions all 21 honest bytes are 0 -/
theorem honByte_off {t : ℕ} (ht : t ∉ x.cnt) (n : ℕ) : hidByte (Honest.honH lg pol x) n t = 0 :=
  hidByte_zero (Honest.honest_off ht) n

end

end Inst.Model.Head.Policy
