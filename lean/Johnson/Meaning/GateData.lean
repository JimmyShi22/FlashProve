-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateData.lean: the test that the words of the verifier's tables SILU and FS (its
sigmoid half), at the stored example's numbers (step 2^-8, bound 4095), are the library's stored
words; as a walk over the distance a from the tables' middle. Definitions, and what a yes of the
walk says.

At the distance a there are four words: SILU and the sigmoid below the middle (not at a = 0) and
above it (not at a = 16384). The library stores SILU + 4095 in Data.silu and the sigmoid in
Data.sigm, 13 bits an entry, both from the argument -16384 on.
  stepOK a x: the four comparisons at the distance a, from the power x = e^(a/256); and that the
    stored words of SILU do not pass 8190, so that the library's clamp leaves them.
  gateOK u n a x: stepOK at a, a + 1, ..., n of them, with the power carried along.
  gateOK_spec: what its yes says. xAt_add: the powers compose. xAtS: xAt for a long evaluation.
  chunkOK k: the walk over the 1024 distances from 1024 k on (k = 16: the one distance 16384).
-/
import Johnson.Meaning.GateLists
import Inst.Model.TablesRef

set_option autoImplicit false

namespace Meaning.Gate

open OnBytes.Model.Layer (fxOne)
open Meaning.Rope (xAt)
open Inst.Model (dec)

/-- The four comparisons at the distance a. -/
def stepOK (a x : ℕ) : Bool :=
  (a == 0 ||
    (siluOf 8 4095 x a true == dec Inst.Model.Data.silu 13 (16384 - a) + 1 &&
      decide (dec Inst.Model.Data.silu 13 (16384 - a) ≤ 8190) &&
      sigOf x true == 16 * min (dec Inst.Model.Data.sigm 13 (16384 - a)) 4096)) &&
  (a == 16384 ||
    (siluOf 8 4095 x a false == dec Inst.Model.Data.silu 13 (16384 + a) + 1 &&
      decide (dec Inst.Model.Data.silu 13 (16384 + a) ≤ 8190) &&
      sigOf x false == 16 * min (dec Inst.Model.Data.sigm 13 (16384 + a)) 4096))

/-- The walk. -/
def gateOK (u : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, a, x => stepOK a x && gateOK u n (a + 1) (x * u / fxOne)

/-- What a yes of the walk says. -/
theorem gateOK_spec (u : ℕ) : ∀ (n a x : ℕ), gateOK u n a x = true →
    ∀ j, j < n → stepOK (a + j) (xAt u j x) = true
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, a, x, h, j, hj => by
    have h' : (stepOK a x && gateOK u n (a + 1) (x * u / fxOne)) = true := h
    rw [Bool.and_eq_true] at h'
    cases j with
    | zero => exact h'.1
    | succ j =>
      have y := gateOK_spec u n (a + 1) (x * u / fxOne) h'.2 j (by omega)
      have e : a + (j + 1) = a + 1 + j := by omega
      rw [e]
      exact y

/-- The powers compose. -/
theorem xAt_add (u : ℕ) : ∀ (m j x : ℕ), xAt u (m + j) x = xAt u j (xAt u m x)
  | 0, j, x => by rw [Nat.zero_add]; rfl
  | m + 1, j, x => by
    have e : m + 1 + j = (m + j) + 1 := by omega
    rw [e]
    exact xAt_add u m j (x * u / fxOne)

/-- xAt, written so that an evaluation step by step has each power as a numeral before it goes on:
the match asks for the number's first constructor. Without it the kernel carries a term as deep as
the number of steps. -/
def xAtS (u : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | m + 1, x =>
    match x * u / fxOne with
    | 0 => xAtS u m 0
    | y + 1 => xAtS u m (y + 1)

theorem xAtS_eq (u : ℕ) : ∀ (m x : ℕ), xAtS u m x = xAt u m x
  | 0, _ => rfl
  | m + 1, x => by
    show (match x * u / fxOne with
      | 0 => xAtS u m 0
      | y + 1 => xAtS u m (y + 1)) = xAt u m (x * u / fxOne)
    cases x * u / fxOne with
    | zero => exact xAtS_eq u m 0
    | succ y => exact xAtS_eq u m (y + 1)

/-- The walk over the distances from 1024 k on: 1024 of them, or the one distance 16384 at
k = 16. -/
def chunkOK (k : ℕ) : Bool :=
  gateOK (stepOf 8) (if k == 16 then 1 else 1024) (1024 * k) (xAtS (stepOf 8) (1024 * k) fxOne)

end Meaning.Gate
