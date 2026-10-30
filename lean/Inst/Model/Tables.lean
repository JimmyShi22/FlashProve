-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Tables.lean

The public tables of the integer model. Definitions only.
Source: as in Inst/Model/Program.lean, the definitions follow a paper of this project that is not
part of this repository; text in double quotes is quoted from it, and labels such as (Tab3) are its
names.
-/
import Inst.Model.Program
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Inst.Model

/-! ## The parts of this file

Part 1: `Tables.OK`, the bounds on the five table functions of the program that the proofs rely on.
These are conditions on public parameters, decidable by enumeration.
Part 2: `EX`, a sixth table function, by its recurrence. The acceptance policy under
Inst/Model/Head/ uses it.
Part 3: the look-up tables of the main look-up arguments, as functions of the row.
Part 4: the rounding `rnd` and the layers without rotary step, `rotaryOff`.
Limits. The values of the five table functions are not fixed here, and nothing here relates them to
the real functions SiLU, sigmoid, exp, cos and sin.
The reference values are in Inst/Model/TablesRef.lean, and `tbRef_ok` there proves `Tables.OK` for
them at `ppref`.
-/

/-! ## Part 1. The bounds on the table functions of the program that the proofs rely on -/

/-- The bounds:
(Tab3) "|SILU[ι]| ≤ 4,095 for all ι < 2^16"; (Tab4) "0 ≤ SIGM[ι] ≤ 2^16 on the domain of SIGM",
which is 2^14 ≤ ι < 3·2^14;
(Tab5) "|C[L][i][ȷ]| ≤ 2^12, |S[L][i][ȷ]| ≤ 2^12 for all L, i, ȷ"; (Tab8) "1 ≤ Exp[t] ≤ 2^12 for all
t < 2,307, and Exp[0] = 2^12". Here with `P.expRows` in place of 2,307. (Tab5) is asked for
L < `P.layers`, i < `P.T`, ȷ < `P.ch` / 2. -/
def Tables.OK (P : Params) (tb : Tables) : Prop :=
  (∀ ι < 2 ^ 16, -4095 ≤ tb.SILU (ι : ℕ) ∧ tb.SILU (ι : ℕ) ≤ 4095) ∧
  (∀ ι < 2 ^ 15, 0 ≤ tb.SIGM ((ι : ℕ) + 2 ^ 14) ∧ tb.SIGM ((ι : ℕ) + 2 ^ 14) ≤ 2 ^ 16) ∧
  (∀ L < P.layers, ∀ i < P.T, ∀ jj < P.ch / 2,
    (-2 ^ 12 ≤ tb.C L i jj ∧ tb.C L i jj ≤ 2 ^ 12) ∧ (-2 ^ 12 ≤ tb.S L i jj ∧ tb.S L i jj ≤ 2 ^ 12))
        ∧
  (∀ t < P.expRows.toNat, 1 ≤ tb.Exp (t : ℕ) ∧ tb.Exp (t : ℕ) ≤ 2 ^ 12) ∧ tb.Exp 0 = 2 ^ 12

instance (P : Params) (tb : Tables) : Decidable (tb.OK P) := by unfold Tables.OK; infer_instance

/-! ## Part 2. EX: "G_0 = 2^41, G_{u+1} = ⌈G_u N / 2^32⌉, EX[u] = ⌈G_u / 2^17⌉, with N = 484"

`exG u` is G_u. With N = 484 the values of G are 2^41, 247,808, 1, 1, ..., so those of `EX` are
2^24, 2, 1, 1, ... (`EX 0`: `tab9`, Inst/Model/TablesSanity.lean; `EX 1`, `EX (u + 2)`,
`exG (u + 2)`: `EX_one`, `EX_ge_two`, `exG_ge_two`, Inst/Model/Head/PolicyHonest.lean; `exG 0`: by
definition; that `exG 1` = 247,808 is neither stated nor proved in this library: it is reckoned
from `exG`).
The files on the acceptance policy call `EX` the step table and rely on these values
(Inst/Model/Head/PolicyDefs.lean, field `HE`; Inst/Model/Head/PolicyHonest.lean).
The policy's relations read `EX` directly, and the protocol looks it up through the table
`FE` below. (Of the head: `tableOf` at `HE0`, `HE1` and `RF.keys`, Policy/Rel/LedgerHead.lean.) -/

def exG : ℕ → ℕ
  | 0 => 2 ^ 41
  | u + 1 => (exG u * 484 + (2 ^ 32 - 1)) / 2 ^ 32
/-- EX[u] = ⌈G_u / 2^17⌉. Its values are 2^24, 2, 1, 1, ... -/
def EX (u : ℕ) : ℤ := ((exG u + (2 ^ 17 - 1)) / 2 ^ 17 : ℕ)

/-! ## Part 3. The look-up tables of the main look-up arguments -/

/-- A table: its number of rows, the entry τ(ι) of each row, and its padding value. -/
structure Lut where
  rows : ℕ
  row : ℕ → ℤ
  pad : ℤ

/-- "S_max = 128 · 2,047² = 536,346,752, the cut-off C = 590,592, st = 2^16 − 2^8 = 65,280,
nd = ⌈(4 S_max + 1)/st⌉ = 32,865,
so that 2,307 + nd = 35,172".
Difference from the paper: the shift sh applied to mx − sc before the look-up in Exp (the paper: 8)
and the number u0 of rows of Exp in use (the paper: 2,307) are arguments: C = 2^sh u0,
st = 2^16 − 2^sh, nd = ⌈(4 S_max + 1)/st⌉, written ⌊4 S_max / st⌋ + 1.
(`Att.mx`, `Att.sc`: Inst/Model/Program.lean.)
The paper's numbers are the values at 8 and 2,307 (Inst/Model/TablesSanity.lean). Which pairs are
valid: `ExpOK`. -/
def Smax : ℤ := 128 * 2047 ^ 2
/-- The cut-off C = 2^sh u0; see `Smax`. -/
def cutC (sh u0 : ℕ) : ℤ := 2 ^ sh * u0
/-- st = 2^16 − 2^sh; see `Smax`. -/
def stp (sh : ℕ) : ℤ := 2 ^ 16 - 2 ^ sh
/-- nd = ⌈(4 S_max + 1)/st⌉, written ⌊4 S_max / st⌋ + 1; see `Smax`. -/
def nd (sh : ℕ) : ℕ := (4 * Smax / stp sh).toNat + 1

/-- The valid shifts and numbers of rows in use. 4 ≤ sh ≤ 12; at least one row is in use; the table
of 2^16 rows has space for the rows in use and the unused rows, and its filler rows are at most as
many as its unused rows; C + 2^16 ≤ 2^24.
In the table `tau2` the rows in use are ι < u0 (called live rows in the quotation at `tau2`), the
unused rows u0 ≤ ι < u0 + nd and the filler rows u0 + nd ≤ ι < 2^16 (together called dead rows
there). (The unused rows hold no value of Exp, and they are looked up: in the proof of
`inLut_tau2`, Inst/Model/Att/HonestArith.lean, under its hypotheses, the key of a `gp` from the
cut-off C on is the entry of row u0 + n for an n < nd.) -/
structure ExpOK (sh u0 : ℕ) : Prop where
  lo : 4 ≤ sh
  hi : sh ≤ 12
  pos : 0 < u0
  room : u0 + nd sh ≤ 2 ^ 16
  fill : 2 ^ 16 ≤ u0 + 2 * nd sh
  cut : cutC sh u0 + 2 ^ 16 ≤ 2 ^ 24

instance (sh u0 : ℕ) : Decidable (ExpOK sh u0) :=
  decidable_of_iff (4 ≤ sh ∧ sh ≤ 12 ∧ 0 < u0 ∧ u0 + nd sh ≤ 2 ^ 16 ∧ 2 ^ 16 ≤ u0 + 2 * nd sh ∧ cutC
      sh u0 + 2 ^ 16 ≤ 2 ^ 24)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun h =>
        ⟨h.lo, h.hi, h.pos, h.room, h.fill, h.cut⟩⟩

/-- R8: "ι, for ι < 2^8" -/
def R8 : Lut := ⟨2 ^ 8, fun ι => ι, 0⟩
/-- R16: "ι, for ι < 2^16" -/
def R16 : Lut := ⟨2 ^ 16, fun ι => ι, 0⟩
/-- τ3 is the same table as R16. -/
def tau3 : Lut := R16
/-- FC (clamp): "ι + 2^28 (clamp_2047(ι − 2^15) + 2^11)"; padding τ(2^15) -/
def FC : Lut := ⟨2 ^ 16, fun ι => ι + 2 ^ 28 * (clamp 2047 (ι - 2 ^ 15) + 2 ^ 11), 2 ^ 15 + 2 ^ 39⟩
/-- FL (SiLU): "ι + 2^28 (SILU[ι] + 2^12)"; padding τ(2^15) -/
def FL (tb : Tables) : Lut :=
  ⟨2 ^ 16, fun ι => ι + 2 ^ 28 * (tb.SILU ι + 2 ^ 12), 2 ^ 15 + 2 ^ 28 *
      (tb.SILU (2 ^ 15) + 2 ^ 12)⟩
/-- FS (sigmoid; clamp of the gate): "ι + 2^17 SIGM[ι + 2^14] for ι < 2^15;
ι + 2^28 (clamp_127(ι − 49,152) + 128) + 2^40 for
2^15 ≤ ι < 2^16"; padding τ(2^15) -/
def FS (tb : Tables) : Lut :=
  ⟨2 ^ 16, fun ι => if ι < 2 ^ 15 then ι + 2 ^ 17 * tb.SIGM (ι + 2 ^ 14)
      else ι + 2 ^ 28 * (clamp 127 (ι - 49152) + 128) + 2 ^ 40,
    2 ^ 15 + 2 ^ 28 * (clamp 127 (2 ^ 15 - 49152) + 128) + 2 ^ 40⟩
/-- τ1: "(ι mod 256) + 2^20 ⌊ι/256⌋ + 2^40 [ι ≥ 2^8]"; padding 0 (row 0). Here with 2^sh in place of
2^8. (256 stays.) -/
def tau1 (sh : ℕ) : Lut := ⟨2 ^ 16, fun ι => (ι % 256 : ℕ) + 2 ^ 20 * (ι / 256 : ℕ) +
    (if 2 ^ sh ≤ ι then 2 ^ 40 else 0), 0⟩
/-- τ2: "2^8 ι + 2^33 Exp[ι] for ι < 2,307 (live rows);
C − 2^8 + st (ι − 2,307) + 2^32 for 2,307 ≤ ι < 35,172, and
C − 2^8 + st (ι − 35,172) + ⌊st/2⌋ + 2^32 for 35,172 ≤ ι < 2^16 (dead rows)"; padding C − 2^8 + 2^32
(row 2,307). Here with 2^sh, u0 and u0 + nd in place of 2^8, 2,307 and 35,172. -/
def tau2 (sh u0 : ℕ) (tb : Tables) : Lut :=
  ⟨2 ^ 16, fun ι =>
    if ι < u0 then 2 ^ sh * ι + 2 ^ 33 * tb.Exp ι
    else if ι < u0 + nd sh then cutC sh u0 - 2 ^ sh + stp sh * (ι - u0) + 2 ^ 32
    else cutC sh u0 - 2 ^ sh + stp sh * (ι - (u0 + nd sh : ℕ)) + stp sh / 2 + 2 ^ 32,
    cutC sh u0 - 2 ^ sh + 2 ^ 32⟩
/-- τ4: "(ι mod 256) + 2^20 ⌊ι/256⌋"; padding 0 -/
def tau4 : Lut := ⟨2 ^ 16, fun ι => (ι % 256 : ℕ) + 2 ^ 20 * (ι / 256 : ℕ), 0⟩
/-- FE: "ι + 2^16 EX[ι]"; padding τ(0) = 2^40 -/
def FE : Lut := ⟨2 ^ 16, fun ι => ι + 2 ^ 16 * EX ι, 2 ^ 40⟩

/-! ## Part 4. Rounding, and the layers without rotary step

`rnd` belongs to the paper's specification of the five table functions by real functions. That
specification is not part of this library: `rnd` is used only by the check `rnd_half` in
Inst/Model/TablesSanity.lean. -/

section Spec
open Real

/-- "rnd rounds to the nearest integer, halves away from zero" -/
def rnd (x : ℝ) : ℤ := if 0 ≤ x then ⌊x + 1 / 2⌋ else -⌊-x + 1 / 2⌋



/-- "Layer L ... the rotary flag is off in the layers with L mod 4 = 3 and on in all others" -/
def rotaryOff (L : ℕ) : Prop := L % 4 = 3
instance (L : ℕ) : Decidable (rotaryOff L) := by unfold rotaryOff; infer_instance


end Spec
end Inst.Model
