-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetInstFFUnit.lean: no wrap-around in a feed-forward segment: the hidden units, at a variable
number p.

Theorems with their proofs. All are under `h` (`RFraw`, Inst/Model/FF/Cast.lean): integer cells t
meet the segment's relation, with keys and identities formed in `ZMod p`. All but `cellB` are at
the hidden unit x of layer l at position i (`hl`, `hx`, `hi`).

Main names:
  `unit_facts`: under the hypotheses of its statement, gw, sl, up and hh of the hidden unit are, as
    integers, those of the program's `UNIT` (Inst/Model/Program.lean), and `UNIT.OK` holds.
  `gate_facts`, `shared_facts`: see their docstrings.
The labels: (U1) to (U6) are the steps of `UNIT`; condition (1) is the first clause of `RFraw`; for
the Steps see the head of Inst/Model/Common/Unit.lean.

The number p is variable, with 2^61 - 1 ≤ p (the class `Big p`: Inst/Model/Bound/Base.lean; that p
is prime is not assumed). The namespace is `Cm.TI`.

Why: `Big p` only lifts the size conditions `Unit.Adm` from 2^61 - 1 (`Unit.adm_ref`) to p
(`Cm.TI.Unit.Adm.mono`).

Limits: what each step is, and the notation: the head of Inst/Model/FF/NoWrapUnit.lean. It tells
the sizes D (here `S : Sz D`) and what the table of scales is (the argument `scl`). (The limits on
the prime: the head of Inst/Model/Bound/Base.lean.)
-/
import Inst.Model.FF.NoWrapUnit
import Inst.Model.Bound.Base


set_option autoImplicit false

/- The default table of scales is not in sight in this file (`Scl.ref` is no instance here): what
reads a table reads the variable `scl`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TI.FFSeg

open Inst.Model Inst.Model.FFSeg

variable {p : ℕ} [Big p]

variable [scl : Scl]

open Finset hiding val

namespace NWU
open Inst.Model.FFSeg.NWU

section
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}
variable (h : RFraw D tb L0 first (ZMod p) w emb tok t)
include h

omit [Big p] in
theorem cellB {c : Cell} (hc : c.Valid D) : -262143 ≤ t c ∧ t c ≤ 262143 := by
  have := abs_lt.mp (h.1 c hc)
  constructor <;> omega

variable {l x i : ℕ} (hl : l < D.nl) (hx : x < D.f) (hi : i < D.T)
include hl hx hi

omit [Big p] in
/-- Condition (1) for the seven values `uv t l x i`: under `h`, `hl`, `hx`, `hi` they meet the
bounds `Unit.Small`. -/
theorem small : Unit.Small (2 ^ 18) (257 * 2 ^ 18) (uv t l x i) := by
  have g0 := cellB h (c := ⟨.g0, 0, l, x, i⟩) ⟨(by decide : 0 < 1), hl, hx, hi⟩
  have gh0 := cellB h (c := ⟨.gh, 0, l, x, i⟩) ⟨(by decide : 0 < 2), hl, hx, hi⟩
  have gh1 := cellB h (c := ⟨.gh, 1, l, x, i⟩) ⟨(by decide : 1 < 2), hl, hx, hi⟩
  have gc := cellB h (c := ⟨.gc, 0, l, x, i⟩) ⟨(by decide : 0 < 1), hl, hx, hi⟩
  have sl0 := cellB h (c := ⟨.sl, 0, l, x, i⟩) ⟨(by decide : 0 < 2), hl, hx, hi⟩
  have sl1 := cellB h (c := ⟨.sl, 1, l, x, i⟩) ⟨(by decide : 1 < 2), hl, hx, hi⟩
  have up0 := cellB h (c := ⟨.up, 0, l, x, i⟩) ⟨(by decide : 0 < 2), hl, hx, hi⟩
  have up1 := cellB h (c := ⟨.up, 1, l, x, i⟩) ⟨(by decide : 1 < 2), hl, hx, hi⟩
  have rg := cellB h (c := ⟨.rg, 0, l, x, i⟩) ⟨(by decide : 0 < 1), hl, hx, hi⟩
  have ru := cellB h (c := ⟨.ru, 0, l, x, i⟩) ⟨(by decide : 0 < 1), hl, hx, hi⟩
  constructor <;> simp only [uv, val, Arr.nCell, Arr.off, sum_range_succ,
      sum_range_zero, Int.cast_id]
    <;> rw [abs_le] <;> constructor <;> omega

omit [Big p] in
/-- Under `h`, `hl`, `hx`, `hi`, the four keys `keyG0`, `keyF`, `keyCG`, `keyUT`, which read no
accumulator, are congruent modulo p to entries of their tables (`Unit.Gate`). -/
theorem gate : Unit.Gate (p : ℤ) tb (uv t l x i) := by
  exact ⟨key_inLut D tb L0 first w emb tok t _ h (s := .G0) hl rfl hx hi,
    key_inLut D tb L0 first w emb tok t _ h (s := .F) hl rfl hx hi,
    key_inLut D tb L0 first w emb tok t _ h (s := .CG) hl rfl hx hi,
    key_inLut D tb L0 first w emb tok t _ h (s := .UT) hl rfl hx hi⟩

omit [Big p] in
/-- Under `h`, `hl`, `hx`, `hi`, all eight keys are congruent modulo p to entries of their tables
(`Unit.Keys`). -/
theorem keys :
    Unit.Keys (p : ℤ) tb (kG D l x) (kU D l x) (Ag D t (fun l => LW.ofInt ℤ (w l)) l x i)
      (Au D t (fun l => LW.ofInt ℤ (w l)) l x i) (uv t l x i) := by
  refine ⟨gate h hl hx hi, ?_, ?_, ?_, ?_⟩
  · exact key_inLut D tb L0 first w emb tok t _ h (s := .G) hl rfl hx hi
  · exact key_inLut D tb L0 first w emb tok t _ h (s := .GH) hl rfl hx hi
  · exact key_inLut D tb L0 first w emb tok t _ h (s := .U) hl rfl hx hi
  · exact key_inLut D tb L0 first w emb tok t _ h (s := .UH) hl rfl hx hi

/-- Steps L1, L2, L3 at every hidden unit: (U2), (U3), (U4) as functions of gw, with the range
conditions of (U2) and (U5). (not all hypotheses are named here: see the statement below) -/
theorem gate_facts {P : Params} (hOK : tb.OK P) (S : Sz D) :
    val t .g0 l x i = lowByte (gw t l x i) ∧
    (-2 ^ 14 ≤ val t .gh l x i ∧ val t .gh l x i < 2 ^ 14) ∧
    val t .gc l x i = clamp 127 (val t .gh l x i) ∧
    val t .sl l x i = tb.SILU (256 * val t .gc l x i + val t .g0 l x i + 2 ^ 15) ∧
    Fits16 (val t .up l x i) ∧
    |val t .sl l x i| ≤ 4095 := by
  obtain ⟨a1, -, a3, a4, a5, a6, -, a8⟩ :=
    Unit.gate_sound (Cm.TI.Unit.Adm.mono (Unit.adm_ref (S.kG l x) (S.kU l x)) (big_pow p))
      (Unit.TabOK.of_ok hOK) (small h hl hx hi) (gate h hl hx hi)
  exact ⟨a1, a3, a4, a5, a6, a8⟩

/-- Steps L7, L7r: under the hypotheses of its statement, gw, sl, up and hh of the unit are those of
the program's `UNIT`, and `UNIT.OK` holds, on every input whose two accumulators are those of the
keys (`eg`, `eu`) and whose entries are small (`hz`, `hg`, `hu`). -/
theorem unit_facts {P : Params} (hOK : tb.OK P) (S : Sz D) {z wg wu : Vec}
    (eg : Ag D t (fun l => LW.ofInt ℤ (w l)) l x i = dot D.d z wg)
    (eu : Au D t (fun l => LW.ofInt ℤ (w l)) l x i = dot D.d z wu) (hz : ∀ j < D.d, |z j| ≤ 2047)
    (hg : ∀ j < D.d, |wg j| ≤ 2 ^ 12) (hu : ∀ j < D.d, |wu j| ≤ 2 ^ 12) :
    gw t l x i = UNIT.gw D.d z wg (kG D l x) ∧
    val t .sl l x i = UNIT.sl tb D.d z wg (kG D l x) ∧
    val t .up l x i = UNIT.up D.d z wu (kU D l x) ∧
    hh t l x i = UNIT.hh tb D.d z wg wu (kG D l x) (kU D l x) ∧
    UNIT.OK D.d z wg wu (kG D l x) (kU D l x) := by
  obtain ⟨a1, -, -, -, a5, a6, a7, a8, -, -⟩ :=
    Unit.unit_sound (Cm.TI.Unit.Adm.mono (Unit.adm_ref (S.kG l x) (S.kU l x)) (big_pow p))
      (Unit.TabOK.of_ok hOK) (small h hl hx hi) (by rw [eg]; exact acc_le S.d hz hg)
      (by rw [eu]; exact acc_le S.d hz hu) (keys h hl hx hi) eg eu
  exact ⟨a1, a5, a6, a7, a8⟩

/-- (U1), (U5) on a dense layer and on the shared expert (Step L7). (not all hypotheses are named
here: see the statement below) -/
theorem shared_facts {P : Params} (hOK : tb.OK P) (S : Sz D) (hr : routed D l x = false)
    (hm : ∀ j < D.d, |val t .m l j i| ≤ 2047) (hg : ∀ j < D.d, |(w l).Wg j x| ≤ 2 ^ 12)
    (hu : ∀ j < D.d, |(w l).Wu j x| ≤ 2 ^ 12) :
    gw t l x i = rhu (dot D.d (fun j => val t .m l j i) fun j => (w l).Wg j x) (D.Pl l).kg ∧
    val t .up l x i =
      rhu (dot D.d (fun j => val t .m l j i) fun j => (w l).Wu j x) (D.Pl l).ku := by
  obtain ⟨eg, eu⟩ := acc_shared (t := t) (w := w) (i := i) hr
  obtain ⟨a1, -, a3, -, -⟩ := unit_facts h hl hx hi hOK S eg eu hm hg hu
  have k1 : kG D l x = (D.Pl l).kg := by unfold FFSeg.kG; rw [hr]; rfl
  have k2 : kU D l x = (D.Pl l).ku := by unfold FFSeg.kU; rw [hr]; rfl
  rw [k1] at a1
  rw [k2] at a3
  exact ⟨a1, a3⟩

end

end NWU

end Cm.TI.FFSeg
