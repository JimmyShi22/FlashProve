-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Lawful.lean: what `LawfulW`, this library's rendering of the programs' tests on the
  words of one layer, says, and the class `Lawful`: "the table in scope is lawful".

  The words of a layer are its numbers in the table of quantization scales of a feed-forward segment
  (`LayerScale`, Inst/Model/Program.lean); the programs' tests: the head of
  Inst/Model/FF/ScalesDef.lean. Other files of this folder say "valid scales" for a lawful table.
  The definitions (`Scales.Shift`, `SiteU`, `SiteW`, `LawfulW`, `Ranges`) are in
  Inst/Model/FF/ScalesDef.lean; the class `Scl`, which carries the table of scales of a segment, is
  in Inst/Model/Scl.lean.

  Main names:
    `lawfulW_iff`: `LawfulW s ↔ Ranges s`: `LawfulW` says exactly 5 ≤ kq, kk ≤ 32, with kq = kk
      unless both are 16 or more; 1 ≤ kv, kg, ku, kg', ku' ≤ 24; 1 ≤ ko ≤ 19; 10 ≤ kd ≤ 19; 8 ≤ kr ≤
      24; and the ranges of the two normalisations (`NormPar.OK`). `LawfulW` is decidable.
    `LawfulFF κ`: `LawfulW` at the four layers of a segment. Decidable.
    `lawfulW_ref`: the reference words are lawful.
    `Scales.wq_int`, `wv_int`, `wo_int`, `wd_int`, `led_K`: the no-overflow conditions that the
      proofs use (`AdmP`, `AdmS`, `Ledger.Adm`), from the ranges, at the reference sizes and
      p = 2^61 − 1.
    `Lawful`: the class: the words of every layer of the table in scope are lawful (`LawfulW`). A
      theorem that needs it has the argument `[Lawful]`. In this file it has an instance at the
      reference table `Scl.ref` and none else; for another table the caller gives the proof
      (`lawful_of`, Inst/Model/FF/Scales.lean).

  Why: the clause of `Lawful` is "∀ l", over all natural numbers, because the records of the files
  in which the sizes D are not fixed (`AdmN`, `AdmP`, `AdmS`, `Sz`, `SzR`, `Par`) quantify over all
  l; at `Dim.ref` (Inst/Model/FF/Index.lean: four layers) only l < 4 is ever read.

  Notation: the programs: the implementation that comes with this Lean code (lean/GLOSSARY.md); `s`:
  a `LayerScale`: the scales of one layer; kq, kk, kv, ko, kg, ku, kd, kr, kg', ku': natural
  numbers: the ten shifts of a layer (Inst/Model/Program.lean); `κ`: ℕ → `LayerScale`: the scales of
  layer l of the segment (`Scl.κ`) (Inst/Model/Scl.lean); D: a `Dim`: the sizes of a feed-forward
  segment (Inst/Model/FF/Index.lean); p: an integer: the modulus (`Ledger.Adm`)
  (Inst/Model/Common/LedgerSound.lean); `Shift`, `SiteU`, `SiteW`: the check on a shift's range and
  the two no-overflow conditions of a rounding site (Inst/Model/FF/ScalesDef.lean).

  Limits: what `LawfulW` is against the programs' tests, and its departures: the header of
  Inst/Model/FF/Scales.lean.
  Terms: lean/GLOSSARY.md.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.ScalesDef
import Inst.Model.Scl
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Inst.Model.FFSeg

open Finset Scales

namespace Scales

/-! the tests of one shift, decided for every value in its range -/

theorem qk_of : ∀ k ≤ 32, SiteW 2 (2 * 2 ^ 12 * 5120 * BC * BW) (2 ^ 15) k → 5 ≤ k := by
  decide +kernel
theorem qk_to :
    ∀ k ≤ 32,
      5 ≤ k → Shift 2 k ∧ SiteU (2 ^ 16) k ∧ SiteW 2 (2 * 2 ^ 12 * 5120 * BC * BW) (2 ^ 15) k := by
  decide +kernel
theorem o_of : ∀ k ≤ 24, SiteU (2 ^ 41) k → k ≤ 19 := by decide +kernel
theorem o_to :
    ∀ k ≤ 19, 1 ≤ k → Shift 1 k ∧ SiteU (2 ^ 41) k ∧ SiteW 1 (5120 * BC * BW) (2 ^ 40) k := by
  decide +kernel
theorem d_of :
    ∀ k ≤ 24,
      SiteU (2 ^ 41) k → SiteW 1 (16384 * 2 ^ 12 * Bu * BW) (2 ^ 40) k → 10 ≤ k ∧ k ≤ 19 := by
  decide +kernel
theorem d_to :
    ∀ k ≤ 19,
      10 ≤ k → Shift 1 k ∧ SiteU (2 ^ 41) k ∧ SiteW 1 (16384 * 2 ^ 12 * Bu * BW) (2 ^ 40) k := by
  decide +kernel
theorem g_to :
    ∀ k ≤ 24,
      1 ≤ k → Shift 1 k ∧ SiteU (2 * (2 ^ 22 + 128) + 1) k ∧ SiteW 1 acc (2 ^ 22 + 128) k := by
  decide +kernel
theorem u_to : ∀ k ≤ 24, 1 ≤ k → Shift 1 k ∧ SiteU (2 ^ 16) k ∧ SiteW 1 acc (2 ^ 15) k := by
  decide +kernel
theorem r_of :
    ∀ k ≤ 24, (acc + 2 ^ (k - 1)) / 2 ^ (k + 3) + 1 + 2 ^ 15 + 2 ^ 16 < 2 ^ 25 → 8 ≤ k := by
  decide +kernel
theorem r_to :
    ∀ k ≤ 24, 8 ≤ k →
      Shift 1 k ∧
      SiteU (16 * Ty2 + 15) k ∧
      SiteW 1 acc (8 * Ty2 + 7) k ∧
      (acc + 2 ^ (k - 1)) / 2 ^ (k + 3) + 1 + 2 ^ 15 + 2 ^ 16 < 2 ^ 25 := by decide +kernel
theorem n_to :
    ∀ M ≤ 47, ∀ K ≤ 32, 17 ≤ K → SiteU (2 ^ 16) K ∧ SiteW 2 (2 ^ M + 2 ^ 38) (2 ^ 15) K := by
  decide +kernel

end Scales

/-- What `LawfulW`, this library's rendering of the programs' tests, says: a list of ranges. -/
theorem lawfulW_iff (s : LayerScale) : LawfulW s ↔ Ranges s := by
  constructor
  · intro h
    exact
      { kq := ⟨qk_of _ h.rq.2 h.Wq, h.rq.2⟩
        kk := ⟨qk_of _ h.rk.2 h.Wk, h.rk.2⟩
        qk := h.qk
        kv := h.rv
        ko := ⟨h.ro.1, o_of _ h.ro.2 h.Uo⟩
        kg := h.rg
        kg' := h.rg'
        ku := h.ru
        ku' := h.ru'
        kd := d_of _ h.rd.2 h.Ud h.Wd
        kr := ⟨r_of _ h.rr.2 h.grc, h.rr.2⟩
        n1 := h.n1
        n2 := h.n2 }
  · intro h
    obtain ⟨q1, q2, q3⟩ := qk_to _ h.kq.2 h.kq.1
    obtain ⟨k1, k2, k3⟩ := qk_to _ h.kk.2 h.kk.1
    obtain ⟨v1, v2, v3⟩ := u_to _ h.kv.2 h.kv.1
    obtain ⟨o1, o2, o3⟩ := o_to _ h.ko.2 h.ko.1
    obtain ⟨g1, g2, g3⟩ := g_to _ h.kg.2 h.kg.1
    obtain ⟨g1', g2', g3'⟩ := g_to _ h.kg'.2 h.kg'.1
    obtain ⟨u1, u2, u3⟩ := u_to _ h.ku.2 h.ku.1
    obtain ⟨u1', u2', u3'⟩ := u_to _ h.ku'.2 h.ku'.1
    obtain ⟨d1, d2, d3⟩ := d_to _ h.kd.2 h.kd.1
    obtain ⟨r1, r2, r3, r4⟩ := r_to _ h.kr.2 h.kr.1
    obtain ⟨a1, a2⟩ := n_to _ h.n1.2.2.2.1 _ h.n1.2.2.2.2.2.1 h.n1.2.2.2.2.1
    obtain ⟨b1, b2⟩ := n_to _ h.n2.2.2.2.1 _ h.n2.2.2.2.2.2.1 h.n2.2.2.2.2.1
    exact { rq := q1, rk := k1, rv := v1, ro := o1, rg := g1, rg' := g1', ru := u1, ru' := u1',
            rd := d1, rr := r1, qk := h.qk, n1 := h.n1, n2 := h.n2, Ug := g2, Wg := g3, Ug' := g2',
            Wg' := g3', Uu := u2, Wu := u3, Uu' := u2', Wu' := u3', Un1 := a1, Wn1 := a2, Un2 := b1,
            Wn2 := b2, Ud := d2, Wd := d3, Uq := q2, Wq := q3, Uk := k2, Wk := k3, Uo := o2,
            Wo := o3, Uv := v2, Wv := v3, Ur := r2, Wr := r3, grc := r4 }

instance (s : LayerScale) : Decidable (LawfulW s) := decidable_of_iff _ (lawfulW_iff s).symm

theorem LawfulW.ranges {s : LayerScale} (h : LawfulW s) : Ranges s := (lawfulW_iff s).1 h

/-- The words of the four layers of a segment are lawful (`LawfulW`). -/
def LawfulFF (κ : ℕ → LayerScale) : Prop := ∀ l < 4, LawfulW (κ l)

instance (κ : ℕ → LayerScale) : Decidable (LawfulFF κ) := by unfold LawfulFF; infer_instance

/-- the reference words (`ppref.scale`) are lawful -/
theorem lawfulW_ref : LawfulW ppref.scale := by decide +kernel

/-! ## The no-overflow conditions of the proofs, from the ranges -/

namespace Scales

theorem wq_int {k : ℕ} (h1 : 5 ≤ k) (h2 : k ≤ 32) :
    (2 : ℤ) ^ Site.dn k * (2 ^ 13 * ((5120 : ℤ) * (2047 * 2 ^ 12)) + 2 ^ (k - 1) + 2 ^ k * 2 ^ 15) +
        2 ^ 16 * (257 * 2 ^ 18 + 32896) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  interval_cases k <;> norm_num [Site.dn]

theorem wv_int {k : ℕ} (h2 : k ≤ 24) :
    (2 : ℤ) ^ Site.dn k * ((5120 : ℤ) * (2047 * 2 ^ 12) + 2 ^ (k - 1) + 2 ^ k * 2 ^ 15) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  interval_cases k <;> norm_num [Site.dn]

theorem wo_int {k : ℕ} (h2 : k ≤ 19) :
    (2 : ℤ) ^ Site.dn k * ((5120 : ℤ) * (2047 * 2 ^ 12) + 2 ^ (k - 1) + 2 ^ k * 2 ^ 40) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  interval_cases k <;> norm_num [Site.dn]

theorem wd_int {k : ℕ} (h1 : 10 ≤ k) (h2 : k ≤ 19) :
    (2 : ℤ) ^ Site.dn k * ((16384 : ℤ) * (4095 * 2 ^ 15 * 2 ^ 12) + 2 ^ (k - 1) + 2 ^ k * 2 ^ 40) +
        2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ 2 ^ 61 - 1 := by
  interval_cases k <;> norm_num [Site.dn]

theorem led_K {np : NormPar} (h : np.OK) : Ledger.Adm (2 ^ 61 - 1) np 5120 (2 ^ 18) :=
  ⟨h.1, h.2.1, h.2.2.2.1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Scales

/-! ## The class -/

/-- The words of every layer of the table in scope are lawful (`LawfulW`). -/
class Lawful [scl : Scl] : Prop where
  all : ∀ l, LawfulW (Scl.κ l)

/-- the reference table (`Scl.ref`) is lawful -/
instance : Lawful (scl := Scl.ref) := Lawful.mk (scl := Scl.ref) fun _ => lawfulW_ref

end Inst.Model.FFSeg
