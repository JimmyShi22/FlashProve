-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFCellLed.lean: the ledger of a normalisation and the stream, as affine forms in cells (over
the algebra of Cm/SegAlg.lean, Cm/SegPilotKit.lean): a mirror of Inst/Model/Common/Ledger.lean, row
by row.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

A ledger (Inst/Model/Common/Ledger.lean) is the function D from the number of a byte to its value;
its rows are numbers read off some of the bytes. Cm/SegFFCellIdn.lean and Cm/SegFFCellKeys.lean
import this file.

Main names:
  `LF.b256`, `LF.Vlo`, .., `LF.rq`: the rows of the ledger, for a ledger D whose bytes are forms;
    LF.val_..: the value of each at the matrices A is the row, in Inst/Model/Common/Ledger.lean, of
    the ledger of the values.
  LF.allPl_..: all places of a row have a property that all places of the 99 bytes have
    (`LF.allPl_b256`: for a + n ≤ 99; `LF.allPl_cs`: for s ≤ 9).
  `cLed g ν i`, `cXS g s j i`, `cBS g s l j i`: the ledger of the norm instance ν at position i,
    the stream at the place s (`FFSeg.streamAt`), and one of its five cells, of the feed-forward
    segment of group g; their values, and their places at indices in range.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegPilotKit
import Inst.Model.Common.Ledger

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset

namespace LF
variable {E : Type} [Field E] (D : ℕ → CForm E)

def b256 (a n : ℕ) : CForm E := cSum n fun l => ((256 : E) ^ l) • D (a + l)
def Vlo : CForm E := b256 D 0 6
def Vhi : CForm E := b256 D 6 4
def cs (s : ℕ) : CForm E :=
  if s = 0 then cK 0 else if s = 9 then D 9 else b256 D (10 + 6 * (s - 1)) 6 - cK (2 ^ 47)
def sa : CForm E := (2 : E) • D 58 + D 59 + ((2 : E) ^ 8) • D 60 + ((2 : E) ^ 16) • D 61
def s0 : CForm E := D 59
def sb : CForm E := D 62 + ((2 : E) ^ 8) • D 63
def sig : CForm E := sa D + ((2 : E) ^ 24) • sb D
def l1 : CForm E := b256 D 64 5
def h1 : CForm E := b256 D 69 5
def Blo : CForm E := b256 D 74 3
def Bhi : CForm E := b256 D 77 2
def kc : CForm E := D 79 - cK 4
def Rlo : CForm E := b256 D 80 3
def Rhi : CForm E := b256 D 83 3
def R : CForm E := Rlo D + ((2 : E) ^ 24) • Rhi D
def q1 : CForm E := b256 D 86 3
def rr : CForm E := b256 D 89 5
def rq : CForm E := b256 D 94 5

variable (A : ℕ → ℕ → ℕ → E)

@[simp] theorem val_b256 (a n : ℕ) :
    (b256 D a n).val A = Ledger.b256 (fun m => (D m).val A) a n := by
  simp [b256, Ledger.b256]
@[simp] theorem val_Vlo : (Vlo D).val A = Ledger.Vlo (fun m => (D m).val A) := by
  simp [Vlo, Ledger.Vlo]
@[simp] theorem val_Vhi : (Vhi D).val A = Ledger.Vhi (fun m => (D m).val A) := by
  simp [Vhi, Ledger.Vhi]
@[simp] theorem val_cs (s : ℕ) : (cs D s).val A = Ledger.cs (fun m => (D m).val A) s := by
  unfold cs Ledger.cs
  split_ifs <;> simp
@[simp] theorem val_sa : (sa D).val A = Ledger.sa (fun m => (D m).val A) := by simp [sa, Ledger.sa]
@[simp] theorem val_s0 : (s0 D).val A = Ledger.s0 (fun m => (D m).val A) := rfl
@[simp] theorem val_sb : (sb D).val A = Ledger.sb (fun m => (D m).val A) := by simp [sb, Ledger.sb]
@[simp] theorem val_sig : (sig D).val A = Ledger.sig (fun m => (D m).val A) := by
  simp [sig, Ledger.sig]
@[simp] theorem val_l1 : (l1 D).val A = Ledger.l1 (fun m => (D m).val A) := by simp [l1, Ledger.l1]
@[simp] theorem val_h1 : (h1 D).val A = Ledger.h1 (fun m => (D m).val A) := by simp [h1, Ledger.h1]
@[simp] theorem val_Blo : (Blo D).val A = Ledger.Blo (fun m => (D m).val A) := by
  simp [Blo, Ledger.Blo]
@[simp] theorem val_Bhi : (Bhi D).val A = Ledger.Bhi (fun m => (D m).val A) := by
  simp [Bhi, Ledger.Bhi]
@[simp] theorem val_kc : (kc D).val A = Ledger.kc (fun m => (D m).val A) := by simp [kc, Ledger.kc]
@[simp] theorem val_Rlo : (Rlo D).val A = Ledger.Rlo (fun m => (D m).val A) := by
  simp [Rlo, Ledger.Rlo]
@[simp] theorem val_Rhi : (Rhi D).val A = Ledger.Rhi (fun m => (D m).val A) := by
  simp [Rhi, Ledger.Rhi]
@[simp] theorem val_R : (R D).val A = Ledger.R (fun m => (D m).val A) := by simp [R, Ledger.R]
@[simp] theorem val_q1 : (q1 D).val A = Ledger.q1 (fun m => (D m).val A) := by simp [q1, Ledger.q1]
@[simp] theorem val_rr : (rr D).val A = Ledger.rr (fun m => (D m).val A) := by simp [rr, Ledger.rr]
@[simp] theorem val_rq : (rq D).val A = Ledger.rq (fun m => (D m).val A) := by simp [rq, Ledger.rq]

variable {D} {P : Cb.Place → Prop} (h : ∀ n < 99, AllPl P (D n))
include h

theorem allPl_b256 {a n : ℕ} (hb : a + n ≤ 99) : AllPl P (b256 D a n) :=
  AllPl.cSum fun l hl => AllPl.smul _ (h _ (by omega))
theorem allPl_Vlo : AllPl P (Vlo D) := allPl_b256 h (by norm_num)
theorem allPl_Vhi : AllPl P (Vhi D) := allPl_b256 h (by norm_num)
theorem allPl_cs {s : ℕ} (hs : s ≤ 9) : AllPl P (cs D s) :=
  AllPl.ite (fun _ => AllPl.cK _) fun _ =>
    AllPl.ite (fun _ => h 9 (by norm_num)) fun _ => AllPl.sub (allPl_b256 h (by omega)) (AllPl.cK _)
theorem allPl_sa : AllPl P (sa D) :=
  (((h 58 (by norm_num)).smul _).add (h 59 (by norm_num))).add ((h 60 (by norm_num)).smul _)
    |>.add ((h 61 (by norm_num)).smul _)
theorem allPl_s0 : AllPl P (s0 D) := h 59 (by norm_num)
theorem allPl_sb : AllPl P (sb D) := (h 62 (by norm_num)).add ((h 63 (by norm_num)).smul _)
theorem allPl_sig : AllPl P (sig D) := (allPl_sa h).add ((allPl_sb h).smul _)
theorem allPl_l1 : AllPl P (l1 D) := allPl_b256 h (by norm_num)
theorem allPl_h1 : AllPl P (h1 D) := allPl_b256 h (by norm_num)
theorem allPl_Blo : AllPl P (Blo D) := allPl_b256 h (by norm_num)
theorem allPl_Bhi : AllPl P (Bhi D) := allPl_b256 h (by norm_num)
theorem allPl_kc : AllPl P (kc D) := (h 79 (by norm_num)).sub (AllPl.cK _)
theorem allPl_Rlo : AllPl P (Rlo D) := allPl_b256 h (by norm_num)
theorem allPl_Rhi : AllPl P (Rhi D) := allPl_b256 h (by norm_num)
theorem allPl_R : AllPl P (R D) := (allPl_Rlo h).add ((allPl_Rhi h).smul _)
theorem allPl_q1 : AllPl P (q1 D) := allPl_b256 h (by norm_num)
theorem allPl_rr : AllPl P (rr D) := allPl_b256 h (by norm_num)
theorem allPl_rq : AllPl P (rq D) := allPl_b256 h (by norm_num)

end LF

section FF
variable {E : Type} [Field E] (g : ℕ)

/-- the ledger of the norm instance ν at position i -/
def cLed (ν i : ℕ) : ℕ → CForm E := fun n => cVal g .D ν n i
/-- the stream at the place s -/
def cXS (s j i : ℕ) : CForm E := cVal g (FFSeg.streamAt DF s).1 (FFSeg.streamAt DF s).2 j i
/-- cell l of the stream at the place s -/
def cBS (s l j i : ℕ) : CForm E :=
  cCell g ⟨(FFSeg.streamAt DF s).1, l, (FFSeg.streamAt DF s).2, j, i⟩

variable (A : ℕ → ℕ → ℕ → E)

theorem val_cLed (ν i : ℕ) :
    (fun m => (cLed g ν i m : CForm E).val A) = FFSeg.led (tA g A) ν i := by
  funext m
  simp [cLed, FFSeg.led]
@[simp] theorem val_cXS (s j i : ℕ) :
    (cXS g s j i : CForm E).val A = FFSeg.xS DF (tA g A) s j i := by
  simp [cXS, FFSeg.xS]
@[simp] theorem val_cBS (s l j i : ℕ) :
    (cBS g s l j i : CForm E).val A = FFSeg.bS DF (tA g A) s l j i := by
  simp [cBS, FFSeg.bS]

theorem inFF_cLed {ν i : ℕ} (hν : ν < DF.nNu) (hi : i < DF.T) :
    ∀ n < 99, InFF g (cLed g ν i n : CForm E) :=
  fun _ hn => inFF_cVal g hν hn hi

/-- for s ≤ 2 * `DF.nl`, the place s of the stream is held by an array of five cells and of the
width of the stream -/
theorem streamAt_ok {s : ℕ} (hs : s ≤ 2 * DF.nl) :
    (FFSeg.streamAt DF s).2 < (FFSeg.streamAt DF s).1.cnt DF ∧
    (FFSeg.streamAt DF s).1.width DF = DF.d ∧
    (FFSeg.streamAt DF s).1.nCell = 5 := by
  unfold FFSeg.streamAt
  split_ifs with h0 h8
  · exact ⟨Nat.one_pos, rfl, rfl⟩
  · exact ⟨Nat.one_pos, rfl, rfl⟩
  · refine ⟨?_, rfl, rfl⟩
    show s - 1 < 2 * DF.nl - 1
    omega

theorem inFF_cXS {s j i : ℕ} (hs : s ≤ 2 * DF.nl) (hj : j < DF.d) (hi : i < DF.T) :
    InFF g (cXS g s j i : CForm E) :=
  inFF_cVal g (streamAt_ok hs).1 ((streamAt_ok hs).2.1.symm ▸ hj) hi

theorem inFF_cBS {s l j i : ℕ} (hs : s ≤ 2 * DF.nl) (hl : l < 5) (hj : j < DF.d) (hi : i < DF.T) :
    InFF g (cBS g s l j i : CForm E) :=
  inFF_cCell g
    ⟨(streamAt_ok hs).2.2.symm ▸ hl, (streamAt_ok hs).1, (streamAt_ok hs).2.1.symm ▸ hj, hi⟩

end FF
end Cm.Seg
