-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyTowers.lean: the four proximity tests of a key file's three chains at full size,
each from its second stage on, as closed values of the data of a test, and that each is knowledge
sound under one condition on counts.

The stages are written out in numbers, each with its radius, as in Johnson/Top/H/KeyValues.lean.
The values are built with the makers of Johnson/Top/H/StageValues.lean; the form at which a test's
second stage begins is a letter: the first stage hands it on. The tests on numbers are proved by
evaluation. In the names, Rng: the proof of the ranges; Row: the folded row; Omg: Omega; Own: the
own test; a digit: the stage; a test's last step is counted as a stage, so the eighteen stages are
fourteen folds with their switches and four last steps. Definitions, statements and proofs.
Main names:
  `sRng1`, `eRng1` and so on: a stage and its radius.
  `fRng1` and so on: the sizes of a stage and the next fit (`CsFit`). `gRng1` and so on: the stage
    passes the two tests of Johnson/Top/H/StageJ.lean.
  `tRng2 bC bZ sl` and so on: the test from that stage on, at counts that the caller gives as
    functions of stage and radius.
  `cRng bC bZ` and so on: the one condition that is asked: `CountsAt` at the stages from the
    second on.
  `tRng2_hypK`, `tRng2_reads`, `tRng2_know` and so on: under it the conditions of all blocks hold;
    what locality asks holds; the test from its second stage on is knowledge sound.
Limits: the first stage of each test, which stands on a group of oracle messages, is not treated;
`sRng1`, `fRng1` and the like are written for whoever lays it. That these numbers are those of a
key file's plan is not proved here: they were read off a print of the planner's calls at the
example of full size, and the radii were reckoned outside Lean, in exact integers. The print was
made by evaluating this library's port of the planner at the three public files of the example set
prover/examples/target_full_f2, held as constants by the program that printed (name, size,
sha256):
  policy.txt (2,629 bytes) ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes) a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes) 1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
That program and the program that cut the numbers out of the print are not in this repository. The
condition on counts is not proved here; at every stage twice the radius is at least the stage's
distance (`keyFar`, Johnson/Top/H/KeyValues.lean).

-/
import Johnson.Top.H.StageValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Cb.Pv.Tower

/-- The condition on counts at one stage. -/
def Cnt (bC bZ : Sg → ℕ → ℕ) (s : Sg) (e : ℕ) : Prop := CountsAt s e (bC s e) (bZ s e)

theorem szd {s : Sg} {e : ℕ} (h : (sizedB s && inJB s e) = true) : s.Sized := by
  simp only [Bool.and_eq_true] at h
  exact sized_of h.1

theorem inj {s : Sg} {e : ℕ} (h : (sizedB s && inJB s e) = true) : InJ s e := by
  simp only [Bool.and_eq_true] at h
  exact inJ_of h.2

/-! ### the proof of the ranges: 4 stages -/

def sRng1 : Sg := ⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 0, 49⟩
def eRng1 : ℕ := 3131959
def sRng2 : Sg := ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩
def eRng2 : ℕ := 431022
def sRng3 : Sg := ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩
def eRng3 : ℕ := 114481
def sRng4 : Sg := ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩
def eRng4 : ℕ := 982125

theorem fRng1 : CsFit sRng1 sRng2 := by decide +kernel
theorem fRng2 : CsFit sRng2 sRng3 := by decide +kernel
theorem fRng3 : CsFit sRng3 sRng4 := by decide +kernel

theorem gRng1 : (sizedB sRng1 && inJB sRng1 eRng1) = true := by decide +kernel
theorem gRng2 : (sizedB sRng2 && inJB sRng2 eRng2) = true := by decide +kernel
theorem gRng3 : (sizedB sRng3 && inJB sRng3 eRng3) = true := by decide +kernel
theorem gRng4 : (sizedB sRng4 && inJB sRng4 eRng4) = true := by decide +kernel

/-- The proof of the ranges: the test from its stage 3 on. -/
noncomputable def tRng3 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRng3.cIn.J) :
    TowR (wholeJ (sRng3.par sRng3.Z.l) sl eRng3) (sRng3.par sRng3.Z.l).Cw.nat :=
  stepLast fRng3 sl eRng3 eRng4 (bC sRng3 eRng3) (bZ sRng3 eRng3)
    (lastAt fRng3 sl eRng3 eRng4 (bC sRng4 eRng4) (bZ sRng4 eRng4))

/-- The proof of the ranges: the test from its stage 2 on. -/
noncomputable def tRng2 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRng2.cIn.J) :
    TowR (wholeJ (sRng2.par sRng2.Z.l) sl eRng2) (sRng2.par sRng2.Z.l).Cw.nat :=
  stepMid fRng2 sl eRng2 eRng3 (bC sRng2 eRng2) (bZ sRng2 eRng2)
    (tRng3 bC bZ ((swOf fRng2 sl).D eRng2).sl')

/-- The condition on counts at the stages 2 to 4. -/
def cRng (bC bZ : Sg → ℕ → ℕ) : Prop :=
  Cnt bC bZ sRng2 eRng2 ∧
    Cnt bC bZ sRng3 eRng3 ∧
    Cnt bC bZ sRng4 eRng4

theorem tRng3_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cRng bC bZ) {St : Type}
    (sl : Slf GE St sRng3.cIn.J) : (tRng3 bC bZ sl).HypK :=
  stepLast_hypK fRng3 sl _ (szd gRng3) (szd gRng4) (inj gRng3) (inj gRng4) hc.2.1
    (lastAt_hypK fRng3 sl eRng3 (szd gRng4) (inj gRng4) hc.2.2)

theorem tRng3_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRng3.cIn.J) :
    (tRng3 bC bZ sl).Reads :=
  stepLast_reads fRng3 sl _ _ _ _ _ (szd gRng4) (lastAt_reads fRng3 sl _ _ _ _)

theorem tRng2_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cRng bC bZ) {St : Type}
    (sl : Slf GE St sRng2.cIn.J) : (tRng2 bC bZ sl).HypK :=
  stepMid_hypK fRng2 sl _ (szd gRng2) (szd gRng3) (inj gRng2) (inj gRng3) hc.1
    (tRng3_hypK bC bZ hc _)

theorem tRng2_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRng2.cIn.J) :
    (tRng2 bC bZ sl).Reads :=
  stepMid_reads fRng2 sl _ _ _ _ _ (szd gRng3) (tRng3_reads bC bZ _)

/-- The proof of the ranges, from its second stage on, is knowledge sound under the
condition on counts. -/
theorem tRng2_know (bC bZ : Sg → ℕ → ℕ) (hc : cRng bC bZ) {St : Type}
    (sl : Slf GE St sRng2.cIn.J) : (tRng2 bC bZ sl).toEnd.Know :=
  (tRng2 bC bZ sl).know (tRng2_hypK bC bZ hc sl)

/-! ### the folded row: 5 stages -/

def sRow1 : Sg := ⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 0, 7, 97⟩
def eRow1 : ℕ := 8342420
def sRow2 : Sg := ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩
def eRow2 : ℕ := 1519572
def sRow3 : Sg := ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩
def eRow3 : ℕ := 95065
def sRow4 : Sg := ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩
def eRow4 : ℕ := 5944
def sRow5 : Sg := ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩
def eRow5 : ℕ := 12184

theorem fRow1 : CsFit sRow1 sRow2 := by decide +kernel
theorem fRow2 : CsFit sRow2 sRow3 := by decide +kernel
theorem fRow3 : CsFit sRow3 sRow4 := by decide +kernel
theorem fRow4 : CsFit sRow4 sRow5 := by decide +kernel

theorem gRow1 : (sizedB sRow1 && inJB sRow1 eRow1) = true := by decide +kernel
theorem gRow2 : (sizedB sRow2 && inJB sRow2 eRow2) = true := by decide +kernel
theorem gRow3 : (sizedB sRow3 && inJB sRow3 eRow3) = true := by decide +kernel
theorem gRow4 : (sizedB sRow4 && inJB sRow4 eRow4) = true := by decide +kernel
theorem gRow5 : (sizedB sRow5 && inJB sRow5 eRow5) = true := by decide +kernel

/-- The folded row: the test from its stage 4 on. -/
noncomputable def tRow4 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow4.cIn.J) :
    TowR (wholeJ (sRow4.par sRow4.Z.l) sl eRow4) (sRow4.par sRow4.Z.l).Cw.nat :=
  stepLast fRow4 sl eRow4 eRow5 (bC sRow4 eRow4) (bZ sRow4 eRow4)
    (lastAt fRow4 sl eRow4 eRow5 (bC sRow5 eRow5) (bZ sRow5 eRow5))

/-- The folded row: the test from its stage 3 on. -/
noncomputable def tRow3 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow3.cIn.J) :
    TowR (wholeJ (sRow3.par sRow3.Z.l) sl eRow3) (sRow3.par sRow3.Z.l).Cw.nat :=
  stepMid fRow3 sl eRow3 eRow4 (bC sRow3 eRow3) (bZ sRow3 eRow3)
    (tRow4 bC bZ ((swOf fRow3 sl).D eRow3).sl')

/-- The folded row: the test from its stage 2 on. -/
noncomputable def tRow2 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow2.cIn.J) :
    TowR (wholeJ (sRow2.par sRow2.Z.l) sl eRow2) (sRow2.par sRow2.Z.l).Cw.nat :=
  stepMid fRow2 sl eRow2 eRow3 (bC sRow2 eRow2) (bZ sRow2 eRow2)
    (tRow3 bC bZ ((swOf fRow2 sl).D eRow2).sl')

/-- The condition on counts at the stages 2 to 5. -/
def cRow (bC bZ : Sg → ℕ → ℕ) : Prop :=
  Cnt bC bZ sRow2 eRow2 ∧
    Cnt bC bZ sRow3 eRow3 ∧
    Cnt bC bZ sRow4 eRow4 ∧
    Cnt bC bZ sRow5 eRow5

theorem tRow4_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cRow bC bZ) {St : Type}
    (sl : Slf GE St sRow4.cIn.J) : (tRow4 bC bZ sl).HypK :=
  stepLast_hypK fRow4 sl _ (szd gRow4) (szd gRow5) (inj gRow4) (inj gRow5) hc.2.2.1
    (lastAt_hypK fRow4 sl eRow4 (szd gRow5) (inj gRow5) hc.2.2.2)

theorem tRow4_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow4.cIn.J) :
    (tRow4 bC bZ sl).Reads :=
  stepLast_reads fRow4 sl _ _ _ _ _ (szd gRow5) (lastAt_reads fRow4 sl _ _ _ _)

theorem tRow3_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cRow bC bZ) {St : Type}
    (sl : Slf GE St sRow3.cIn.J) : (tRow3 bC bZ sl).HypK :=
  stepMid_hypK fRow3 sl _ (szd gRow3) (szd gRow4) (inj gRow3) (inj gRow4) hc.2.1
    (tRow4_hypK bC bZ hc _)

theorem tRow3_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow3.cIn.J) :
    (tRow3 bC bZ sl).Reads :=
  stepMid_reads fRow3 sl _ _ _ _ _ (szd gRow4) (tRow4_reads bC bZ _)

theorem tRow2_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cRow bC bZ) {St : Type}
    (sl : Slf GE St sRow2.cIn.J) : (tRow2 bC bZ sl).HypK :=
  stepMid_hypK fRow2 sl _ (szd gRow2) (szd gRow3) (inj gRow2) (inj gRow3) hc.1
    (tRow3_hypK bC bZ hc _)

theorem tRow2_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sRow2.cIn.J) :
    (tRow2 bC bZ sl).Reads :=
  stepMid_reads fRow2 sl _ _ _ _ _ (szd gRow3) (tRow3_reads bC bZ _)

/-- The folded row, from its second stage on, is knowledge sound under the
condition on counts. -/
theorem tRow2_know (bC bZ : Sg → ℕ → ℕ) (hc : cRow bC bZ) {St : Type}
    (sl : Slf GE St sRow2.cIn.J) : (tRow2 bC bZ sl).toEnd.Know :=
  (tRow2 bC bZ sl).know (tRow2_hypK bC bZ hc sl)

/-! ### Omega: 4 stages -/

def sOmg1 : Sg := ⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 0, 4, 49⟩
def eOmg1 : ℕ := 3138896
def sOmg2 : Sg := ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩
def eOmg2 : ℕ := 196275
def sOmg3 : Sg := ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩
def eOmg3 : ℕ := 12184
def sOmg4 : Sg := ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩
def eOmg4 : ℕ := 26851

theorem fOmg1 : CsFit sOmg1 sOmg2 := by decide +kernel
theorem fOmg2 : CsFit sOmg2 sOmg3 := by decide +kernel
theorem fOmg3 : CsFit sOmg3 sOmg4 := by decide +kernel

theorem gOmg1 : (sizedB sOmg1 && inJB sOmg1 eOmg1) = true := by decide +kernel
theorem gOmg2 : (sizedB sOmg2 && inJB sOmg2 eOmg2) = true := by decide +kernel
theorem gOmg3 : (sizedB sOmg3 && inJB sOmg3 eOmg3) = true := by decide +kernel
theorem gOmg4 : (sizedB sOmg4 && inJB sOmg4 eOmg4) = true := by decide +kernel

/-- Omega: the test from its stage 3 on. -/
noncomputable def tOmg3 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOmg3.cIn.J) :
    TowR (wholeJ (sOmg3.par sOmg3.Z.l) sl eOmg3) (sOmg3.par sOmg3.Z.l).Cw.nat :=
  stepLast fOmg3 sl eOmg3 eOmg4 (bC sOmg3 eOmg3) (bZ sOmg3 eOmg3)
    (lastAt fOmg3 sl eOmg3 eOmg4 (bC sOmg4 eOmg4) (bZ sOmg4 eOmg4))

/-- Omega: the test from its stage 2 on. -/
noncomputable def tOmg2 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOmg2.cIn.J) :
    TowR (wholeJ (sOmg2.par sOmg2.Z.l) sl eOmg2) (sOmg2.par sOmg2.Z.l).Cw.nat :=
  stepMid fOmg2 sl eOmg2 eOmg3 (bC sOmg2 eOmg2) (bZ sOmg2 eOmg2)
    (tOmg3 bC bZ ((swOf fOmg2 sl).D eOmg2).sl')

/-- The condition on counts at the stages 2 to 4. -/
def cOmg (bC bZ : Sg → ℕ → ℕ) : Prop :=
  Cnt bC bZ sOmg2 eOmg2 ∧
    Cnt bC bZ sOmg3 eOmg3 ∧
    Cnt bC bZ sOmg4 eOmg4

theorem tOmg3_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cOmg bC bZ) {St : Type}
    (sl : Slf GE St sOmg3.cIn.J) : (tOmg3 bC bZ sl).HypK :=
  stepLast_hypK fOmg3 sl _ (szd gOmg3) (szd gOmg4) (inj gOmg3) (inj gOmg4) hc.2.1
    (lastAt_hypK fOmg3 sl eOmg3 (szd gOmg4) (inj gOmg4) hc.2.2)

theorem tOmg3_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOmg3.cIn.J) :
    (tOmg3 bC bZ sl).Reads :=
  stepLast_reads fOmg3 sl _ _ _ _ _ (szd gOmg4) (lastAt_reads fOmg3 sl _ _ _ _)

theorem tOmg2_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cOmg bC bZ) {St : Type}
    (sl : Slf GE St sOmg2.cIn.J) : (tOmg2 bC bZ sl).HypK :=
  stepMid_hypK fOmg2 sl _ (szd gOmg2) (szd gOmg3) (inj gOmg2) (inj gOmg3) hc.1
    (tOmg3_hypK bC bZ hc _)

theorem tOmg2_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOmg2.cIn.J) :
    (tOmg2 bC bZ sl).Reads :=
  stepMid_reads fOmg2 sl _ _ _ _ _ (szd gOmg3) (tOmg3_reads bC bZ _)

/-- Omega, from its second stage on, is knowledge sound under the
condition on counts. -/
theorem tOmg2_know (bC bZ : Sg → ℕ → ℕ) (hc : cOmg bC bZ) {St : Type}
    (sl : Slf GE St sOmg2.cIn.J) : (tOmg2 bC bZ sl).toEnd.Know :=
  (tOmg2 bC bZ sl).know (tOmg2_hypK bC bZ hc sl)

/-! ### the own test: 5 stages -/

def sOwn1 : Sg := ⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 1, 4, 49⟩
def eOwn1 : ℕ := 3138896
def sOwn2 : Sg := ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩
def eOwn2 : ℕ := 196275
def sOwn3 : Sg := ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩
def eOwn3 : ℕ := 24460
def sOwn4 : Sg := ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩
def eOwn4 : ℕ := 6631
def sOwn5 : Sg := ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩
def eOwn5 : ℕ := 29702

theorem fOwn1 : CsFit sOwn1 sOwn2 := by decide +kernel
theorem fOwn2 : CsFit sOwn2 sOwn3 := by decide +kernel
theorem fOwn3 : CsFit sOwn3 sOwn4 := by decide +kernel
theorem fOwn4 : CsFit sOwn4 sOwn5 := by decide +kernel

theorem gOwn1 : (sizedB sOwn1 && inJB sOwn1 eOwn1) = true := by decide +kernel
theorem gOwn2 : (sizedB sOwn2 && inJB sOwn2 eOwn2) = true := by decide +kernel
theorem gOwn3 : (sizedB sOwn3 && inJB sOwn3 eOwn3) = true := by decide +kernel
theorem gOwn4 : (sizedB sOwn4 && inJB sOwn4 eOwn4) = true := by decide +kernel
theorem gOwn5 : (sizedB sOwn5 && inJB sOwn5 eOwn5) = true := by decide +kernel

/-- The own test: the test from its stage 4 on. -/
noncomputable def tOwn4 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn4.cIn.J) :
    TowR (wholeJ (sOwn4.par sOwn4.Z.l) sl eOwn4) (sOwn4.par sOwn4.Z.l).Cw.nat :=
  stepLast fOwn4 sl eOwn4 eOwn5 (bC sOwn4 eOwn4) (bZ sOwn4 eOwn4)
    (lastAt fOwn4 sl eOwn4 eOwn5 (bC sOwn5 eOwn5) (bZ sOwn5 eOwn5))

/-- The own test: the test from its stage 3 on. -/
noncomputable def tOwn3 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn3.cIn.J) :
    TowR (wholeJ (sOwn3.par sOwn3.Z.l) sl eOwn3) (sOwn3.par sOwn3.Z.l).Cw.nat :=
  stepMid fOwn3 sl eOwn3 eOwn4 (bC sOwn3 eOwn3) (bZ sOwn3 eOwn3)
    (tOwn4 bC bZ ((swOf fOwn3 sl).D eOwn3).sl')

/-- The own test: the test from its stage 2 on. -/
noncomputable def tOwn2 (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn2.cIn.J) :
    TowR (wholeJ (sOwn2.par sOwn2.Z.l) sl eOwn2) (sOwn2.par sOwn2.Z.l).Cw.nat :=
  stepMid fOwn2 sl eOwn2 eOwn3 (bC sOwn2 eOwn2) (bZ sOwn2 eOwn2)
    (tOwn3 bC bZ ((swOf fOwn2 sl).D eOwn2).sl')

/-- The condition on counts at the stages 2 to 5. -/
def cOwn (bC bZ : Sg → ℕ → ℕ) : Prop :=
  Cnt bC bZ sOwn2 eOwn2 ∧
    Cnt bC bZ sOwn3 eOwn3 ∧
    Cnt bC bZ sOwn4 eOwn4 ∧
    Cnt bC bZ sOwn5 eOwn5

theorem tOwn4_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cOwn bC bZ) {St : Type}
    (sl : Slf GE St sOwn4.cIn.J) : (tOwn4 bC bZ sl).HypK :=
  stepLast_hypK fOwn4 sl _ (szd gOwn4) (szd gOwn5) (inj gOwn4) (inj gOwn5) hc.2.2.1
    (lastAt_hypK fOwn4 sl eOwn4 (szd gOwn5) (inj gOwn5) hc.2.2.2)

theorem tOwn4_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn4.cIn.J) :
    (tOwn4 bC bZ sl).Reads :=
  stepLast_reads fOwn4 sl _ _ _ _ _ (szd gOwn5) (lastAt_reads fOwn4 sl _ _ _ _)

theorem tOwn3_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cOwn bC bZ) {St : Type}
    (sl : Slf GE St sOwn3.cIn.J) : (tOwn3 bC bZ sl).HypK :=
  stepMid_hypK fOwn3 sl _ (szd gOwn3) (szd gOwn4) (inj gOwn3) (inj gOwn4) hc.2.1
    (tOwn4_hypK bC bZ hc _)

theorem tOwn3_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn3.cIn.J) :
    (tOwn3 bC bZ sl).Reads :=
  stepMid_reads fOwn3 sl _ _ _ _ _ (szd gOwn4) (tOwn4_reads bC bZ _)

theorem tOwn2_hypK (bC bZ : Sg → ℕ → ℕ) (hc : cOwn bC bZ) {St : Type}
    (sl : Slf GE St sOwn2.cIn.J) : (tOwn2 bC bZ sl).HypK :=
  stepMid_hypK fOwn2 sl _ (szd gOwn2) (szd gOwn3) (inj gOwn2) (inj gOwn3) hc.1
    (tOwn3_hypK bC bZ hc _)

theorem tOwn2_reads (bC bZ : Sg → ℕ → ℕ) {St : Type} (sl : Slf GE St sOwn2.cIn.J) :
    (tOwn2 bC bZ sl).Reads :=
  stepMid_reads fOwn2 sl _ _ _ _ _ (szd gOwn3) (tOwn3_reads bC bZ _)

/-- The own test, from its second stage on, is knowledge sound under the
condition on counts. -/
theorem tOwn2_know (bC bZ : Sg → ℕ → ℕ) (hc : cOwn bC bZ) {St : Type}
    (sl : Slf GE St sOwn2.cIn.J) : (tOwn2 bC bZ sl).toEnd.Know :=
  (tOwn2 bC bZ sl).know (tOwn2_hypK bC bZ hc sl)

end Johnson.Top.H

#print axioms Johnson.Top.H.tRng2_know
#print axioms Johnson.Top.H.tRow2_know
#print axioms Johnson.Top.H.tOmg2_know
#print axioms Johnson.Top.H.tOwn2_know
