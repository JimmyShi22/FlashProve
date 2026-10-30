-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesRounds.lean: counting the rounds of a protocol: all rounds, and the rounds with a
non-empty verifier message (the two numbers of rounds of a parameter list).

Definitions, statements and proofs. No protocol occurs here.
A round (Iop/Shape.lean) is a prover message followed by a verifier message; either may be empty.
"The verifier message is empty" is, in this library, "it has exactly one value" (Fintype.card r.Chal
= 1, as in Iop/BatchJoin.lean: `Err.UnitZero`). The errors below are the entries of a list ε
(`Err s`, Iop/Rbr.lean), a variable of each statement that speaks of them: that a protocol is sound
at such a list is no statement of this file.

Main names:
  `s.nAll`: the number of all rounds of the shape s (its length).
  `s.nVer`: the number of its rounds whose verifier message has more than one value.
  Both are additive under composition, and nothing is merged:
  `Spec.rounds_app`, `Spec.rounds_seq`: two shapes in a row; `R₁.seq R₂`.
  `Spec.rounds_hoist`: marked rounds sent in one first message (Ior/Hoist.lean), under `μ.OK`: nVer
    is kept (the marked rounds' verifier messages have one value, and so has the new first round's);
    nAll becomes 1 + the number of rounds that are not marked.
  A round with an empty verifier message has the error 0. This is a property of a list of errors
    (`Err.UnitZero`), not a theorem about every list: with one value, the count 1 says nothing.
  `Spec.unitZero_of_below`: a list all of whose errors are below 1, as fractions, has it.
  `ε.nPos`, `Spec.nPos_le_nVer`: so at most nVer entries of such a list are not 0.
  `ε.total`, `Spec.total_app`: the sum of the counts' fractions is not defined here; the sum of the
    counts of two lists in a row is the sum of the two sums.

Limits: this file says nothing on the numbers of any block of a protocol: none is named;
`Spec.rounds_seq` and `Spec.rounds_frame` are rules for every `IOR`. It says nothing on chain
queries of a compiler: whether it makes one query for each round counted by nVer is a matter of the
compiler.
The two numbers and "nothing is merged" restate a convention of this protocol's technical report
(lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Ior.Hoist
import Ior.Frame
import Iop.BatchJoin

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- All rounds. -/
def Shape.nAll (s : Shape) : ℕ := s.length

/-- The rounds with a non-empty verifier message. -/
def Shape.nVer : Shape → ℕ
  | [] => 0
  | r :: s => (if Fintype.card r.Chal = 1 then 0 else 1) + Shape.nVer s

/-- n times the same shape in a row. -/
def Shape.rep (s : Shape) : ℕ → Shape
  | 0 => []
  | n + 1 => s ++ Shape.rep s n

/-- How many entries of a list of errors are not 0. -/
def Err.nPos : {s : Shape} → Err s → ℕ
  | [], _ => 0
  | _ :: _, (e, ε) => (if e = 0 then 0 else 1) + Err.nPos ε

/-- The sum of the counts. -/
def Err.total : {s : Shape} → Err s → ℕ
  | [], _ => 0
  | _ :: _, (e, ε) => e + Err.total ε

/-- How many rounds are marked. -/
def Marks.nMarked : {s : Shape} → Marks s → ℕ
  | [], _ => 0
  | _ :: _, (none, μ) => Marks.nMarked μ
  | _ :: _, (some _, μ) => 1 + Marks.nMarked μ

namespace Spec
open IOR

def rounds_app : Prop :=
  ∀ s t : Shape, (s ++ t).nAll = s.nAll + t.nAll ∧ (s ++ t).nVer = s.nVer + t.nVer

def rounds_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    (R₁.seq R₂).shape.nAll = R₁.shape.nAll + R₂.shape.nAll ∧
    (R₁.seq R₂).shape.nVer = R₁.shape.nVer + R₂.shape.nVer

def rounds_frame : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo),
    (∀ Z : Type, (R.keepX Z).shape = R.shape) ∧
    (∀ F : ExtSpec, (R.keepE F).shape = R.shape) ∧
    (∀ (Xi' : Type) (Ei' : ExtSpec) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei),
      (R.pre f g).shape = R.shape) ∧
    (∀ (Xo' : Type) (Eo' : ExtSpec) (f : Xo → Option Xo') (g : ExtMap Eo Eo'),
      (R.post f g).shape = R.shape) ∧
    (∀ (f : Xi → Option Xo) (g : ExtMap Ei Eo),
      (IOR.pure f g).shape.nAll = 0 ∧ (IOR.pure f g).shape.nVer = 0)

def nVer_le : Prop := ∀ s : Shape, s.nVer ≤ s.nAll

def rounds_cons : Prop :=
  ∀ (r : Round) (s : Shape),
    Shape.nAll (r :: s) = 1 + s.nAll ∧
    (Fintype.card r.Chal = 1 → Shape.nVer (r :: s) = s.nVer) ∧
    (Fintype.card r.Chal ≠ 1 → Shape.nVer (r :: s) = 1 + s.nVer)

def rounds_replicate : Prop :=
  ∀ (s : Shape) (n : ℕ), (s.rep n).nAll = n * s.nAll ∧ (s.rep n).nVer = n * s.nVer

def rounds_hoist : Prop :=
  ∀ (s : Shape) (μ : Marks s), μ.OK → μ.shape.nVer = s.nVer ∧ μ.shape.nAll + μ.nMarked = 1 + s.nAll

def unitZero_app : Prop :=
  ∀ (s t : Shape) (ε : Err s) (ε' : Err t), (Err.app ε ε').UnitZero ↔ ε.UnitZero ∧ ε'.UnitZero

def unitZero_of_below : Prop := ∀ (s : Shape) (ε : Err s) (c : ℝ≥0∞), c < 1 → ε.Below c → ε.UnitZero

def nPos_le_nVer : Prop := ∀ (s : Shape) (ε : Err s), ε.UnitZero → ε.nPos ≤ s.nVer

def total_app : Prop :=
  ∀ (s t : Shape) (ε : Err s) (ε' : Err t),
    (Err.app ε ε').total = ε.total + ε'.total ∧ (Err.app ε ε').nPos = ε.nPos + ε'.nPos

end Spec

theorem rounds_app : Spec.rounds_app := by
  intro s t
  refine ⟨List.length_append, ?_⟩
  induction s with
  | nil => exact (Nat.zero_add _).symm
  | cons r s ih =>
      show _ + Shape.nVer (s ++ t) = (_ + Shape.nVer s) + Shape.nVer t
      rw [ih, Nat.add_assoc]

theorem rounds_seq : Spec.rounds_seq := fun _ _ _ _ _ _ R₁ R₂ => rounds_app R₁.shape R₂.shape

theorem rounds_frame : Spec.rounds_frame := fun _ _ _ _ _ =>
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem nVer_le : Spec.nVer_le := by
  intro s
  induction s with
  | nil => exact Nat.le_refl _
  | cons r s ih =>
      show (if Fintype.card r.Chal = 1 then 0 else 1) + Shape.nVer s ≤ s.length + 1
      have : (if Fintype.card r.Chal = 1 then 0 else 1) ≤ 1 := by split <;> omega
      have ih' : Shape.nVer s ≤ s.length := ih
      omega

theorem rounds_cons : Spec.rounds_cons := by
  intro r s
  refine ⟨by show s.length + 1 = 1 + s.length; omega, fun h => ?_, fun h => ?_⟩
  · show (if Fintype.card r.Chal = 1 then 0 else 1) + s.nVer = s.nVer
    rw [if_pos h, Nat.zero_add]
  · show (if Fintype.card r.Chal = 1 then 0 else 1) + s.nVer = 1 + s.nVer
    rw [if_neg h]

theorem rounds_replicate : Spec.rounds_replicate := by
  intro s n
  induction n with
  | zero => exact ⟨(Nat.zero_mul _).symm, (Nat.zero_mul _).symm⟩
  | succ n ih =>
      have h := rounds_app s (s.rep n)
      refine ⟨?_, ?_⟩
      · show (s ++ s.rep n).nAll = _
        rw [h.1, ih.1, Nat.succ_mul, Nat.add_comm]
      · show (s ++ s.rep n).nVer = _
        rw [h.2, ih.2, Nat.succ_mul, Nat.add_comm]

/-- The kept rounds: both numbers. -/
theorem Marks.rest_counts :
    ∀ {s : Shape} (μ : Marks s),
      μ.OK → μ.rest.nVer = Shape.nVer s ∧ μ.rest.nAll + μ.nMarked = Shape.nAll s
  | [], _, _ => ⟨rfl, rfl⟩
  | r :: s, (none, μ), h => by
      obtain ⟨h1, h2⟩ := Marks.rest_counts μ h
      refine ⟨?_, ?_⟩
      · show _ + μ.rest.nVer = _ + Shape.nVer s
        rw [h1]
      · show (μ.rest.length + 1) + μ.nMarked = s.length + 1
        have : μ.rest.length + μ.nMarked = s.length := h2
        omega
  | r :: s, (some u, μ), h => by
      obtain ⟨h1, h2⟩ := Marks.rest_counts μ h.2
      have hc : Fintype.card r.Chal = 1 := Fintype.card_eq_one_iff.2 ⟨u, h.1⟩
      refine ⟨?_, ?_⟩
      · show μ.rest.nVer = (if Fintype.card r.Chal = 1 then 0 else 1) + Shape.nVer s
        rw [if_pos hc, Nat.zero_add, h1]
      · show μ.rest.length + (1 + μ.nMarked) = s.length + 1
        have : μ.rest.length + μ.nMarked = s.length := h2
        omega

theorem rounds_hoist : Spec.rounds_hoist := by
  intro s μ h
  obtain ⟨h1, h2⟩ := Marks.rest_counts μ h
  refine ⟨?_, ?_⟩
  · show (if Fintype.card Unit = 1 then 0 else 1) + μ.rest.nVer = s.nVer
    rw [if_pos Fintype.card_unit, Nat.zero_add, h1]
  · show (μ.rest.length + 1) + μ.nMarked = 1 + s.length
    have : μ.rest.length + μ.nMarked = s.length := h2
    omega

theorem unitZero_app : Spec.unitZero_app := by
  intro s t ε ε'
  induction s with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons r s ih =>
      obtain ⟨e, ε⟩ := ε
      exact ⟨fun h => ⟨⟨h.1, ((ih ε).1 h.2).1⟩, ((ih ε).1 h.2).2⟩,
        fun h => ⟨h.1.1, (ih ε).2 ⟨h.1.2, h.2⟩⟩⟩

theorem unitZero_of_below : Spec.unitZero_of_below := by
  intro s ε c hc h
  induction s with
  | nil => trivial
  | cons r s ih =>
      obtain ⟨e, ε⟩ := ε
      refine ⟨fun h1 => ?_, ih ε h.2⟩
      have h2 : (e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) := h.1
      rw [h1, Nat.cast_one, mul_one] at h2
      have h3 : (e : ℝ≥0∞) < 1 := lt_of_le_of_lt h2 hc
      have h4 : e < 1 := by exact_mod_cast h3
      omega

theorem nPos_le_nVer : Spec.nPos_le_nVer := by
  intro s ε h
  induction s with
  | nil => exact Nat.le_refl _
  | cons r s ih =>
      obtain ⟨e, ε⟩ := ε
      have h2 := ih ε h.2
      show (if e = 0 then 0 else 1) + ε.nPos ≤
        (if Fintype.card r.Chal = 1 then 0 else 1) + Shape.nVer s
      by_cases hc : Fintype.card r.Chal = 1
      · rw [if_pos hc, if_pos (h.1 hc)]
        omega
      · rw [if_neg hc]
        have : (if e = 0 then 0 else 1) ≤ 1 := by split <;> omega
        omega

theorem total_app : Spec.total_app := by
  intro s t ε ε'
  induction s with
  | nil => exact ⟨(Nat.zero_add _).symm, (Nat.zero_add _).symm⟩
  | cons r s ih =>
      obtain ⟨e, ε⟩ := ε
      refine ⟨?_, ?_⟩
      · show e + (Err.app ε ε').total = (e + ε.total) + ε'.total
        rw [(ih ε).1, Nat.add_assoc]
      · show _ + (Err.app ε ε').nPos = (_ + ε.nPos) + ε'.nPos
        rw [(ih ε).2, Nat.add_assoc]

end Iop
