-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/ShapeOwnAgrees.lean: the yardstick for ShapeOwn.lean: its functions give
what the verifier program's functions of the same office give, at every argument. Theorems alone.

Main names: `bitsFor_eq`, `fallingOrder_eq`, `planesOk_eq`, `planeColsOwn_eq`, `phiBOwn_eq`,
`pubLoopOwn_eq`, `pubRunOwn_eq`.

Limits: `shapeOwn` against `Forest.shape` and `pubOk` against `Forest.pubAsk` are not here. A
refusal's name is dropped: the program's answer is read as an option or as a Bool. No file of the
description imports this one.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.ShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

theorem bitsFor_eq (n : Nat) : bitsFor n = clog2 n := rfl

theorem fallingOrder_eq (count : Nat) (key : Nat → Nat) :
    fallingOrder count key = byFallingKey count key := rfl

theorem planesOk_eq (h : Forest.Shape) (lm : Nat) :
    planesOk h lm = (Forest.planeCols h lm).toBool := by
  unfold planesOk Forest.planeCols
  by_cases h1 : lm < 5
  · have : ¬ 5 ≤ lm := by omega
    simp [h1, this, Except.toBool, throw, throwThe, MonadExceptOf.throw]
  · by_cases h2 : lm > h.kT + 5
    · have : ¬ lm ≤ h.kT + 5 := by omega
      simp [h1, h2, this, Except.toBool, throw, throwThe, MonadExceptOf.throw]
    · have a : 5 ≤ lm := by omega
      have b : lm ≤ h.kT + 5 := by omega
      simp [h1, h2, a, b, Except.toBool, pure, Except.pure]

theorem planeColsOwn_eq (h : Forest.Shape) (lm : Nat) :
    planeColsOwn h lm = (Forest.planeCols h lm).toOption := by
  unfold planeColsOwn planesOk Forest.planeCols
  by_cases h1 : lm < 5
  · have : ¬ 5 ≤ lm := by omega
    simp [h1, this, Except.toOption, throw, throwThe, MonadExceptOf.throw]
  · by_cases h2 : lm > h.kT + 5
    · have : ¬ lm ≤ h.kT + 5 := by omega
      simp [h1, h2, this, Except.toOption, throw, throwThe, MonadExceptOf.throw]
    · have a : 5 ≤ lm := by omega
      have b : lm ≤ h.kT + 5 := by omega
      simp [h1, h2, a, b, Except.toOption, pure, Except.pure]

theorem phiBOwn_eq (g : Forest.Heard) (lm e : Nat) : phiBOwn g lm e = Forest.phiB g lm e := by
  unfold phiBOwn Forest.phiB
  simp only [planesOk_eq]

theorem pubLoopOwn_eq (dT base : Nat) : ∀ (steps : Nat) (pub : Array Nat) (first count : Nat),
    pubLoopOwn dT base steps pub first count = Forest.pubLoop dT base steps pub first count
  | 0, _, _, _ => rfl
  | s + 1, pub, first, count => by
    by_cases h : count = 0
    · simp [pubLoopOwn, Forest.pubLoop, h]
    · simp [pubLoopOwn, Forest.pubLoop, h, pubLoopOwn_eq dT base s]

theorem pubRunOwn_eq (h : Forest.Shape) (pub : Array Nat) (c first count : Nat) :
    pubRunOwn h pub c first count = (Forest.pubRun h pub c first count).toOption := by
  unfold pubRunOwn Forest.pubRun
  dsimp only
  cases h1 : (pub.size != h.NT || decide (c ≥ h.iota.size))
  · cases h2 : (decide (first > 2 ^ (h.dT + h.iota.getD c 0)) ||
        decide (count > 2 ^ (h.dT + h.iota.getD c 0) - first))
    · simp only [Bool.false_eq_true, ↓reduceIte, pubLoopOwn_eq]
      try rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      try rfl
  · simp only [↓reduceIte]
    try rfl

end VerifiableInference.Desc.First.Look
