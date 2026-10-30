-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/Bounds.lean: the bounds boundsW of the reduction's game
(Johnson/WholeKey/Wrap.lean): their sums, when they fit a budget of reads, and the game's error at
them. Lemmas and proofs. This file states no goal of the release.

boundsW h s1: M + 1 further encoded indices; one test, on the first; one link for each further one;
s1 sessions on each further one; no single read; one slot.
  sum_tests_boundsW, sum_links_boundsW   1 test and M + 1 links in all.
  fits_boundsW     they fit the budget b (BoundsR.Fits, Hiop/RecWhole.lean) under two inequalities:
                   qT + (M + 1) · qpar ≤ b for the first encoded index, qch + s1 · qon ≤ b for each
                   further one.
  errN_boundsW     the error with n sessions in all (errN, Hiop/Seeded/Total.lean) is
                   zT + (M + 1) · zL + n · zO.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Wrap
import Hiop.Seeded.Total

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open OnBytes.WholeKey Hiop Hiop.Seeded
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (h : HonestSide lam L Bd aT aL) (s1 : ℕ)

theorem sum_tests_boundsW : (boundsW h s1).sum (boundsW h s1).tests = 1 := by
  show ∑ j ∈ Finset.range (h.M + 1 + 1), (if j = 0 then 1 else 0) = 1
  rw [Finset.sum_range_succ']
  simp

theorem sum_links_boundsW : (boundsW h s1).sum (boundsW h s1).links = h.M + 1 := by
  show ∑ j ∈ Finset.range (h.M + 1 + 1), (if j = 0 then 0 else 1) = h.M + 1
  rw [Finset.sum_range_succ']
  simp

theorem fits_boundsW {b qT qpar qch qon : ℕ} (h0 : qT + (h.M + 1) * qpar ≤ b)
    (h1 : qch + s1 * qon ≤ b) : (boundsW h s1).Fits b qT qpar qch qon := by
  intro e _
  show (if e = 0 then 1 else 0) * qT +
      (if e = 0 then (boundsW h s1).sum (boundsW h s1).links * qpar else 0) +
      (if e = 0 then 0 else 1) * qch + (if e = 0 then 0 else s1) * qon + 0 ≤ b
  rw [sum_links_boundsW]
  by_cases he : e = 0
  · simp only [if_pos he]
    omega
  · simp only [if_neg he]
    omega

theorem errN_boundsW (n : ℕ) (zT zL zO : ℝ≥0∞) :
    errN (boundsW h s1) n zT zL zO = zT + ((h.M + 1 : ℕ) : ℝ≥0∞) * zL + n * zO := by
  unfold errN
  rw [sum_tests_boundsW, sum_links_boundsW]
  show ((1 : ℕ) : ℝ≥0∞) * zT + ((h.M + 1 : ℕ) : ℝ≥0∞) * zL + n * (((1 : ℕ) : ℝ≥0∞) * zO) = _
  rw [Nat.cast_one, one_mul, one_mul]

end OnBytes.WrapLaws

#print axioms OnBytes.WrapLaws.fits_boundsW
#print axioms OnBytes.WrapLaws.errN_boundsW
