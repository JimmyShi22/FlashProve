-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/WeightsOfRunIs.lean: the weights' tie of Reads/HeadFold.lean (the last clause of
`FoldFits`) from "the run's points and vectors are the kind's letters" (`RunIs`,
Johnson/Desc/Kinds/Law/TwelveOurs.lean).

What is shown is a step of the row at the head: it speaks of the kind's written declarations of its
five reads, against the arrays that the routine for the head's tables lays.
  `asksOfRun R ZV YN qFC qROW b0 b1`: the letters of Reads/HeadFold.lean's list of lines, at a run
    R: what was heard, and the two vectors of the positions with a cost, are the run's own.
  `weights_of_runIs`: for each of the five reads and every j below the run's length, the array of
    the read's line reads at j as the weight that the kind declares, under the library's reading.

How. The library of the kind's laws has that the verifier's table of equality weights reads entry
for entry as the kind's (`eqTab_reads`, `longPhi_cut`, Johnson/Desc/Kinds/Law/ReadsMeet.lean), and
that the run's two vectors read as the kind's weights at the positions with a cost (`cost_phi`,
`cost_rho`, Law/TwelveOurs.lean).

Premises. `RunIs R`; the run's shape has the kind's lt and ls, and la = ls + lt.

Limits. `RunIs` is a premise here: Reads/RunIsAt.lean has it at the seat, under named premises.
Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadFold
import Johnson.Desc.Kinds.Law.TwelveOurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading eqTab longPhi)
open OnBytes.Model.Head (Run costWeights ztOf)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- The letters of the list of lines, at a run. -/
def asksOfRun (R : Run) (ZV YN : Array E) (qFC qROW : ℕ) (b0 b1 : Array E) : HeadAsks :=
  { x := R.x, ZV := ZV, YN := YN
    phiC := (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1
    rhoCv := (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2
    qFC := qFC, qROW := qROW, b0 := b0, b1 := b1 }

section At
variable [Sizes] [Request] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [Heard]

/-- **The weights' tie, from RunIs.** S: any seat. -/
theorem weights_of_runIs (R : Run) (I : RunIs R) (hlt : R.h.lt = Norm.lt) (hls : R.h.ls = Norm.ls)
    (hla : R.h.la = Norm.ls + Norm.lt) (S : Seat) (ZV YN : Array E) (qFC qROW : ℕ)
    (b0 b1 : Array E) (r : Head.Read) (j : ℕ)
    (hj : j < (askOf (asksOfRun R ZV YN qFC qROW b0 b1) R.h r).2.2.1) :
    Reading.gl.val ((askOf (asksOfRun R ZV YN qFC qROW b0 b1) R.h r).2.2.2.1.getD j zeroE) =
      Reading.gl.val ((declOf S r).w j) := by
  have hT : R.h.T = Norm.T := by
    show 2 ^ R.h.lt = 2 ^ Norm.lt
    rw [hlt]
  have hTpos : 0 < Norm.T := Nat.two_pow_pos _
  have hZs : R.x.Zl.size = Norm.ls + Norm.lt := by
    rw [I.Zl, Array.size_append, I.szl, I.szt]
  have eZ1 : R.x.Zl.extract 0 Norm.ls = FinalNorm.zl := by
    rw [I.Zl, ← I.szl]
    exact Came.extract_left _ _
  have eZ2 : R.x.Zl.extract Norm.ls (Norm.ls + Norm.lt) = FinalNorm.zt := by
    rw [I.Zl, ← I.szl, ← I.szt]
    exact Came.extract_right _ _
  have hlong : ∀ {j : ℕ}, j < 2 ^ R.h.la → j / Norm.T < 2 ^ Norm.ls ∧ j % Norm.T < 2 ^ Norm.lt := by
    intro j hj
    rw [hla, Nat.pow_add] at hj
    exact ⟨Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj), Nat.mod_lt _ hTpos⟩
  cases r
  · -- wideAtKeys
    have hj' : j < 2 ^ R.h.la := hj
    obtain ⟨h1, h2⟩ := hlong hj'
    show rd ((longPhi R.x.Zl R.h.ls R.h.lt).getD j zeroE) =
      rd (eq FinalNorm.zl (j / Norm.T) * eq FinalNorm.zt (j % Norm.T))
    have e := Came.longPhi_cut R.x.Zl Norm.ls Norm.lt hZs h1 h2
    rw [eZ1, eZ2] at e
    have ej : j / Norm.T * 2 ^ Norm.lt + j % Norm.T = j := Nat.div_add_mod' j Norm.T
    rw [ej] at e
    rw [hls, hlt, e, rd_mul]
  · -- wideAtCosts
    have hj' : j < 2 ^ R.h.la := hj
    obtain ⟨-, h2⟩ := hlong hj'
    show rd (((Array.range (2 ^ R.h.la)).map fun i =>
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE).getD j zeroE) =
      rd ((1 : E) * phiC (j % Norm.T))
    have e : ((Array.range (2 ^ R.h.la)).map fun i =>
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE).getD j zeroE =
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (j % R.h.T) zeroE := by
      simp [Array.getD, hj']
    rw [e, hT, I.ztH, Came.cost_phi I.szt I.cov _ h2, rd_mul, rd_one, one_mul]
  · -- actAtLogits
    have hj' : j < Norm.T := by
      have h0 : j < R.h.T := hj
      rw [hT] at h0
      exact h0
    show rd ((eqTab R.x.tH.r).getD j zeroE) = rd (eq rH j)
    rw [I.tH]
    exact Came.eqTab_reads rH j (by rw [I.stH]; exact hj')
  · -- rowAtCosts
    have hj' : j < Norm.T := by
      have h0 : j < R.h.T := hj
      rw [hT] at h0
      exact h0
    show rd ((costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD j zeroE) = rd (phiC j)
    rw [I.ztH]
    exact Came.cost_phi I.szt I.cov j hj'
  · -- rowCount
    have hj' : j < Norm.T := by
      have h0 : j < R.h.T := hj
      rw [hT] at h0
      exact h0
    show rd ((costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2.getD j zeroE) =
      rd (if costed j then (1 : E) else 0)
    rw [I.ztH]
    exact Came.cost_rho I.szt I.cov j hj'

end At

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.weights_of_runIs
