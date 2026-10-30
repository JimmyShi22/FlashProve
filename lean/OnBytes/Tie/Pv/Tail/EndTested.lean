-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndTested.lean: in a smallness test the verifier's state holds row weights. The
verifier tests them against a second computation (`HTailF2.tileSelfTestF`, OnBytes/Model/Tail.lean).
This file says what the success of that test tells about the weights, whoever has set them.
States.
 - `tileSelfTest_ok`: the test leaves state and context as they were, and `SelfTested tl F` holds:
   the record of what its tests on the weights say of the state F.
 - `tie_rowWeight`: in a symbol array's first virtual row, the weight of row R reads as
   theta ^ (Np * R), where Np is the second computation's power of two.
 - `pow2Again_eq`, `pow2Again_tau`: that power of two is the first computation's, up to 2^64.
Under. `tileSelfTest_ok`, two premises: (1) the run is not dry (`c.ch.dry = false`); (2) the test
returns. `tie_rowWeight`, four: (1) the Boolean `tieWeightsHeld` is true; (2) the array's number of
rows is at most `mS`, which `tie_R_le` proves from (1); (3) R is below that number of rows; (4) the
weight and theta are read in a commutative ring K through a map ρ that respects 0, 1, sums,
differences and products. `pow2Again_eq`, `pow2Again_tau`, one each: the number is at most 2^64.
Does not show.
 1. The test alone completes no equation.
 2. The chain takes a row's weights from the product form, not from the weights written out; a
    further test at run time links the two, and nothing is said of it here.

Notes in full, with every limit at length, stand at the end of this file.
-/
import OnBytes.Tie.Pv.Tail.EndClaimsB
import OnBytes.Slice.ProgCodes
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## The run of the test -/

theorem testAs_ok (name : String) (b : Bool) (c c' : Ctx) (u : Unit) (hd : c.ch.dry = false) :
    testAs name b c = .ok (u, c') ↔ b = true ∧ c' = c := by
  unfold testAs
  show (StateT.bind Blk.isDry _) c = .ok (u, c') ↔ _
  simp only [StateT.bind, Blk.isDry]
  show Except.bind (Except.ok (c.ch.dry, c)) _ = _ ↔ _
  simp only [Except.bind, hd, Bool.or_false]
  cases b with
  | true => simp [pure, StateT.pure, Except.pure, eq_comm]
  | false => simp [refuse, Blk.fail]

/-- What the self-test's success says. -/
structure SelfTested (tl : HTailF2) (F : Fork) : Prop where
  wants : ∃ nbW W, tl.wants = some (nbW, W) ∧
    (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 ∧
    (∀ mu, mu < tl.NM → tl.tieShapeHeld F mu = true) ∧
    (∀ u, u < tl.tau →
      ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u zeroE = powE F.theta u ∧
      ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.getD u zeroE = powE F.theta u) ∧
    (∀ mu, mu < tl.NM →
      tl.tieWeightsHeld F ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L mu = true) ∧
    tl.readShapeHeld ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
    tl.readWeightsHeld F ((F.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true

/-- If tileSelfTestF succeeds from the state F on a view that is not dry, it leaves state and
context as they were, and its tests on the ties' and the reads' weights were true of F. -/
theorem tileSelfTest_ok (tl : HTailF2) (F G : Fork) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : tl.tileSelfTestF F c = .ok (((), G), c')) : G = F ∧ c' = c ∧ SelfTested tl F := by
  unfold HTailF2.tileSelfTestF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq] at h
  obtain ⟨g, _, _, ⟨_, rfl, rfl⟩, jo, _, _, ⟨_, rfl, rfl⟩, w, _, _, ⟨hw, rfl, rfl⟩,
    _, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h5, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨h8, rfl⟩, h⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h8
  obtain ⟨_, rfl⟩ := h8
  obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨h10, rfl⟩, h⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h10
  obtain ⟨_, rfl⟩ := h10
  obtain ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h12, rfl⟩, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    _, _, _, ⟨h14, rfl⟩, h⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h14
  obtain ⟨h14, rfl⟩ := h14
  obtain ⟨_, _, _, ⟨rfl, rfl, rfl⟩, _, _, _, ⟨⟨h16, rfl⟩, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    h18, rfl⟩ := h
  rw [testAs_ok _ _ _ _ _ hd] at h18
  obtain ⟨h18, rfl⟩ := h18
  refine ⟨rfl, rfl, ⟨w.1, w.2, hw, ?_, ?_, ?_, ?_, h16, h18⟩⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at h5
    exact h5.1.1
  · intro mu hmu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h12
    exact h12.1.1.2 mu hmu
  · intro u hu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h14
    have := h14.1.1 u hu
    exact ⟨this.1, this.2.trans this.1⟩
  · intro mu hmu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h14
    exact h14.1.2 mu hmu

/-! ## Loops, and the second computation's powers -/

theorem allFrom_spec (p : Nat → Bool) : ∀ (count i : Nat), allFrom p count i = true →
    ∀ j, i ≤ j → j < i + count → p j = true := by
  intro count
  induction count with
  | zero => intro i _ j h1 h2; omega
  | succ n ih =>
    intro i h j h1 h2
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases e : j = i
    · subst e; exact h.1
    · exact ih (i + 1) h.2 j (by omega) (by omega)

/-- A test that holds of all numbers below n holds of each. -/
theorem allBelow_spec (n : Nat) (p : Nat → Bool) (h : allBelow n p = true) (j : Nat) (hj : j < n) :
    p j = true := allFrom_spec p n 0 h j (by omega) (by omega)

/-- powersAgain's entry R is theta^(np2 R). -/
theorem powersAgain_val (theta : E) (np2 count R : Nat) (h : R < count) :
    ρ.val ((HTailF2.powersAgain theta np2 count).getD R zeroE) = ρ.val theta ^ (np2 * R) := by
  unfold HTailF2.powersAgain
  simp only []
  rw [getD_map_range _ _ _ _ h, ρ.mul,
    getD_map_range _ _ _ _ (by omega : R / 128 < (count + 127) / 128),
    getD_map_range _ _ _ _ (by omega : R % 128 < 128), ρ.pow, ρ.pow, ← pow_add]
  congr 1
  have := Nat.div_add_mod R 128
  calc np2 * 128 * (R / 128) + np2 * (R % 128) = np2 * (128 * (R / 128) + R % 128) := by ring
    _ = np2 * R := by rw [this]

/-! ## The rows of a symbol array -/

/-- Where `tieWeightsHeld` is true and the array's number of rows is at most mS, the weight of a row
R below that number of rows reads as theta^(Np R), where Np is the second computation's power of
two. -/
theorem tie_rowWeight (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat)
    (h : tl.tieWeightsHeld F L5 mu = true) (hR : (tl.shp.getD mu {}).R ≤ (tl.shp.getD mu {}).mS)
    (R : Nat) (hlt : R < (tl.shp.getD mu {}).R) :
    ρ.val (((F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).coef.getD R zeroE)
      = ρ.val F.theta ^ (HTailF2.pow2Again tl.tau * R) := by
  simp only [HTailF2.tieWeightsHeld, Bool.and_eq_true] at h
  have h2 := allBelow_spec _ _ h.1.1.1.1.2 R hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  rw [h2.1, powersAgain_val ρ _ _ _ _ (by omega)]

/-- Beyond mS the second computation's vector reads zeroE, and the same conjunct refuses a weight
0. -/
theorem tie_R_le (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat)
    (h : tl.tieWeightsHeld F L5 mu = true) :
    (tl.shp.getD mu {}).R ≤ (tl.shp.getD mu {}).mS := by
  by_contra hlt
  simp only [HTailF2.tieWeightsHeld, Bool.and_eq_true] at h
  have h2 := allBelow_spec _ _ h.1.1.1.1.2 (tl.shp.getD mu {}).mS (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  have hz : (HTailF2.powersAgain F.theta (HTailF2.pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD
      (tl.shp.getD mu {}).mS zeroE = zeroE := by
    simp [HTailF2.powersAgain, Array.getD]
  obtain ⟨e, nz⟩ := h2
  rw [e, hz] at nz
  exact absurd nz (by decide)

/-! ## The second computation's power of two -/

theorem doubledTo_pow (x : Nat) : ∀ (fuel a : Nat), x ≤ 2 ^ (a + fuel) →
    HTailF2.doubledTo x fuel (2 ^ a) = 2 ^ max a (ceilLog2 x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a h
    have hc := Slice.ceilLog2_le x a (by simpa using h)
    simp only [HTailF2.doubledTo]
    rw [Nat.max_eq_left hc]
  | succ n ih =>
    intro a h
    simp only [HTailF2.doubledTo]
    by_cases hlt : 2 ^ a < x
    · have h1 : a + 1 ≤ ceilLog2 x := by
        by_contra hc
        have h2 : ceilLog2 x ≤ a := by omega
        have h3 := Slice.le_two_pow_ceilLog2 x
        have h4 : 2 ^ ceilLog2 x ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) h2
        omega
      rw [if_pos hlt, show 2 * 2 ^ a = 2 ^ (a + 1) by rw [Nat.pow_succ]; omega,
        ih (a + 1) (by rw [show a + 1 + n = a + (n + 1) by omega]; exact h),
        Nat.max_eq_right h1, Nat.max_eq_right (by omega)]
    · rw [if_neg hlt]
      have hc := Slice.ceilLog2_le x a (by omega)
      rw [Nat.max_eq_left hc]

/-- pow2Again is the first computation's 2 ^ clog2, up to 2^64. Beyond that it is false (a guard in
OnBytes/Model/TestTailCases.lean shows it). -/
theorem pow2Again_eq (x : Nat) (h : x ≤ 2 ^ 64) : HTailF2.pow2Again x = 2 ^ clog2 x := by
  have e := doubledTo_pow x 64 0 (by simpa using h)
  simpa [HTailF2.pow2Again] using e

/-- At the number of combinations it is the step between two rows' exponents. -/
theorem pow2Again_tau (tl : HTailF2) (h : tl.tau ≤ 2 ^ 64) :
    HTailF2.pow2Again tl.tau = tl.stepF :=
  pow2Again_eq _ h

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.tileSelfTest_ok
#print axioms OnBytes.Tie.Pv.Tail.Port.tie_rowWeight
#print axioms OnBytes.Tie.Pv.Tail.Port.pow2Again_tau

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Tie/Pv/Tail/EndTested.lean: what it says of the weights that the verifier's own test of them
(`HTailF2.tileSelfTestF`, OnBytes/Model/Tail.lean) has succeeded on a view.

Definitions, and theorems with their proofs. All three kinds of sub-proof call the test on the way
to a decision; on a view a failed test refuses. So on a run that succeeds the Boolean tests were
true, and from them row weights that were laid are read off in closed form, whoever has laid them.

Main names:
  `testAs_ok`: a named condition on values, in a run on a view.
  `SelfTested tl F`: what the test's success says of the state F. `tileSelfTest_ok`: the test leaves
    state and context as they were, and `SelfTested` holds.
  `allBelow_spec`, `powersAgain_val`: the second computation's loops and powers, read.
  `tie_rowWeight`: row R of a symbol array has the weight theta^(Np R). `tie_R_le`: its premise.
  `pow2Again_eq`, `pow2Again_tau`: the second computation's power of two is the first's, up to 2^64.

Limits: the test alone completes no equation. The chain takes a row's weights from the product form,
not from the weights written out; a further test at run time ties the two, and nothing is said of it
here.


-/
