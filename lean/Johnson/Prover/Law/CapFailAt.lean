-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/CapFailAt.lean: capFail (Johnson/Prover/Law/Defs.lean: the sum over the rounds of
the bound on a failed search) AS A CLOSED SUM over the written rounds' data, at the caps capAt
(Johnson/Prover/Law/CountFAt.lean: 2^(work + 6) tries), and a bound on each term.

Main names.
  failAt b   A DEFINITION: (1 - 2^-b)^(2^(b + 6)); 0 at b = 0.
  exp_neg_64, failAt_le   failAt b ≤ 2^-92, whatever b: by the library's Prob.one_sub_inv_pow_exp
    (CompileK/FailCapSharp.lean) and 92 · log 2 < 64.
  grFailAt_grOf, capFail_app, capFail_bare   steps.
  capFail_wiresSL, capFail_wiresLo, capFail_wiresSh   a stretch of written rounds.
  capFail_file, capFail_wqWhole, capFail_wqW   THE CLOSED SUMS.
  tested, sum_failAt_le   a sum of such terms is at most (the number of rounds with a test) · 2^-92.

Kin in the library. failBits cap64 (Compile/Batch/FitGrind.lean, Iop/GrindCap.lean): the like at
2^(b + 7) tries, a rule once planned for the programs; failBits_cap64_sharp
(CompileK/FailCapSharp.lean) bounds it by 2^-184.

Limits. Equations and a bound between numbers: that capFail bounds the chance that a search fails is
another file's (Johnson/Prover/Law/YesProved.lean). THE CAPS ARE OF OUR CHOOSING. 92 is the best
whole exponent for all b: the terms rise with b to exp (-64) = 2^-92.33 (by arithmetic, not by a
theorem).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.CountFAt
import CompileK.FailCapSharp

set_option autoImplicit false

open scoped ENNReal

namespace OnBytes.Prover
open _root_.Run _root_.Run.PQ Compile.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- One term of the closed sum, for a test of b bits: (1 - 2^-b)^(2^(b + 6)); 0 at b = 0. -/
noncomputable def failAt (b : ℕ) : ℝ≥0∞ :=
  if b = 0 then 0 else (1 - ((2 : ℝ≥0∞) ^ b)⁻¹) ^ 2 ^ (b + 6)

/-- exp (-64) ≤ 2^-92: exp_neg_128's text (CompileK/FailCapSharp.lean) at other numbers. -/
theorem exp_neg_64 : ENNReal.ofReal (Real.exp (-((64 : ℕ) : ℝ))) ≤ ((2 : ℝ≥0∞) ^ 92)⁻¹ := by
  have h1 : (2 : ℝ) ^ 92 ≤ Real.exp 64 := by
    have e : (2 : ℝ) ^ 92 = Real.exp (92 * Real.log 2) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]
      norm_cast
    rw [e]
    exact Real.exp_le_exp.2 (by have := Real.log_two_lt_d9; linarith)
  have h2 : Real.exp (-((64 : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ 92)⁻¹ := by
    rw [Real.exp_neg]
    push_cast
    exact inv_anti₀ (by positivity) h1
  have e2 : ((2 : ℝ≥0∞) ^ 92)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ 92)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [e2]
  exact ENNReal.ofReal_le_ofReal h2

/-- **One term is at most 2^-92.** -/
theorem failAt_le : ∀ b : ℕ, failAt b ≤ ((2 : ℝ≥0∞) ^ 92)⁻¹
  | 0 => zero_le _
  | b + 1 => by
    show (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ 2 ^ (b + 1 + 6) ≤ _
    have e : 2 ^ (b + 1 + 6) = 2 ^ (b + 1) * 64 := by
      rw [pow_add (2 : ℕ) (b + 1) 6]
      norm_num
    rw [e]
    have h := Prob.one_sub_inv_pow_exp (2 ^ (b + 1)) (by positivity) 64
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    exact h.trans exp_neg_64

theorem grFailAt_grOf {Cc P : Type} : ∀ b : ℕ,
    grFailAt (2 ^ (b + 6) - 1) ((grOf Dn Cc P b).map TypedOracleCompiler.Tagged.ofGr) = failAt b
  | 0 => rfl
  | b + 1 => by
    show (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ (2 ^ (b + 1 + 6) - 1 + 1) =
      (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ 2 ^ (b + 1 + 6)
    rw [Nat.sub_add_cancel Nat.one_le_two_pow]

theorem capFail_app {lam K : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B) (cap : ℕ → ℕ) (i : ℕ),
    capFail (s ++ u) (RoundSplits.app A B) (WireSB.app W V) cap i =
      capFail s A W cap i + capFail u B V cap (i + s.length)
  | [], _, _, _, _, _, _, _ => (zero_add _).symm
  | r :: s, u, (a, A), B, (w, W), V, cap, i => by
    show (match a.kind with
        | .lo => grFailAt (cap i) w.grJ
        | .sh => grFailAt (cap i) w.gr0) +
        capFail (s ++ u) (RoundSplits.app A B) (WireSB.app W V) cap (i + 1) =
      (match a.kind with
        | .lo => grFailAt (cap i) w.grJ
        | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1) +
        capFail u B V cap (i + (r :: s).length)
    rw [capFail_app W V cap (i + 1),
      show i + (r :: s).length = i + 1 + s.length by rw [List.length_cons]; omega]
    exact (add_assoc _ _ _).symm

/-- A bare round (Bare, Johnson/Prover/Law/CountFAt.lean) adds nothing. -/
theorem capFail_bare {lam K : ℕ} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (h : Bare w) (cap : ℕ → ℕ) (i : ℕ) :
    capFail (r :: s) (a, A) (w, W) cap i = capFail s A W cap (i + 1) := by
  show (match a.kind with
      | .lo => grFailAt (cap i) w.grJ
      | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1) = _
  rw [h.2.2.1, h.2.2.2]
  cases a.kind <;> exact zero_add _

section Wires
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (cap : ℕ → ℕ)

theorem capFail_wiresSL : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    capFail (TypedOracleCompiler.Run.PQ.uL C ds) (Twin.allLo (TypedOracleCompiler.Run.PQ.SL C ds))
      (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) cap i = (ds.map fun d => failAt d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show grFailAt (cap i) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map
        TypedOracleCompiler.Tagged.ofGr) +
        capFail _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) cap (i + 1) =
      failAt d.entry.work + (ds.map fun d => failAt d.entry.work).sum
    rw [capFail_wiresSL ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), h0, grFailAt_grOf]

theorem capFail_wiresLo : ∀ (ds : List RDT) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    capFail (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) cap i =
      (ds.map fun d => failAt d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show grFailAt (cap i) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map
        TypedOracleCompiler.Tagged.ofGr) + capFail _ _ (wiresLo C K chal ds) cap (i + 1) =
      failAt d.entry.work + (ds.map fun d => failAt d.entry.work).sum
    rw [capFail_wiresLo ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), h0, grFailAt_grOf]

theorem capFail_wiresSh : ∀ (ds : List RDT) (i : ℕ),
    (∀ j (h : j < ds.length), cap (i + j) = 2 ^ (ds[j].entry.work + 6) - 1) →
    capFail (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) cap i =
      (ds.map fun d => failAt d.entry.work).sum
  | [], _, _ => rfl
  | d :: ds, i, h => by
    have h0 : cap i = 2 ^ (d.entry.work + 6) - 1 := h 0 (Nat.succ_pos _)
    show grFailAt (cap i) ((grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map
        TypedOracleCompiler.Tagged.ofGr) + capFail _ _ (wiresSh C K chal ds) cap (i + 1) =
      failAt d.entry.work + (ds.map fun d => failAt d.entry.work).sum
    rw [capFail_wiresSh ds (i + 1) (fun j hj => by
        rw [show i + 1 + j = i + (j + 1) by omega]
        exact h (j + 1) (Nat.succ_lt_succ hj)), h0, grFailAt_grOf]

end Wires

/-- **Three stretches, each behind a bare round.** -/
theorem capFail_file {lam K : ℕ} {rF rJ r3 : Round} {s₁ s₂ s₃ : Shape} {aF : RAnn rF}
    {aJ : RAnn rJ} {a3 : RAnn r3} {A₁ : RoundSplits s₁} {A₂ : RoundSplits s₂} {A₃ : RoundSplits s₃}
    (wF : WireRB lam K rF aF) (wJ : WireRB lam K rJ aJ) (w3 : WireRB lam K r3 a3)
    (W₁ : RoundsQueryLayout lam K s₁ A₁) (W₂ : RoundsQueryLayout lam K s₂ A₂) (W₃ : RoundsQueryLayout lam K s₃ A₃)
    (hF : Bare wF) (hJ : Bare wJ) (h3 : Bare w3) (cap : ℕ → ℕ) :
    capFail (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃))) (aF, RoundSplits.app A₁ (aJ, RoundSplits.app A₂ (a3, A₃)))
      (wF, WireSB.app (u := rJ :: (s₂ ++ r3 :: s₃)) (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁
        (wJ, WireSB.app (u := r3 :: s₃) (B := (a3, A₃)) W₂ (w3, W₃))) cap 0 =
      capFail s₁ A₁ W₁ cap 1 + capFail s₂ A₂ W₂ cap (1 + s₁.length + 1) +
        capFail s₃ A₃ W₃ cap (1 + s₁.length + 1 + s₂.length + 1) := by
  rw [capFail_bare wF _ hF, capFail_app (u := rJ :: (s₂ ++ r3 :: s₃))
      (B := (aJ, RoundSplits.app A₂ (a3, A₃))) W₁, capFail_bare wJ _ hJ,
    capFail_app (u := r3 :: s₃) (B := (a3, A₃)) W₂, capFail_bare w3 _ h3]
  simp only [Nat.zero_add]
  exact (add_assoc _ _ _).symm

section Files
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **THE COPY's FILE.** -/
theorem capFail_wqW (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
    (dec : Y → View → Bool) :
    capFail (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh (capAt (workL ds)) 0 =
      (ds.map fun d => failAt d.entry.work).sum :=
  (capFail_bare (TypedOracleCompiler.Run.PQ.wire0S C K chal) (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
    ⟨rfl, rfl, rfl, rfl⟩ _ 0).trans
      (capFail_wiresSL C K chal _ ds (0 + 1) fun j h => by
        unfold capAt workL
        rw [show 0 + 1 + j = j + 1 by omega, List.getD_cons_succ, getD_map_at _ ds j h])

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A WHOLE FILE.** -/
theorem capFail_wqWhole :
    capFail (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh (capAt (Page.workAt D)) 0 =
      (D.ds₁.map fun d => failAt d.entry.work).sum +
        (D.ds₂.map fun d => failAt d.entry.work).sum +
        (D.ds₃.map fun d => failAt d.entry.work).sum := by
  have l₁ : (uLT C D.ds₁).length = D.ds₁.length := length_uLT C D.ds₁
  have l₂ : (uLT C D.ds₂).length = D.ds₂.length := length_uLT C D.ds₂
  refine (capFail_file (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _)
    (wireSilent (K + 1) T3 t3 _) (wiresLo C K chal D.ds₁) (wiresSh C K chal D.ds₂)
    (wiresLo C K chal D.ds₃) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩
    _).trans ?_
  rw [capFail_wiresLo C K chal _ D.ds₁ 1 (fun j h => by unfold capAt; rw [workAt_1 D j h]),
    capFail_wiresSh C K chal _ D.ds₂ _ (fun j h => by unfold capAt; rw [l₁, workAt_2 D j h]),
    capFail_wiresLo C K chal _ D.ds₃ _ (fun j h => by
      unfold capAt
      rw [l₁, l₂, workAt_3 D j h])]

end Files

/-- The number of entries that are not 0. -/
def tested (l : List ℕ) : ℕ := (l.map fun b => if b = 0 then 0 else 1).sum

/-- **A sum of such terms.** -/
theorem sum_failAt_le : ∀ l : List ℕ,
    (l.map failAt).sum ≤ (tested l : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 92)⁻¹
  | [] => by simp [tested]
  | b :: l => by
    have ih := sum_failAt_le l
    have e : tested (b :: l) = (if b = 0 then 0 else 1) + tested l := rfl
    rw [List.map_cons, List.sum_cons, e, Nat.cast_add, add_mul]
    refine add_le_add ?_ ih
    by_cases hb : b = 0
    · rw [hb]
      exact zero_le _
    · rw [if_neg hb, Nat.cast_one, one_mul]
      exact failAt_le b

end OnBytes.Prover

#print axioms OnBytes.Prover.exp_neg_64
#print axioms OnBytes.Prover.failAt_le
#print axioms OnBytes.Prover.grFailAt_grOf
#print axioms OnBytes.Prover.capFail_app
#print axioms OnBytes.Prover.capFail_bare
#print axioms OnBytes.Prover.capFail_wiresSL
#print axioms OnBytes.Prover.capFail_wiresLo
#print axioms OnBytes.Prover.capFail_wiresSh
#print axioms OnBytes.Prover.capFail_file
#print axioms OnBytes.Prover.capFail_wqW
#print axioms OnBytes.Prover.capFail_wqWhole
#print axioms OnBytes.Prover.sum_failAt_le
