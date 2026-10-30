-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6NoNs.lean: the cheap public test planK6V
(Johnson/Desc/Kinds/PlanK6Test.lean) WITHOUT THE EXACT NUMBER OF MASK ENTRIES IN USE. Theorems, and
Lean's kernel's evaluation at the written View of the full size.

Why. The View has a field ns: how many entries of the output head's segment's mask row are in use
(Wp.H.ns). No theorem gives that number's value in the goals' scope. The test reads of it only
whether so many entries fit the mask row, and that is monotone: what fits b entries fits fewer. The
IOP as written already tests "ns + answers ≤ the mask code's message length"
(Johnson/Desc/Ok/Links.lean: linkLaid, under linksFit). So the test is asked at an upper bound b in
ns's place, and Wp.H.ns ≤ b is a premise of its own.

What is proved.
  maskV_mono, copyV_mono, planK6V_mono   the test at ns := b implies the test at ns := a for a ≤ b.
  **planK6_of_bound**   Meaning.laidThere ..., Wp.H.ns ≤ b and planK6V { viewOf ... with ns := b } n
          rb = true imply the four clauses named, seats, maskNamed, maskIn of PlanK6
          (Law/K6Cut.lean).
  viewFull_bound        planK6V { viewFull with ns := 8192 } 145 0 = true. Lean's kernel evaluates
          it. 8192 is the mask code's message length at the full size.
  viewFull_bound_no     a negative test: at ns := 8193 it rejects.
  planK6_of_view_bound  whoever shows { viewOf ... with ns := 8192 } = { viewFull with ns := 8192 },
          Wp.H.ns ≤ 8192 and laidThere has the four clauses at n := 145, rb := 0.

No existential quantifier in these statements.
Not proved here. Wp.H.ns ≤ b. Meaning.laidThere. That the View of any arguments is the written one.
Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6ViewFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqLayout)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem namedOnce)

theorem maskV_mono {a b rb : ℕ} {y : MemV} (h : maskV b rb y = true) (hab : a ≤ b) :
    maskV a rb y = true := by
  unfold maskV at h ⊢
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with e | e
  · have : b = 0 := by simpa using e
    left
    have : a = 0 := by omega
    simp [this]
  · right
    exact lt_of_le_of_lt (Nat.div_le_div_right (by omega)) e

theorem copyV_mono {v : View} {k : ℕ} {ok ok' : MemV → Bool}
    (hok : ∀ y, ok y = true → ok' y = true) (h : copyV v k ok = true) : copyV v k ok' = true := by
  unfold copyV at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun y hy => ?_⟩
  have e := h.2 y hy
  rw [Bool.or_eq_true, Bool.and_eq_true] at e ⊢
  rcases e with e | e
  · exact Or.inl e
  · exact Or.inr ⟨e.1, hok y e.2⟩

/-- **What fits b entries fits fewer.** -/
theorem planK6V_mono {v : View} {a b n rb : ℕ} (h : planK6V { v with ns := b } n rb = true)
    (hab : a ≤ b) : planK6V { v with ns := a } n rb = true := by
  unfold planK6V at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.1.2⟩, copyV_mono (v := { v with ns := a }) (fun y hy => maskV_mono hy hab) h.2⟩

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- **The test at an upper bound in ns's place implies PlanK6's four clauses.** -/
theorem planK6_of_bound (n rb b : ℕ)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true) (hb : Wp.H.ns ≤ b)
    (h : planK6V { viewOf cs arr msR N Wp lay6 num with ns := b } n rb = true) :
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      InCopy cs arr (ms0 msR N) msR N 24 (seatLay Wp lay6 num 24 μ r c).1 false
        (seatLay Wp lay6 num 24 μ r c).2.1 (seatLay Wp lay6 num 24 μ r c).2.2) ∧
    (∀ j, j < Wp.H.ns → namedOnce arr N 24 (plAt n rb j).1 = true) ∧
    (∀ j, j < Wp.H.ns → InCopy cs arr (ms0 msR N) msR N 24 (plAt n rb j).1
      (plAt n rb j).2.1 (plAt n rb j).2.2.1 (plAt n rb j).2.2.2) := by
  refine planK6_of_C cs arr msR N Wp lay6 num n rb T ?_
  rw [planK6C_eq]
  exact planK6V_mono (v := viewOf cs arr msR N Wp lay6 num) h hb

end

/-- At the written View of the full size, with the mask code's message length in ns's place. Lean's
kernel evaluates it. -/
theorem viewFull_bound : planK6V { viewFull with ns := 8192 } 145 0 = true := by
  decide +kernel

/-- A negative test: one entry more does not fit. -/
theorem viewFull_bound_no : planK6V { viewFull with ns := 8193 } 145 0 = false := by
  decide +kernel

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- So: at arguments whose View is the written one but for ns. -/
theorem planK6_of_view_bound (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay6 = true)
    (hb : Wp.H.ns ≤ 8192)
    (hv : { viewOf cs arr msR N Wp lay6 num with ns := 8192 } = { viewFull with ns := 8192 }) :
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay6 num 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      InCopy cs arr (ms0 msR N) msR N 24 (seatLay Wp lay6 num 24 μ r c).1 false
        (seatLay Wp lay6 num 24 μ r c).2.1 (seatLay Wp lay6 num 24 μ r c).2.2) ∧
    (∀ j, j < Wp.H.ns → namedOnce arr N 24 (plAt 145 0 j).1 = true) ∧
    (∀ j, j < Wp.H.ns → InCopy cs arr (ms0 msR N) msR N 24 (plAt 145 0 j).1
      (plAt 145 0 j).2.1 (plAt 145 0 j).2.2.1 (plAt 145 0 j).2.2.2) :=
  planK6_of_bound cs arr msR N Wp lay6 num 145 0 8192 T hb (by rw [hv]; exact viewFull_bound)

end

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.maskV_mono
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.copyV_mono
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6V_mono
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_of_bound
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewFull_bound
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewFull_bound_no
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_of_view_bound
