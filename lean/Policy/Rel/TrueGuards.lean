-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/TrueGuards.lean

Guards on "true under a policy" (`IsTrueUnder`, Policy/Rel/True.lean): what it is at exact match,
that it is empty under no policy and not everything at the policies named below, and what it
comes to at the edges of the policy's three numbers (C, θ, cap). Each docstring tells its case.

A policy is looser than exact match if at some lawful table and index it admits a request that exact
match refuses. A request has its form if r < e ≤ 1,024, and y = 0 if e < 1,024 (`Head3`).

* The notion: `isTrueUnder_iff` (written out), `isTrueUnder_ofIndex`, `isTrueUnder_exact_iff` (at
  exact match it is `Cm.TrueAt`, Cm/RelBase.lean).
* For any logits: `polOK_low_clip`, `polOK_mono`. At every table: `none_true`, `idle`.
* At every lawful table (there is one: `lawful_sRef`, Cm/Rel2Guards.lean), at the all-zero weights:
  `some_true`, `zero_all`, `looser_refuses`, `two_replies`.

Limits: at the all-zero weights all logits are equal, at every position: a gap of 1 is a lost tie,
and which position's logits meet which token is not seen. At these weights every logit is 0 and
every gap is 0 or 1 (`lg_zero`, `gap_zero'`, Inst/Model/ProgramRGuards.lean);
Policy/Rel/PosGuards.lean has larger gaps.
-/
import Cm.RelTrue
import Cm.Rel2Proofs
import Inst.Model.RequestGuards2
import Policy.Rel.True

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open Inst.Model Inst.Model.ScalesSanity Inst.Model.ProgramRGuards Inst.Model.RequestGuards2

/-- "True under the policy", written out. -/
theorem isTrueUnder_iff (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) :
    IsTrueUnder s pol i x ↔
    RunsK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt ∧
    Head3 x ∧
    (∑ t ∈ x.cnt,
        min (costOf (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt) x t) pol.C ≤
      pol.theta * x.NB) ∧
    ((x.cnt.filter fun t =>
        (pol.C : ℤ) <
          costOf (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt) x t).card ≤
      pol.cap) ∧
    (x.e = ppref.T →
      gapOf ppref.V (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt (ppref.T - 1))
        x.y.val = 0) :=
  RinfR_written_out ppref s.kap s.nf (fun _ => tbRef) pol i.index x

/-- At the index that holds given weights, in the words of Inst/Model/ProgramR.lean. -/
theorem isTrueUnder_ofIndex (s : Cm.Scales) (pol : AcceptancePolicy) (j : Index ppref) (x : Instance ppref) :
    IsTrueUnder s pol (Cm.Idx.ofIndex j) x ↔
      RinfR ppref s.kap s.nf (fun _ => tbRef) pol j x := by
  unfold IsTrueUnder
  rw [Cm.index_ofIndex]
  exact Iff.rfl

/-- At exact match the notion is the true request of Cm/RelBase.lean. -/
theorem isTrueUnder_exact_iff (s : Cm.Scales) (i : Cm.Idx) (x : Instance ppref) :
    IsTrueUnder s AcceptancePolicy.exact i x ↔ Cm.TrueAt s.kap s.nf i x := by
  unfold IsTrueUnder
  rw [Cm.trueAt_iff]
  exact ((RinfS_iff_exact ppref (by decide) s.kap s.nf (fun _ => tbRef) i.index x).symm).trans
    (RinfS_iff ppref s.kap s.nf (fun _ => tbRef) i.index x)

namespace TrueGuards

/-- At one C, the policy's clauses are monotone in θ and in cap. -/
theorem polOK_mono {P : Params} {lg : ℕ → ℕ → ℤ} {pol pol' : AcceptancePolicy} {x : Instance P}
    (hC : pol'.C = pol.C) (hθ : pol.theta ≤ pol'.theta) (hcap : pol.cap ≤ pol'.cap)
    (h : PolOK lg pol x) : PolOK lg pol' x := by
  refine ⟨?_, ?_, h.c⟩
  · rw [hC]
    refine le_trans h.a ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hθ) (Int.natCast_nonneg _)
  · rw [hC]
    exact le_trans h.b hcap

/-- At C < 2^8 every counted position costs more than C: with NB the number of counted positions,
(a) is C NB ≤ θ NB, (b) is NB ≤ cap, and no logit of a counted position is read. -/
theorem polOK_low_clip {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)
    (hC : pol.C < 256) :
    PolOK lg pol x ↔ ((pol.C : ℤ) * x.NB ≤ pol.theta * x.NB ∧ x.NB ≤ pol.cap ∧
      (x.r < x.e → x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0)) := by
  have hc : ∀ t ∈ x.cnt, (pol.C : ℤ) < costOf lg x t := fun t _ => by
    unfold costOf
    have := gapOf_nonneg P.V (lg t) (x.w_lt t)
    have h : (pol.C : ℤ) < 256 := by exact_mod_cast hC
    omega
  have hs : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) = (pol.C : ℤ) * x.NB := by
    rw [Finset.sum_congr rfl fun t ht => min_eq_right (le_of_lt (hc t ht)), Finset.sum_const,
      x.card_cnt, nsmul_eq_mul, mul_comm]
  have hf : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t) = x.cnt :=
    Finset.filter_true_of_mem hc
  constructor
  · intro h
    exact ⟨hs ▸ h.a, by have := h.b; rwa [hf, x.card_cnt] at this, h.c⟩
  · rintro ⟨a, b, c⟩
    exact ⟨hs ▸ a, by rw [hf, x.card_cnt]; exact b, c⟩

/-- Under every policy some request is true, at every lawful table: all tokens 0, r = 1,023,
e = 1,024, y = 0, at the all-zero weights. It has no counted position. -/
theorem some_true {s : Cm.Scales} (hs : s.Lawful) (pol : AcceptancePolicy) :
    IsTrueUnder s pol (Cm.Idx.ofIndex iZero) (xz ⟨1023, by decide⟩ ⟨1024, by decide⟩) := by
  rw [isTrueUnder_ofIndex]
  have h := zero_range (pp := ppOf s AcceptancePolicy.exact) hs.toPP ⟨1023, by decide⟩ ⟨1024, by decide⟩
    (by decide)
  have hc : (xz ⟨1023, by decide⟩ ⟨1024, by decide⟩).cnt = ∅ := by decide
  exact ⟨h.1, h.2.1,
    (polOK_iff_of_noCnt _ pol _ hc).2 ((polOK_iff_of_noCnt _ AcceptancePolicy.exact _ hc).1 h.2.2)⟩

/-- At θ < 2^8 ≤ C no request with a counted position is true: every cost is at least 2^8. -/
theorem none_true (s : Cm.Scales) (pol : AcceptancePolicy) (h1 : pol.theta < 256) (h2 : 256 ≤ pol.C)
    (i : Cm.Idx) (x : Instance ppref) (hN : 0 < x.NB) : ¬ IsTrueUnder s pol i x := by
  intro h
  have ha := ((isTrueUnder_iff s pol i x).1 h).2.2.1
  have hm : ∀ t ∈ x.cnt, (256 : ℤ) ≤
      min (costOf (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt) x t)
        (pol.C : ℤ) := by
    intro t _
    refine le_min ?_ (by exact_mod_cast h2)
    unfold costOf
    have := gapOf_nonneg ppref.V
      (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt t) (x.w_lt t)
    omega
  have hs := Finset.card_nsmul_le_sum x.cnt _ (256 : ℤ) hm
  rw [x.card_cnt, nsmul_eq_mul] at hs
  have h3 : (pol.theta : ℤ) < 256 := by exact_mod_cast h1
  have h4 : (0 : ℤ) < x.NB := by exact_mod_cast hN
  nlinarith

/-- At C ≤ θ and 1,023 ≤ cap clauses (a) and (b) hold of every request: a request is true if and
only if the integer program runs, the request has its form, and y has gap 0 if e = 1,024. -/
theorem idle (s : Cm.Scales) (pol : AcceptancePolicy) (h1 : pol.C ≤ pol.theta) (h2 : 1023 ≤ pol.cap)
    (i : Cm.Idx) (x : Instance ppref) :
    IsTrueUnder s pol i x ↔
    RunsK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt ∧ Head3 x ∧
    (x.e = ppref.T →
      gapOf ppref.V (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt (ppref.T - 1))
        x.y.val = 0) := by
  rw [isTrueUnder_iff]
  constructor
  · rintro ⟨a, b, -, -, c⟩
    exact ⟨a, b, c⟩
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, ?_, ?_, c⟩
    · have := Finset.sum_le_card_nsmul x.cnt
        (fun t => min (costOf (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt) x t)
          (pol.C : ℤ)) (pol.theta : ℤ)
        (fun t _ => le_trans (min_le_right _ _) (by exact_mod_cast h1))
      rw [x.card_cnt, nsmul_eq_mul, mul_comm] at this
      exact this
    · refine le_trans (Finset.card_filter_le _ _) ?_
      rw [x.card_cnt]
      have : x.NB ≤ 1023 := by
        unfold Instance.NB
        show min x.e (1024 - 1) - x.r ≤ 1023
        omega
      exact le_trans this h2

/-- At 257 ≤ θ and 257 ≤ C, at the all-zero weights and every lawful table: every request that has
its form, with y = 0 if e = 1,024, is true, whatever its tokens: every cost is 2^8 or 2^8 + 1. -/
theorem zero_all {s : Cm.Scales} (hs : s.Lawful) (pol : AcceptancePolicy) (hθ : 257 ≤ pol.theta)
    (hC : 257 ≤ pol.C) (x : Instance ppref) (h3 : Head3 x) (hy : x.e = ppref.T → x.y.val = 0) :
    IsTrueUnder s pol (Cm.Idx.ofIndex iZero) x := by
  rw [isTrueUnder_ofIndex]
  refine ⟨runs_iZero (pp := ppOf s AcceptancePolicy.exact) hs.toPP x.prompt, h3, ⟨?_, ?_, fun _ he => ?_⟩⟩
  · have := Finset.sum_le_card_nsmul x.cnt
      (fun t => min (costOf (lgK ppref s.kap s.nf (fun _ => tbRef) iZero.val x.prompt) x t)
        (pol.C : ℤ)) (pol.theta : ℤ)
      (fun t _ => by
        refine le_trans (min_le_left _ _) ?_
        rw [cost_zero]
        have : (257 : ℤ) ≤ pol.theta := by exact_mod_cast hθ
        split <;> omega)
    rw [x.card_cnt, nsmul_eq_mul, mul_comm] at this
    exact this
  · rw [Finset.filter_false_of_mem]
    · exact Nat.zero_le _
    · intro t _
      rw [cost_zero]
      have : (257 : ℤ) ≤ (pol.C : ℤ) := by exact_mod_cast hC
      split <;> omega
  · rw [gap_zero' (lg_zero _ _ _ _ _) x.y.isLt, if_pos (hy he)]

/-- A policy that is looser than exact match refuses: at (2^8, 2^8, 1), at the all-zero weights and
every lawful table, the request `x1` (all tokens 1; 1,023 counted positions) is not true: more than
one of its counted positions costs more than the clip. `xOne`, with one such position, is true there
(`two_replies`) and not at exact match (`one_not_exact`, Inst/Model/ProgramRGuards.lean, on
`RinfR`). -/
theorem looser_refuses {s : Cm.Scales} (hs : s.Lawful) :
    ¬ IsTrueUnder s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) x1 := fun h => by
  have h1 := (isTrueUnder_ofIndex s _ iZero x1).1 h
  have h2 := ((rinfR_zero_iff (pp := ppOf s AcceptancePolicy.exact) hs.toPP 1 x1).1 h1).2.1
  have h3 : ({0, 1} : Finset ℕ) ⊆ miss x1 := by
    intro t ht
    have hc : t ∈ x1.cnt := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> (unfold Instance.cnt; decide)
    exact Finset.mem_filter.2 ⟨hc, by rw [x1_w hc]; norm_num⟩
  have h4 := Finset.card_le_card h3
  have h5 : ({0, 1} : Finset ℕ).card = 2 := by decide
  omega

/-- At (2^8, 2^8, 1), at the all-zero weights and every lawful table, the reply is no function of
what comes before it: two requests that agree in r, e and x_0 and differ in x_1 are both true. -/
theorem two_replies {s : Cm.Scales} (hs : s.Lawful) :
    (xOne.r = xAll.r ∧ xOne.e = xAll.e ∧ xOne.tok 0 = xAll.tok 0 ∧ xOne.tok 1 ≠ xAll.tok 1) ∧
    IsTrueUnder s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) xOne ∧
    IsTrueUnder s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) xAll := by
  have h1 := one_cap (pp := ppOf s AcceptancePolicy.exact) hs.toPP
  have h := (all_exact (pp := ppOf s AcceptancePolicy.exact) hs.toPP).1
  exact ⟨by decide, (isTrueUnder_ofIndex s _ iZero xOne).2 h1,
    (isTrueUnder_ofIndex s _ iZero xAll).2
      ⟨h.1, h.2.1, polOK_mono (pol := AcceptancePolicy.exact) (pol' := ⟨256, 256, 1⟩) rfl (le_refl _)
        (Nat.zero_le _) h.2.2⟩⟩

end TrueGuards

end Policy
