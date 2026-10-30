-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/Teeth.lean

A guard on "true under a policy" (`IsTrueUnder`, Policy/Rel/True.lean): a policy's own two clauses
can refuse a request at large numbers too. A policy is three numbers (C, θ, cap). Clause (a) bounds
the mean of the costs, each clipped at C, by θ; clause (b) lets at most cap counted positions cost
more than C. In the other guards of this folder a cost is at most 2^8 + 2,048
(Policy/Rel/PosGuards.lean), so none of them shows a refusal by (a) at 2^8 + 2,048 ≤ θ, or by (b) at
2^8 + 2,048 ≤ C.

Here the weights `wtsAB a b` are made up so that the logits are 2,047 a at token 1, -2,047 b at
token 0 and 0 elsewhere, for 0 ≤ a ≤ 4,095 and 0 ≤ b ≤ 4,096 (`Votes a b`). In the request `xz` of
1,024 tokens 0 (Inst/Model/RequestGuards2.lean) every position checks token 0, so every position
costs 2^8 + 2,047 (a + b): at most 16,767,233.

Main names:
* `lg_wtsAB`, `gap_zero`, `cost_xz`: the logits, the gap of token 0, the cost of a position.
* `xz_iff`: at these weights, for every policy, r and e: exactly when `xz` is true under the policy.
* `teeth_mean`, `teeth_count`, `passes`: (a) refuses it, (b) refuses it, the policy admits it.
* `teeth_in_range`: one index `iTeeth` (a = 4,095, b = 4,096) and one request `xTeeth`
  (r = 0, e = 1,023). The request is not true under any policy with θ < C and θ < 16,767,233, or
  with C < 16,767,233 and cap < 1,023. It is true under (16,767,233, 16,767,233, 0). So what refuses
  it is the three numbers, not its form, a failed range test or clause (c).
* `refused_iff`: these are all the policies under which `xTeeth` is not true at `iTeeth`.
* `teeth_in_range_witness`: the same for "has a witness modulo 2^64 - 2^32 + 1".

The policies that `teeth_in_range` leaves out. At C ≤ θ and 1,023 ≤ cap, (a) and (b) hold of
every request (`TrueGuards.idle`, Policy/Rel/TrueGuards.lean). For every other one
(16,767,233 ≤ θ < C; or C ≤ θ, 16,767,233 ≤ C and cap < 1,023) this file shows no request that (a)
or (b) refuses, and does not show that there is none.

Limits:
* The weights are made up. All 48 layers are zero and all tokens have one embedding, so the logits
  are the same at every position and for every prompt. The theorems show that (a) and (b) can
  refuse. They do not show that these clauses refuse anything at a trained model, or how often.
* Every refusal shown here is of the request `xz`, whose counted positions all have one cost: 2^8 +
  2,047 (a + b). It runs from 2^8 at a = b = 0, where every checked token is the first choice, to
  16,767,233 at `iTeeth`, where every checked token is the token of least logit. No request that
  checks the first choice at some positions and another token at others is shown refused here.
* At a policy in the range with θ < C, clause (a) refuses `xTeeth`; where (b) refuses it too, it
  does so together with (a). Clause (b) alone refuses `xTeeth` only at C ≤ θ. No theorem here shows
  (b) refusing a request that (a) admits at a policy with θ < C: a request with one cost at all
  counted positions cannot. Policy/Rel/TeethCount.lean shows it at the same weights, at a request
  with two costs (`cap_alone_decides`).
* The clauses are this library's definitions (`PolOK`, `costOf`, Inst/Model/ProgramR.lean): a cost
  is the gap plus 2^8. That they are what the programs test is no theorem: by that file's head it is
  a reading of a version of the programs other than the released one, at its step table (sh = 8),
  with an argument over the real numbers that no Lean file has. No other exponent than 8 is covered.
* The range is over all triples (C, θ, cap), whether or not they pass `PolTests`
  (Inst/Model/ProgTests.lean).
* A gap has the unit of the weights' own logits: whoever makes the weights sets it.
* All statements are at the reference scales (`Cm.sRef`, Cm/Rel2Guards.lean) alone.
* Nothing here speaks of a protocol, a prover or a verifier.

Terms: lean/GLOSSARY.md.

-/
import Policy.Rel.PosGuards
noncomputable section

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.Teeth

open Inst.Model Inst.Model.SanityRef Inst.Model.ProgramRGuards Inst.Model.RequestGuards2

/-! ## 1. The weights, their logits, the cost of a position -/

/-- The output matrix: every channel votes a for token 1, -b for token 0 and 0 for every other. -/
def headAB (a b : ℤ) : Mat := fun j ι =>
  if j < 5120 ∧ ι < 202048 then (if ι = 1 then a else if ι = 0 then -b else 0) else 0

/-- The weights: all layers zero, every token embedded as 2^20 in channel 0, the output matrix
`headAB a b`. -/
def wtsAB (a b : ℤ) : Weights := ⟨fun _ => zeroLayer, embOf (fun _ => 0), headAB a b⟩

/-- The range of the two votes: a and -b are two-byte weights (`Two`, Inst/Model/Program.lean), and
neither a nor b is negative. -/
structure Votes (a b : ℤ) : Prop where
  a0 : 0 ≤ a
  a1 : a ≤ 4095
  b0 : 0 ≤ b
  b1 : b ≤ 4096

/-- For a, b with `Votes` the weights are well-formed. -/
theorem wtsAB_wf {a b : ℤ} (h : Votes a b) : (wtsAB a b).WF ppref := by
  obtain ⟨a0, a1, b0, b1⟩ := h
  refine ⟨(wts_wf (fun _ => 0) (fun _ => 0)).1, (wts_wf (fun _ => 0) (fun _ => 0)).2.1,
    fun j ι => ?_⟩
  show if j < 5120 ∧ ι < 202048 then _ ≤ headAB a b j ι ∧ headAB a b j ι ≤ _ else headAB a b j ι = 0
  unfold headAB
  split_ifs
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by norm_num, by norm_num⟩
  · rfl

/-- The stream at the start: at every position the row with 2^20 in channel 0. -/
theorem X0_wtsAB (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) (pos : ℕ) (h : pos < ppref.T) :
    X ppref tbRef (wtsAB a b) prompt 0 pos = row 0 :=
  X0_wts (fun _ => 0) (fun _ => 0) prompt (fun _ => by norm_num) pos h

/-- No range condition fails, whatever a, b and the prompt. -/
theorem runs_wtsAB (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) :
    Runs ppref tbRef (wtsAB a b) prompt :=
  runs_zero ppref tbRef (embOf fun _ => 0) (headAB a b) prompt shifts_ref fun pos hpos => by
    have e : X ppref tbRef ⟨fun _ => zeroLayer, embOf fun _ => 0, headAB a b⟩ prompt 0 pos =
        row 0 := X0_wtsAB a b prompt pos hpos
    rw [e]
    exact ⟨ok_row (by norm_num), ok_row (by norm_num), ok_row (by norm_num)⟩

/-- The logits at every position, for every prompt: 2,047 a at token 1, -2,047 b at token 0, 0 at
every other token. -/
theorem lg_wtsAB (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) (pos : ℕ) (hpos : pos < ppref.T)
    {ι : ℕ} (hι : ι < 202048) :
    lg ppref tbRef (wtsAB a b) prompt pos ι =
      if ι = 1 then 2047 * a else if ι = 0 then -(2047 * b) else 0 := by
  have e : X ppref tbRef (wtsAB a b) prompt (2 * ppref.layers) pos = row 0 := by
    rw [show X ppref tbRef (wtsAB a b) prompt (2 * ppref.layers) =
        X ppref tbRef (wtsAB a b) prompt 0
        from X_zero ppref tbRef (embOf fun _ => 0) (headAB a b) prompt shifts_ref _]
    exact X0_wtsAB a b prompt pos hpos
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ Finset.range 5120, NORM.out npR 5120 (row 0) j * headAB a b j ι = _
  rw [Finset.sum_eq_single 0
        (fun j _ hj => by rw [out_row (by norm_num), if_neg hj, zero_mul])
        (fun h => absurd (Finset.mem_range.2 (by norm_num)) h),
    out_row (by norm_num), if_pos rfl]
  unfold headAB
  rw [if_pos ⟨by norm_num, hι⟩]
  split_ifs <;> ring

/-- Under such logits, for a, b with `Votes`, the gap of token 0 is 2,047 (a + b). No token is
below token 0, so no tie adds 1. At a = b = 0 the gap is 0. -/
theorem gap_zero {a b : ℤ} (h : Votes a b) {l : ℕ → ℤ}
    (hl : ∀ v < ppref.V, l v = if v = 1 then 2047 * a else if v = 0 then -(2047 * b) else 0) :
    gapOf ppref.V l 0 = 2047 * (a + b) := by
  obtain ⟨a0, -, b0, -⟩ := h
  have l0 : l 0 = -(2047 * b) := by
    rw [hl 0 (by decide), if_neg (by norm_num), if_pos rfl]
  have l1 : l 1 = 2047 * a := by rw [hl 1 (by decide), if_pos rfl]
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, e⟩ :=
      (maxTo_spec (fun v => l v - l 0 + if v < 0 then 1 else 0) (ppref.V - 1)).2
    unfold gapOf
    rw [← e]
    show l j - l 0 + (if j < 0 then 1 else 0) ≤ _
    have hV : 0 < ppref.V := by decide
    rw [if_neg (Nat.not_lt_zero j), l0, hl j (by omega)]
    split_ifs <;> omega
  · have := le_gapOf ppref.V l (w := 0) (v := 1) (by decide)
    rw [l1, l0, if_neg (by norm_num)] at this
    omega

/-- For a, b with `Votes`, every position of `xz` costs 2^8 + 2,047 (a + b), whatever r and e. -/
theorem cost_xz {a b : ℤ} (h : Votes a b) (rF eF : Fin (ppref.T + 1)) {t : ℕ} (ht : t < ppref.T) :
    costOf (lg ppref tbRef (wtsAB a b) (xz rF eF).prompt) (xz rF eF) t =
      2 ^ 8 + 2047 * (a + b) := by
  unfold costOf
  rw [xz_w, gap_zero h (fun v hv => lg_wtsAB a b _ t ht hv), add_comm]

/-! ## 2. True under a policy at these weights -/

/-- The index that holds the weights `wtsAB a b`, for a, b with `Votes`. -/
def idxAB {a b : ℤ} (h : Votes a b) : Cm.Idx := Cm.Idx.ofIndex ⟨wtsAB a b, wtsAB_wf h⟩

/-- The integer program at the reference scales runs on every prompt at the weights that `idxAB h`
holds. -/
theorem runsK_idxAB {a b : ℤ} (h : Votes a b) (prompt : Fin ppref.T → Fin ppref.V) :
    RunsK ppref Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) (idxAB h).index.val prompt := by
  unfold idxAB
  rw [Cm.index_ofIndex]
  show RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAB a b) prompt
  rw [kap_ref]
  exact Cm.runsK_ref _ _ (runs_wtsAB a b prompt)

/-- At the reference scales and these weights, under every policy: a request is true if and only if
it has its form and the policy's clauses hold of the logits that `lg_wtsAB` gives. -/
theorem true_iff {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) (x : Instance ppref) :
    IsTrueUnder Cm.sRef pol (idxAB h) x ↔
      Head3 x ∧ PolOK (lg ppref tbRef (wtsAB a b) x.prompt) pol x := by
  unfold idxAB
  rw [isTrueUnder_ofIndex]
  show (RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAB a b) x.prompt ∧ Head3 x ∧
      PolOK (lgK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAB a b) x.prompt) pol x) ↔ _
  rw [kap_ref, Cm.lgK_ref]
  exact ⟨fun h => h.2, fun h => ⟨Cm.runsK_ref _ _ (runs_wtsAB a b x.prompt), h⟩⟩

/-- A counted position is below 1,024. -/
theorem cnt_lt (x : Instance ppref) {t : ℕ} (ht : t ∈ x.cnt) : t < ppref.T := by
  have h1 := lt_of_lt_of_le (Finset.mem_Ico.1 ht).2 (min_le_right _ _)
  omega

/-- For any logits under which all counted positions have one cost k (the hypothesis `hk`), with NB
their number: (a) says that NB = 0 or min(k, C) ≤ θ; (b) says that NB ≤ cap if C < k; (c) is as it
stands in `PolOK`. -/
theorem polOK_const_iff {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (k : ℤ)
    (hk : ∀ t ∈ x.cnt, costOf lg x t = k) :
    PolOK lg pol x ↔
      (x.NB = 0 ∨ min k (pol.C : ℤ) ≤ pol.theta) ∧ ((pol.C : ℤ) < k → x.NB ≤ pol.cap) ∧
      (x.r < x.e → x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0) := by
  have hs : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) = (x.NB : ℤ) * min k (pol.C : ℤ) := by
    rw [Finset.sum_congr rfl fun t ht => by rw [hk t ht], Finset.sum_const, x.card_cnt,
      nsmul_eq_mul]
  have ha : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) ≤ pol.theta * x.NB ↔
      (x.NB = 0 ∨ min k (pol.C : ℤ) ≤ pol.theta) := by
    rw [hs, mul_comm (pol.theta : ℤ)]
    rcases Nat.eq_zero_or_pos x.NB with h0 | h0
    · simp [h0]
    · have h1 : (0 : ℤ) < x.NB := by exact_mod_cast h0
      rw [mul_le_mul_iff_right₀ h1]
      exact ⟨Or.inr, fun h => h.resolve_left (Nat.ne_of_gt h0)⟩
  have hb : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t).card ≤ pol.cap ↔
      ((pol.C : ℤ) < k → x.NB ≤ pol.cap) := by
    by_cases c : (pol.C : ℤ) < k
    · rw [Finset.filter_true_of_mem fun t ht => by rw [hk t ht]; exact c, x.card_cnt]
      exact ⟨fun h _ => h, fun h => h c⟩
    · rw [Finset.filter_false_of_mem fun t ht => by rw [hk t ht]; exact c]
      exact ⟨fun _ h => absurd h c, fun _ => Nat.zero_le _⟩
  exact ⟨fun h => ⟨ha.1 h.a, hb.1 h.b, h.c⟩, fun h => ⟨ha.2 h.1, hb.2 h.2.1, h.2.2⟩⟩

/-- For a, b with `Votes`, every policy, r and e, with k = 2^8 + 2,047 (a + b) and NB the number of
counted positions: `xz` is true under the policy if and only if r < e; NB = 0 or min(k, C) ≤ θ;
NB ≤ cap if C < k; and a + b = 0 if e = 1,024. The last clause is (c): y is token 0, which is the
first choice only at a = b = 0. -/
theorem xz_iff {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) (rF eF : Fin (ppref.T + 1)) :
    IsTrueUnder Cm.sRef pol (idxAB h) (xz rF eF) ↔
      rF.val < eF.val ∧
      ((xz rF eF).NB = 0 ∨ min (2 ^ 8 + 2047 * (a + b)) (pol.C : ℤ) ≤ pol.theta) ∧
      ((pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b) → (xz rF eF).NB ≤ pol.cap) ∧
      (eF.val = ppref.T → a + b = 0) := by
  rw [true_iff h, polOK_const_iff _ pol _ _ fun t ht => cost_xz h rF eF (cnt_lt _ ht)]
  have hg : gapOf ppref.V (lg ppref tbRef (wtsAB a b) (xz rF eF).prompt (ppref.T - 1))
      (xz rF eF).y.val = 2047 * (a + b) :=
    gap_zero h fun v hv => lg_wtsAB a b _ (ppref.T - 1) (by decide) hv
  rw [hg]
  constructor
  · rintro ⟨h3, h1, h2, hc⟩
    exact ⟨h3.1, h1, h2, fun e => by have := hc h3.1 e; omega⟩
  · rintro ⟨hre, h1, h2, hc⟩
    exact ⟨⟨hre, Nat.lt_succ_iff.1 eF.isLt, fun _ => rfl⟩, h1, h2,
      fun _ e => by have := hc e; rw [this]; norm_num⟩

/-- Clause (a) refuses. Hypotheses: a, b meet `Votes`, θ < C, θ is below the cost
2^8 + 2,047 (a + b) of a position, and a position is counted. Then `xz` is not true under the
policy. -/
theorem teeth_mean {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) (hC : pol.theta < pol.C)
    (hθ : (pol.theta : ℤ) < 2 ^ 8 + 2047 * (a + b)) (rF eF : Fin (ppref.T + 1))
    (hN : 0 < (xz rF eF).NB) :
    ¬ IsTrueUnder Cm.sRef pol (idxAB h) (xz rF eF) := fun hT => by
  have hC' : (pol.theta : ℤ) < (pol.C : ℤ) := by exact_mod_cast hC
  exact absurd (((xz_iff h pol rF eF).1 hT).2.1.resolve_left (Nat.ne_of_gt hN))
    (not_le.2 (lt_min hθ hC'))

/-- Clause (b) refuses. Hypotheses: a, b meet `Votes`, C is below the cost
2^8 + 2,047 (a + b) of a position, and more than cap positions are counted. Then `xz` is not true
under the policy. -/
theorem teeth_count {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy)
    (hC : (pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b)) (rF eF : Fin (ppref.T + 1))
    (hcap : pol.cap < (xz rF eF).NB) :
    ¬ IsTrueUnder Cm.sRef pol (idxAB h) (xz rF eF) := fun hT =>
  absurd (((xz_iff h pol rF eF).1 hT).2.2.1 hC) (not_le.2 hcap)

/-- The policy admits the same request. Hypotheses: a, b meet `Votes`, the cost
2^8 + 2,047 (a + b) of a position is at most θ, θ ≤ C, and r < e < 1,024. Then `xz` is true under
the policy, whatever cap is. -/
theorem passes {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy)
    (hθ : 2 ^ 8 + 2047 * (a + b) ≤ (pol.theta : ℤ)) (hC : pol.theta ≤ pol.C)
    (rF eF : Fin (ppref.T + 1)) (hre : rF.val < eF.val) (he : eF.val < ppref.T) :
    IsTrueUnder Cm.sRef pol (idxAB h) (xz rF eF) := by
  have hC' : (pol.theta : ℤ) ≤ (pol.C : ℤ) := by exact_mod_cast hC
  exact (xz_iff h pol rF eF).2 ⟨hre, Or.inr (min_le_of_left_le hθ),
    fun c => absurd c (not_lt.2 (le_trans hθ hC')), fun e => absurd e (Nat.ne_of_lt he)⟩

/-! ## 3. One index and one request for every policy in a range -/

/-- The index with the largest votes: a = 4,095, b = 4,096. -/
def iTeeth : Cm.Idx :=
  idxAB (a := 4095) (b := 4096) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- 1,024 tokens 0, y = 0, r = 0, e = 1,023: 1,023 counted positions; clause (c) asks nothing. -/
def xTeeth : Instance ppref := xz ⟨0, by decide⟩ ⟨1023, by decide⟩

/-- The cost of every position of `xTeeth` at `iTeeth`. -/
theorem cost_number : (2 : ℤ) ^ 8 + 2047 * (4095 + 4096) = 16767233 := by norm_num

theorem nb_xTeeth : xTeeth.NB = 1023 := by decide

/-- **Every policy in the range refuses one request that another policy admits.** The hypothesis
`h` is the range: θ < C and θ < 16,767,233, or C < 16,767,233 and cap < 1,023. Under such a policy
the request `xTeeth` is not true at the index `iTeeth`: in the first case by clause (a), in the
second by clause (b). Under the policy (C, θ, cap) = (16,767,233, 16,767,233, 0) it is true there.
Index and request do not depend on the policy. The weights are made up: see the limits at the top
of this file. -/
theorem teeth_in_range (pol : AcceptancePolicy)
    (h : (pol.theta < pol.C ∧ pol.theta < 16767233) ∨ (pol.C < 16767233 ∧ pol.cap < 1023)) :
    ¬ IsTrueUnder Cm.sRef pol iTeeth xTeeth ∧
      IsTrueUnder Cm.sRef ⟨16767233, 16767233, 0⟩ iTeeth xTeeth := by
  refine ⟨?_, passes _ _ (by norm_num) (le_refl _) _ _ (by decide) (by decide)⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine teeth_mean _ pol h1 ?_ _ _ (by decide)
    rw [cost_number]
    exact_mod_cast h2
  · refine teeth_count _ pol ?_ _ _ (by rw [show (xz _ _).NB = 1023 from nb_xTeeth]; exact h2)
    rw [cost_number]
    exact_mod_cast h1

/-- The range of `teeth_in_range` is all of it: `xTeeth` is true at `iTeeth` under every
policy outside the range. -/
theorem refused_iff (pol : AcceptancePolicy) :
    ¬ IsTrueUnder Cm.sRef pol iTeeth xTeeth ↔
      (pol.theta < pol.C ∧ pol.theta < 16767233) ∨ (pol.C < 16767233 ∧ pol.cap < 1023) := by
  refine ⟨fun hn => ?_, fun h => (teeth_in_range pol h).1⟩
  by_contra hr
  refine hn ((xz_iff _ pol _ _).2 ⟨by decide, ?_, ?_, fun e => absurd e (by decide)⟩)
  · rw [cost_number]
    right
    by_cases c : pol.theta < pol.C
    · exact min_le_of_left_le (by
        have : ¬ pol.theta < 16767233 := fun c' => hr (Or.inl ⟨c, c'⟩)
        exact_mod_cast not_lt.1 this)
    · exact min_le_of_right_le (by exact_mod_cast not_lt.1 c)
  · rw [cost_number, show (xz _ _).NB = 1023 from nb_xTeeth]
    intro hC
    have hC' : pol.C < 16767233 := by exact_mod_cast hC
    exact not_lt.1 fun c => hr (Or.inr ⟨hC', c⟩)

/-- The policy that admits `xTeeth` passes `PolTests` (Inst/Model/ProgTests.lean). -/
theorem polTests_lax : PolTests ⟨16767233, 16767233, 0⟩ := (polTests_iff _).2 (by decide)

/-- `teeth_in_range` for "has a witness modulo 2^64 - 2^32 + 1" (`LedgerGuards.HasWitness`,
Policy/Rel/LedgerGuards.lean), under the further hypothesis that the policy meets `PolCond`. -/
theorem teeth_in_range_witness (pol : AcceptancePolicy) (hpol : PolCond pol)
    (h : (pol.theta < pol.C ∧ pol.theta < 16767233) ∨ (pol.C < 16767233 ∧ pol.cap < 1023)) :
    ¬ LedgerGuards.HasWitness Cm.sRef pol iTeeth xTeeth ∧
      LedgerGuards.HasWitness Cm.sRef ⟨16767233, 16767233, 0⟩ iTeeth xTeeth :=
  ⟨fun w => (teeth_in_range pol h).1
      ((LedgerGuards.hasWitness_iff Cm.lawful_sRef hpol _ _).1 w),
    (LedgerGuards.hasWitness_iff Cm.lawful_sRef (polCond_of_tests polTests_lax) _ _).2
      (teeth_in_range pol h).2⟩

end Policy.Teeth
