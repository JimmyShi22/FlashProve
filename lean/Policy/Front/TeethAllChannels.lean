-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/TeethAllChannels.lean

Below, a policy "excludes no output by its scores", at given settings and weights, if every output
that has scores (`HasScores`) and meets clause (c) of `MeetsPolicy` meets it. Neither of these two
reads the policy. Clause (c): a token after a full window is the model's next token.

At the reference scales a token can cost more than 2^32. So there the clauses of `MeetsPolicy`
(Policy/Front/MeetsPolicy.lean) on the mean cost and on the number of tokens above the clip can
reject an output, under some weights, at every policy with C < 2^32 and theta ≤ C, but for those
with theta = C and 1,023 ≤ cap. (C < 2^32 and theta ≤ C are what a lawful table of scales asks of
these two numbers: `Inst.Model.Lawful`, Inst/Model/Scales.lean.) This file widens
Policy/Rel/Teeth.lean and Policy/Front/Teeth.lean, where no cost is above 16,767,233. Compare
Policy/Front/MeetsPolicyIdleAtScales.lean: with MF ≤ KF + 11 in the final norm, some such policies
with theta < C, or with cap = 0, exclude no output by its scores, whatever the weights; at the
reference scales (MF = 44, KF = 30) none of these does so under all weights. The two files do not
meet: for the differences 12 and 13, and for 14 at other scales than the reference's, neither says
anything about a policy with C < 2^32.

The weights are those of Policy/Rel/Teeth.lean with another embedding. All 48 layers are zero; every
token is embedded as 2^20 in all 5,120 channels, where that file has one channel; the output matrix
is its `headAB a b`. The final norm then gives 229 in every channel, so the logits are 1,172,480 a
at token 1, -1,172,480 b at token 0 and 0 elsewhere. After the prompt of the one token 0, every
token of an output of tokens 0 costs 2^8 + 1,172,480 (a + b): at a = 4,095 and b = 4,096 that is
9,603,783,936. (The theorem on the cost, `cost_xz`, is on the cost of the library's relation on a
request, `Inst.Model.costOf`; no theorem here is on `outputCost` itself.) It need not be the largest
cost that weights reach at these scales: by hand a larger one is reached, and no theorem here says
what the largest is.

Words of the library's relation on a request, in parts 2 and 3: `xz rF eF`
(Inst/Model/RequestGuards2.lean) is the request of 1,024 tokens 0 that announces token 0; r and e
are its two numbers `rF` and `eF`, the ends of the stretch of positions that it covers; NB is the
number of its counted positions (`Instance.NB`, Inst/Model/ProgramR.lean).

Main names.
* `out_rowAll`, `ok_rowAll`: the norm of the row with 2^20 in every channel.
* `lg_wtsAll`, `cost_xz`: the logits, the cost of a position.
* `xz_iff`: at these weights, exactly when the request of 1,024 tokens 0 is true under a policy.
* `meetsPolicy_replicate_iff`: at the weights of `iTeethAll`, for 1 ≤ n ≤ 1,023, exactly which
  policies the output of n tokens 0 meets. `teeth_in_range_meetsPolicy`: the same at n = 1,023, as a
  range of policies that it fails.
* `every_output_at_meets_iff`: at the settings of the reference scales, for 1 ≤ n ≤ 1,023, a policy
  with C < 2^32 and theta ≤ C is met, under all weights, by every output of n counted tokens that
  has scores and meets clause (c), if and only if theta = C and n ≤ cap.
* `every_output_meets_iff`: the same for outputs of every length: if and only if theta = C and
  1,023 ≤ cap.
* `every_short_output_meets_iff`: the same for outputs of at most cap counted tokens, at a policy
  with 1 ≤ cap and theta < 9,603,783,936: if and only if C ≤ theta.
* `meetsPolicy_zeroWeights_of_scores` (in the namespace `Policy`): at all valid settings, under the
  all-zero weights, every output that has scores and meets clause (c) meets every policy with
  257 ≤ theta and 257 ≤ C. Part 6 is on other weights than the rest of this file. It stands here
  because a limit below and two docstrings of part 5 use it.

Limits: those of Policy/Rel/Teeth.lean and Policy/Front/Teeth.lean.
* In the three theorems `every_output_at_meets_iff`, `every_output_meets_iff` and
  `every_short_output_meets_iff`, "under all weights" is part of the left side. They name the
  policies that exclude no output by its scores whatever the model is. A policy that fails the left
  side rejects some output under some made-up weights. Under the weights at hand it may still be met
  by every output that has scores and meets clause (c): under the all-zero weights every policy with
  257 ≤ theta and 257 ≤ C is (`meetsPolicy_zeroWeights_of_scores`, part 6 of this file).
* The weights are made up, with the same logits after every context. The theorems show that the two
  clauses can reject an output. They do not show that these clauses reject anything at a trained
  model, or how often. Every rejection shown here is of an output whose counted tokens all have one
  cost.
* The unit of a gap is that of the given weights' own integer logits, and the number of counted
  tokens is that of one output, which in a soundness statement the prover picks and may cut. At
  theta = C a reply that is cut into outputs of at most cap counted tokens meets the policy in each,
  whatever its tokens, given scores and clause (c).
* All statements but `meetsPolicy_zeroWeights_of_scores` are at the settings of the reference scales
  (`settingsOf Cm.sRef`) alone. That these are the settings which the library's reader returns at
  the two named sets of public files, and the three theorems on all weights at what the reader
  returns there: Johnson/Goal/Files/MeetsPolicyAtFiles.lean. About files with other scales nothing
  is said.
* Nothing here speaks of a protocol, a prover or a verifier.
* Numbers are evaluated by Lean's kernel (`decide +kernel`) on closed integer terms, as in
  Inst/Model/SanityRef.lean.

Terms: lean/GLOSSARY.md.

-/
import Policy.Front.Teeth
import Policy.Front.MeetsPolicyGuards
noncomputable section

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.TeethAll

open VerifiableInference
open Inst.Model Inst.Model.SanityRef Inst.Model.ProgramRGuards Inst.Model.RequestGuards2
open Policy.Teeth (Votes headAB wtsAB_wf polOK_const_iff cnt_lt built_xz)

/-! ## 1. The normalisation of the row with 2^20 in every channel -/

/-- the row with the entry 2^20 in each of the 5,120 channels -/
def rowAll : Vec := fun j => if j < 5120 then 2 ^ 20 else 0

/-- the sum of its squares: 5,120 · 2^40 -/
theorem V_rowAll : NORM.V 5120 rowAll = 5629499534213120 := by
  unfold NORM.V
  rw [Finset.sum_congr rfl fun j hj => show rowAll j ^ 2 = 2 ^ 40 by
    rw [show rowAll j = 2 ^ 20 from if_pos (Finset.mem_range.1 hj)]
    norm_num]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- the root of that sum plus 53,687, rounded down -/
theorem sig_rowAll : NORM.sig npR 5120 rowAll = 75029990 := by
  unfold NORM.sig
  rw [V_rowAll]
  decide +kernel

/-- the reciprocal: 2^44 divided by the root, rounded -/
theorem R_rowAll : NORM.R npR 5120 rowAll = 234469 := by
  unfold NORM.R
  rw [sig_rowAll]
  decide +kernel

/-- the quotient in each channel: 2^20 times the reciprocal, divided by 2^30, rounded -/
theorem yw_rowAll {j : ℕ} (hj : j < 5120) : NORM.yw npR 5120 rowAll j = 229 := by
  unfold NORM.yw
  rw [R_rowAll, show rowAll j = 2 ^ 20 from if_pos hj]
  decide +kernel

/-- the norm's output in each channel: the clamp at 2,047 leaves 229 as it is -/
theorem out_rowAll {j : ℕ} (hj : j < 5120) : NORM.out npR 5120 rowAll j = 229 := by
  unfold NORM.out
  rw [yw_rowAll hj]
  decide +kernel

/-- Neither range condition of the norm fails on this row. -/
theorem ok_rowAll : NORM.OK npR 5120 rowAll := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [V_rowAll]
    decide +kernel
  · rw [yw_rowAll hj]
    unfold Fits16
    norm_num

/-! ## 2. The weights, their logits, the cost of a position -/

/-- every token has the embedding row with 2^20 in every channel -/
def embAll : Mat := fun t j => if t < 202048 ∧ j < 5120 then 2 ^ 20 else 0

/-- The weights: all layers zero, every token embedded as 2^20 in every channel, the output matrix
`headAB a b` (Policy/Rel/Teeth.lean). -/
def wtsAll (a b : ℤ) : Weights := ⟨fun _ => zeroLayer, embAll, headAB a b⟩

/-- For a, b with `Votes` the weights are well-formed. -/
theorem wtsAll_wf {a b : ℤ} (h : Votes a b) : (wtsAll a b).WF ppref := by
  refine ⟨(wtsAB_wf h).1, fun t j => ?_, (wtsAB_wf h).2.2⟩
  show if t < 202048 ∧ j < 5120 then _ ≤ embAll t j ∧ embAll t j ≤ _ else embAll t j = 0
  unfold embAll
  split_ifs <;> norm_num

/-- The stream at the start: at every position the row with 2^20 in every channel. -/
theorem X0_wtsAll (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) (pos : ℕ) (h : pos < ppref.T) :
    X ppref tbRef (wtsAll a b) prompt 0 pos = rowAll := by
  funext j
  show (if h : pos < ppref.T then embAll (prompt ⟨pos, h⟩) j else 0) = _
  rw [dif_pos h]
  unfold embAll rowAll
  by_cases hj : j < 5120
  · rw [if_pos ⟨(prompt ⟨pos, h⟩).2, hj⟩, if_pos hj]
  · rw [if_neg fun hh => hj hh.2, if_neg hj]

/-- No range condition fails, whatever a, b and the prompt. -/
theorem runs_wtsAll (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) :
    Runs ppref tbRef (wtsAll a b) prompt :=
  runs_zero ppref tbRef embAll (headAB a b) prompt shifts_ref fun pos hpos => by
    have e : X ppref tbRef ⟨fun _ => zeroLayer, embAll, headAB a b⟩ prompt 0 pos = rowAll :=
      X0_wtsAll a b prompt pos hpos
    rw [e]
    exact ⟨ok_rowAll, ok_rowAll, ok_rowAll⟩

/-- The logits at every position, for every prompt: 1,172,480 a at token 1, -1,172,480 b at token 0,
0 at every other token. -/
theorem lg_wtsAll (a b : ℤ) (prompt : Fin ppref.T → Fin ppref.V) (pos : ℕ) (hpos : pos < ppref.T)
    {ι : ℕ} (hι : ι < 202048) :
    lg ppref tbRef (wtsAll a b) prompt pos ι =
      if ι = 1 then 1172480 * a else if ι = 0 then -(1172480 * b) else 0 := by
  have e : X ppref tbRef (wtsAll a b) prompt (2 * ppref.layers) pos = rowAll := by
    rw [show X ppref tbRef (wtsAll a b) prompt (2 * ppref.layers) =
        X ppref tbRef (wtsAll a b) prompt 0
        from X_zero ppref tbRef embAll (headAB a b) prompt shifts_ref _]
    exact X0_wtsAll a b prompt pos hpos
  unfold lg nrm dot
  rw [e]
  show ∑ j ∈ Finset.range 5120, NORM.out npR 5120 rowAll j * headAB a b j ι = _
  rw [Finset.sum_congr rfl fun j hj =>
    show NORM.out npR 5120 rowAll j * headAB a b j ι =
        229 * (if ι = 1 then a else if ι = 0 then -b else 0) by
      rw [out_rowAll (Finset.mem_range.1 hj)]
      unfold headAB
      rw [if_pos ⟨Finset.mem_range.1 hj, hι⟩]]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- Under such logits, for a, b with `Votes`, the gap of token 0 is 1,172,480 (a + b). No token is
below token 0, so no tie adds 1. -/
theorem gap_zero {a b : ℤ} (h : Votes a b) {l : ℕ → ℤ}
    (hl : ∀ v < ppref.V,
      l v = if v = 1 then 1172480 * a else if v = 0 then -(1172480 * b) else 0) :
    gapOf ppref.V l 0 = 1172480 * (a + b) := by
  obtain ⟨a0, -, b0, -⟩ := h
  have l0 : l 0 = -(1172480 * b) := by
    rw [hl 0 (by decide), if_neg (by norm_num), if_pos rfl]
  have l1 : l 1 = 1172480 * a := by rw [hl 1 (by decide), if_pos rfl]
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

/-- For a, b with `Votes`, every position of `xz` costs 2^8 + 1,172,480 (a + b), whatever r and e.
-/
theorem cost_xz {a b : ℤ} (h : Votes a b) (rF eF : Fin (ppref.T + 1)) {t : ℕ} (ht : t < ppref.T) :
    costOf (lg ppref tbRef (wtsAll a b) (xz rF eF).prompt) (xz rF eF) t =
      2 ^ 8 + 1172480 * (a + b) := by
  unfold costOf
  rw [xz_w, gap_zero h (fun v hv => lg_wtsAll a b _ t ht hv), add_comm]

/-! ## 3. True under a policy at these weights -/

/-- The index that holds the weights `wtsAll a b`, for a, b with `Votes`. -/
def idxAll {a b : ℤ} (h : Votes a b) : Cm.Idx := Cm.Idx.ofIndex ⟨wtsAll a b, wtsAll_wf h⟩

/-- The integer program at the reference scales runs on every prompt at the weights that `idxAll h`
holds. -/
theorem runsK_idxAll {a b : ℤ} (h : Votes a b) (prompt : Fin ppref.T → Fin ppref.V) :
    RunsK ppref Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) (idxAll h).index.val prompt := by
  unfold idxAll
  rw [Cm.index_ofIndex]
  show RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAll a b) prompt
  rw [kap_ref]
  exact Cm.runsK_ref _ _ (runs_wtsAll a b prompt)

/-- At the reference scales and these weights, under every policy: a request is true if and only if
it has its form and the policy's clauses hold of the logits that `lg_wtsAll` gives. -/
theorem true_iff {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) (x : Instance ppref) :
    IsTrueUnder Cm.sRef pol (idxAll h) x ↔
      Head3 x ∧ PolOK (lg ppref tbRef (wtsAll a b) x.prompt) pol x := by
  unfold idxAll
  rw [isTrueUnder_ofIndex]
  show (RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAll a b) x.prompt ∧ Head3 x ∧
      PolOK (lgK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAll a b) x.prompt) pol x) ↔ _
  rw [kap_ref, Cm.lgK_ref]
  exact ⟨fun h => h.2, fun h => ⟨Cm.runsK_ref _ _ (runs_wtsAll a b x.prompt), h⟩⟩

/-- For a, b with `Votes`, every policy, r and e, with k = 2^8 + 1,172,480 (a + b) and NB the number
of counted positions: `xz` is true under the policy if and only if r < e; NB = 0 or
min(k, C) ≤ theta; NB ≤ cap if C < k; and a + b = 0 if e = 1,024. -/
theorem xz_iff {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) (rF eF : Fin (ppref.T + 1)) :
    IsTrueUnder Cm.sRef pol (idxAll h) (xz rF eF) ↔
      rF.val < eF.val ∧
      ((xz rF eF).NB = 0 ∨ min (2 ^ 8 + 1172480 * (a + b)) (pol.C : ℤ) ≤ pol.theta) ∧
      ((pol.C : ℤ) < 2 ^ 8 + 1172480 * (a + b) → (xz rF eF).NB ≤ pol.cap) ∧
      (eF.val = ppref.T → a + b = 0) := by
  rw [true_iff h, polOK_const_iff _ pol _ _ fun t ht => cost_xz h rF eF (cnt_lt _ ht)]
  have hg : gapOf ppref.V (lg ppref tbRef (wtsAll a b) (xz rF eF).prompt (ppref.T - 1))
      (xz rF eF).y.val = 1172480 * (a + b) :=
    gap_zero h fun v hv => lg_wtsAll a b _ (ppref.T - 1) (by decide) hv
  rw [hg]
  constructor
  · rintro ⟨h3, h1, h2, hc⟩
    exact ⟨h3.1, h1, h2, fun e => by have := hc h3.1 e; omega⟩
  · rintro ⟨hre, h1, h2, hc⟩
    exact ⟨⟨hre, Nat.lt_succ_iff.1 eF.isLt, fun _ => rfl⟩, h1, h2,
      fun _ e => by have := hc e; rw [this]; norm_num⟩

/-- The index with the largest votes: a = 4,095, b = 4,096. -/
def iTeethAll : Cm.Idx :=
  idxAll (a := 4095) (b := 4096) ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The cost of every position at `iTeethAll`. -/
theorem cost_number : (2 : ℤ) ^ 8 + 1172480 * (4095 + 4096) = 9603783936 := by norm_num

/-- `xz` with r = 0 and e = 1,023 has 1,023 counted positions. -/
theorem nb_1023 : (xz ⟨0, by decide⟩ ⟨1023, by decide⟩).NB = 1023 := by decide

/-- `xz` with r = 0 and e = n ≤ 1,023 has n counted positions. -/
theorem nb_xz {n : ℕ} (hn : n ≤ 1023) (h0 : 0 < ppref.T + 1) (h1 : n < ppref.T + 1) :
    (xz ⟨0, h0⟩ ⟨n, h1⟩).NB = n := by
  show min n (ppref.T - 1) - 0 = n
  have hT : ppref.T = 1024 := by decide
  rw [hT]
  omega

/-- Exactly which policies reject the request of 1,024 tokens 0 with r = 0 and e = 1,023 at
`iTeethAll`: those with theta < C and theta < 9,603,783,936, and those with C < 9,603,783,936 and
cap < 1,023. -/
theorem refused_iff (pol : AcceptancePolicy) :
    ¬ IsTrueUnder Cm.sRef pol iTeethAll (xz ⟨0, by decide⟩ ⟨1023, by decide⟩) ↔
      (pol.theta < pol.C ∧ pol.theta < 9603783936) ∨ (pol.C < 9603783936 ∧ pol.cap < 1023) := by
  unfold iTeethAll
  rw [xz_iff, cost_number, nb_1023]
  have h1 : ((⟨0, by decide⟩ : Fin (ppref.T + 1)).val < (⟨1023, by decide⟩ : Fin (ppref.T + 1)).val)
      := by decide
  have h2 : ¬ ((⟨1023, by decide⟩ : Fin (ppref.T + 1)).val = ppref.T) := by decide
  have c1 : ((pol.C : ℤ) < 9603783936) ↔ pol.C < 9603783936 := by exact_mod_cast Iff.rfl
  have c2 : (min (9603783936 : ℤ) (pol.C : ℤ) ≤ pol.theta) ↔
      (9603783936 ≤ pol.theta ∨ pol.C ≤ pol.theta) := by
    rw [min_le_iff]
    exact_mod_cast Iff.rfl
  rw [c1, c2]
  constructor
  · intro hn
    by_contra hr
    refine hn ⟨h1, Or.inr ?_, fun hC => ?_, fun e => absurd e h2⟩
    · by_contra hm
      exact hr (Or.inl (by omega))
    · by_contra hm
      exact hr (Or.inr (by omega))
  · rintro hr ⟨-, ha, hb, -⟩
    rcases hr with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · rcases ha with ha | ha | ha <;> omega
    · have := hb r1
      omega

/-! ## 4. The same for a prompt and output tokens -/

/-- For a, b with `Votes`, every policy and 1 ≤ n ≤ 1,024, at the settings of the reference scales
and the weights that `idxAll h` holds: after the prompt of one token 0 the output of n tokens 0
meets the policy if and only if the request `xz` with r = 0 and e = n is true under it. -/
theorem meetsPolicy_iff_xz {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) {n : ℕ} (h0 : 0 < n)
    (hn : n ≤ 1024) :
    MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAll h)) [0]
        (List.replicate n 0) ↔
      IsTrueUnder Cm.sRef pol (idxAll h) (xz ⟨0, by decide⟩ ⟨n, Nat.lt_succ_of_le hn⟩) := by
  rw [isTrueUnder_iff_meetsPolicy Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl
    pol (idxAll h) (built_xz h0 hn)]
  exact ⟨fun m => ⟨runsK_idxAll h _, m⟩, fun m => m.2⟩

/-- **Which policies one output of n tokens meets, under made-up weights at the reference scales.**
At the settings of the reference scales and the weights that `iTeethAll` holds, for 1 ≤ n ≤ 1,023,
after the prompt of one token 0: the output of n tokens 0 meets a policy exactly if
min(9,603,783,936, C) ≤ theta, and n ≤ cap in case C < 9,603,783,936. 9,603,783,936 is the cost of
each position of the request that is built from them (`cost_xz`, `cost_number`). Weights and prompt
do not depend on the policy or on n. The weights are made up: see the limits at the top of this
file. -/
theorem meetsPolicy_replicate_iff (pol : AcceptancePolicy) {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeethAll) [0]
        (List.replicate n 0) ↔
      min (9603783936 : ℤ) (pol.C : ℤ) ≤ pol.theta ∧
        ((pol.C : ℤ) < 9603783936 → n ≤ pol.cap) := by
  have hT : ppref.T = 1024 := by decide
  refine (meetsPolicy_iff_xz _ pol h0 (by omega : n ≤ 1024)).trans ?_
  rw [xz_iff, cost_number, nb_xz hn]
  constructor
  · rintro ⟨-, a, b, -⟩
    exact ⟨a.resolve_left (by omega), b⟩
  · rintro ⟨a, b⟩
    refine ⟨h0, Or.inr a, b, fun e => ?_⟩
    have e' : n = ppref.T := e
    rw [hT] at e'
    omega

/-- **Which policies one output of 1,023 tokens fails, under made-up weights at the reference
scales.** At the settings of the reference scales and the weights that `iTeethAll` holds, after the
prompt of one token 0, the output of 1,023 tokens 0 does not meet a policy exactly if theta < C and
theta < 9,603,783,936, or C < 9,603,783,936 and cap < 1,023. Weights, prompt and output do not
depend on the policy. `HasScores` and `afterFullWindow` do not read the policy, and the output meets
some policies, so what rejects it is `meanCost` or `aboveClip`. The weights are made up: see the
limits at the top of this file. -/
theorem teeth_in_range_meetsPolicy (pol : AcceptancePolicy) :
    ¬ MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeethAll) [0]
        (List.replicate 1023 0) ↔
      (pol.theta < pol.C ∧ pol.theta < 9603783936) ∨ (pol.C < 9603783936 ∧ pol.cap < 1023) :=
  (not_congr (meetsPolicy_iff_xz _ pol (by norm_num) (by norm_num))).trans (refused_iff pol)

/-! ## 5. The policies that every output meets, whatever the weights -/

/-- The window of the reference scales' settings has 1,024 positions. -/
theorem positions_ref : (settingsOf Cm.sRef).positions = 1024 :=
  (Back.valid_numbers (settingsAreValid_settingsOf Cm.lawful_sRef)).1

/-- For 1 ≤ n ≤ 1,023, at the weights that `iTeethAll` holds, the output of n tokens 0 after the
prompt of one token 0 meets the policy (9,603,783,936, 9,603,783,936, 0) and has n counted tokens.
So it has scores and meets clause (c) of `MeetsPolicy`, which are parts of the claim. -/
theorem replicate_facts {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) ⟨9603783936, 9603783936, 0⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeethAll) [0]
        (List.replicate n 0) ∧
      countedTokens (settingsOf Cm.sRef) [0] (List.replicate n 0) = n := by
  refine ⟨(meetsPolicy_replicate_iff _ h0 hn).2
    ⟨min_le_right _ _, fun c => absurd c (by norm_num)⟩, ?_⟩
  unfold countedTokens
  rw [positions_ref, List.length_replicate, List.length_singleton]
  omega

/-- **At the settings of the reference scales, for 1 ≤ n ≤ 1,023, a policy with C < 2^32 and
theta ≤ C is met under all weights by every output of n counted tokens that has scores and meets
clause (c), if and only if theta = C and n ≤ cap.** C < 2^32 and theta ≤ C are what a lawful table
of scales asks of these two numbers (`Inst.Model.Lawful`, Inst/Model/Scales.lean). Clause (c) of
`MeetsPolicy`: a token after a full window is the model's next token. The left side ranges over all
weights. A policy that fails it rejects some output under some made-up weights. Under the weights at
hand it may still be met by every output that has scores and meets clause (c): under the all-zero
weights every policy with 257 ≤ theta and 257 ≤ C is (`meetsPolicy_zeroWeights_of_scores`, part 6 of
this file). So these are the policies that exclude no output of that many counted tokens by its
scores whatever the model is, not all the policies that mean nothing for a given model. For
2^8 ≤ theta the right side is where the library's port of `policyEmpty` returns 4
(`OnBytes.Model.policyEmpty` at n, C, theta, cap and the exponent 8, OnBytes/Model/Config.lean;
`policyEmpty_eq_four_iff`, Johnson/IMR/MeetsPolicyAtPort.lean). Limits: "only if" is shown by one
output under made-up weights. n counts one output, which in a soundness statement the prover picks
and may cut. The same at what the library's reader returns at the two named sets of public files:
the theorem of this name in Johnson/Goal/Files/MeetsPolicyAtFiles.lean. -/
theorem every_output_at_meets_iff (pol : AcceptancePolicy) (clip : pol.C < 2 ^ 32) (mean : pol.theta ≤ pol.C)
    {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1023) :
    (∀ (weights : ModelWeights (settingsOf Cm.sRef)) (prompt output : List Token),
      HasScores (settingsOf Cm.sRef) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOf Cm.sRef).positions ≤ prompt.length + position →
          modelNextToken (settingsOf Cm.sRef) weights (prompt ++ output.take position) =
            some output[position]) →
      countedTokens (settingsOf Cm.sRef) prompt output = n →
      MeetsPolicy (settingsOf Cm.sRef) pol weights prompt output) ↔
      pol.theta = pol.C ∧ n ≤ pol.cap := by
  constructor
  · intro all
    obtain ⟨base, counted⟩ := replicate_facts h0 hn
    obtain ⟨a, b⟩ := (meetsPolicy_replicate_iff pol h0 hn).1
      (all _ _ _ base.toHasScores base.afterFullWindow counted)
    have small : (pol.C : ℤ) < 9603783936 := by
      have : pol.C < 9603783936 := lt_trans clip (by norm_num)
      exact_mod_cast this
    rw [min_eq_right small.le] at a
    exact ⟨le_antisymm mean (by exact_mod_cast a), b small⟩
  · rintro ⟨e, limit⟩ weights prompt output scores after counted
    exact (meetsPolicy_iff_of_clip_le_mean (le_of_eq e.symm) (by rw [counted]; exact limit)).2
      ⟨scores, after⟩

/-- **At the settings of the reference scales, a policy with C < 2^32 and theta ≤ C is met under all
weights by every output that has scores and meets clause (c), if and only if theta = C and
1,023 ≤ cap.** 1,023 is the largest number of counted tokens: a prompt has at least one token, and
the window has 1,024. It is `every_output_at_meets_iff` for all lengths at once. The left side
ranges over all weights. A policy that fails it rejects some output under some made-up weights.
Under the weights at hand it may still be met by every output that has scores and meets clause (c):
under the all-zero weights every policy with 257 ≤ theta and 257 ≤ C is
(`meetsPolicy_zeroWeights_of_scores`, part 6 of this file). So these are the policies that exclude
no output by its scores whatever the model is, not all the policies that mean nothing for a given
model. A policy with theta = C and 1 ≤ cap < 1,023 fails the left side, yet it excludes only outputs
of more than cap counted tokens: every output of at most cap counted tokens that has scores and
meets clause (c) meets it (`every_short_output_meets_iff`), and in a soundness statement the prover
picks the cut. Limits: "only if" is shown by one output of 1,023 tokens under made-up weights; it
says nothing of a trained model. The same at what the library's reader returns at the two named sets
of public files: the theorem of this name in Johnson/Goal/Files/MeetsPolicyAtFiles.lean. -/
theorem every_output_meets_iff (pol : AcceptancePolicy) (clip : pol.C < 2 ^ 32) (mean : pol.theta ≤ pol.C) :
    (∀ (weights : ModelWeights (settingsOf Cm.sRef)) (prompt output : List Token),
      HasScores (settingsOf Cm.sRef) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOf Cm.sRef).positions ≤ prompt.length + position →
          modelNextToken (settingsOf Cm.sRef) weights (prompt ++ output.take position) =
            some output[position]) →
      MeetsPolicy (settingsOf Cm.sRef) pol weights prompt output) ↔
      pol.theta = pol.C ∧ 1023 ≤ pol.cap := by
  constructor
  · intro all
    exact (every_output_at_meets_iff pol clip mean (n := 1023) (by norm_num) (le_refl _)).1
      fun weights prompt output scores after _ => all weights prompt output scores after
  · rintro ⟨e, limit⟩ weights prompt output scores after
    refine (meetsPolicy_iff_of_clip_le_mean (le_of_eq e.symm) ?_).2 ⟨scores, after⟩
    have nonempty : 0 < prompt.length := List.length_pos_iff.2 scores.promptNonempty
    unfold countedTokens
    rw [positions_ref]
    omega

/-- **At the settings of the reference scales, a policy with 1 ≤ cap and theta < 9,603,783,936 is
met under all weights by every output of at most cap counted tokens that has scores and meets clause
(c), if and only if C ≤ theta.** Every policy with theta ≤ C < 2^32 has theta < 9,603,783,936; for
such a policy the right side is theta = C. With cap = 0 the left side holds of every policy: only
outputs without a counted token are asked. The left side ranges over all weights. At given weights
more policies are met by every such output (`meetsPolicy_of_close_logits`,
Policy/Front/MeetsPolicyBounds.lean). Limits: "only if" is shown by one output of one token under
made-up weights. The number of counted tokens is that of one output, which in a soundness statement
the prover picks and may cut: at C ≤ theta and 1 ≤ cap a reply that is cut into outputs of at most
cap counted tokens meets the policy in each, whatever its tokens, given scores and clause (c). The
same at what the library's reader returns at the two named sets of public files: the theorem of this
name in Johnson/Goal/Files/MeetsPolicyAtFiles.lean. -/
theorem every_short_output_meets_iff (pol : AcceptancePolicy) (limit : 1 ≤ pol.cap)
    (mean : pol.theta < 9603783936) :
    (∀ (weights : ModelWeights (settingsOf Cm.sRef)) (prompt output : List Token),
      HasScores (settingsOf Cm.sRef) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOf Cm.sRef).positions ≤ prompt.length + position →
          modelNextToken (settingsOf Cm.sRef) weights (prompt ++ output.take position) =
            some output[position]) →
      countedTokens (settingsOf Cm.sRef) prompt output ≤ pol.cap →
      MeetsPolicy (settingsOf Cm.sRef) pol weights prompt output) ↔
      pol.C ≤ pol.theta := by
  constructor
  · intro all
    obtain ⟨base, counted⟩ := replicate_facts (n := 1) (by norm_num) (by norm_num)
    have a := ((meetsPolicy_replicate_iff pol (n := 1) (by norm_num) (by norm_num)).1
      (all _ _ _ base.toHasScores base.afterFullWindow (by rw [counted]; exact limit))).1
    rcases min_le_iff.1 a with a | a
    · have : 9603783936 ≤ pol.theta := by exact_mod_cast a
      omega
    · exact_mod_cast a
  · intro clip weights prompt output scores after counted
    exact (meetsPolicy_iff_of_clip_le_mean clip counted).2 ⟨scores, after⟩

end Policy.TeethAll

/-! ## 6. The all-zero weights, at all valid settings -/

namespace Policy

open VerifiableInference

/-- **At valid settings, under the all-zero weights, every output that has scores and meets clause
(c) meets every policy with 257 ≤ theta and 257 ≤ C, whatever cap is.** It is
`meetsPolicy_zeroWeights` (Policy/Front/TrueUnder.lean) with its side conditions drawn from scores
and clause (c). The one that is not a part of `HasScores` is that a token after a full window is
token 0. That theorem, at the output of the one token 0 after the full window, says that token 0 is
the model's next token there, and clause (c) says that the output's token is. So at such a policy
the claim, said of weights of which one knows only that they exist, says little. That there are such
outputs: `meetsPolicy_zeroWeights`. -/
theorem meetsPolicy_zeroWeights_of_scores {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {policy : Inst.Model.AcceptancePolicy} (mean : 257 ≤ policy.theta)
    (clip : 257 ≤ policy.C) {prompt output : List Token}
    (scores : HasScores settings (zeroWeights valid) prompt output)
    (after : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position →
        modelNextToken settings (zeroWeights valid) (prompt ++ output.take position) =
          some output[position]) :
    MeetsPolicy settings policy (zeroWeights valid) prompt output := by
  refine meetsPolicy_zeroWeights valid mean clip scores.promptNonempty scores.outputNonempty
    scores.length_le scores.inVocabulary fun position h full => ?_
  have vocabulary : settings.vocabulary = 202048 :=
    (Back.valid_numbers valid).2.2.2.2.2.2.2.2.2.1
  have len : (prompt ++ output.take position).length = prompt.length + position := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  have bound := scores.length_le
  have zero : MeetsPolicy settings policy (zeroWeights valid) (prompt ++ output.take position)
      [0] := by
    refine meetsPolicy_zeroWeights valid mean clip (fun e => ?_) (List.cons_ne_nil _ _) ?_
      (fun token member => ?_) fun p hp _ => ?_
    · have l0 : (prompt ++ output.take position).length = 0 := congrArg List.length e
      have pos := List.length_pos_iff.2 scores.promptNonempty
      omega
    · rw [len, List.length_singleton]
      omega
    · rcases List.mem_append.1 member with m | m
      · rcases List.mem_append.1 m with m | m
        · exact scores.inVocabulary token (List.mem_append_left _ m)
        · exact scores.inVocabulary token (List.mem_append_right _ (List.mem_of_mem_take m))
      · rw [List.mem_singleton.1 m, vocabulary]
        norm_num
    · have h1 : p < 1 := hp
      have e0 : p = 0 := by omega
      subst e0
      rfl
  have next := zero.afterFullWindow 0 Nat.zero_lt_one (by rw [len]; omega)
  rw [List.take_zero, List.append_nil, after position h full] at next
  exact (Option.some.inj next).trans rfl

end Policy

#print axioms Policy.TeethAll.rowAll
#print axioms Policy.TeethAll.V_rowAll
#print axioms Policy.TeethAll.sig_rowAll
#print axioms Policy.TeethAll.R_rowAll
#print axioms Policy.TeethAll.yw_rowAll
#print axioms Policy.TeethAll.out_rowAll
#print axioms Policy.TeethAll.ok_rowAll
#print axioms Policy.TeethAll.embAll
#print axioms Policy.TeethAll.wtsAll
#print axioms Policy.TeethAll.wtsAll_wf
#print axioms Policy.TeethAll.X0_wtsAll
#print axioms Policy.TeethAll.runs_wtsAll
#print axioms Policy.TeethAll.lg_wtsAll
#print axioms Policy.TeethAll.gap_zero
#print axioms Policy.TeethAll.cost_xz
#print axioms Policy.TeethAll.idxAll
#print axioms Policy.TeethAll.runsK_idxAll
#print axioms Policy.TeethAll.true_iff
#print axioms Policy.TeethAll.xz_iff
#print axioms Policy.TeethAll.iTeethAll
#print axioms Policy.TeethAll.cost_number
#print axioms Policy.TeethAll.nb_1023
#print axioms Policy.TeethAll.nb_xz
#print axioms Policy.TeethAll.refused_iff
#print axioms Policy.TeethAll.meetsPolicy_iff_xz
#print axioms Policy.TeethAll.meetsPolicy_replicate_iff
#print axioms Policy.TeethAll.teeth_in_range_meetsPolicy
#print axioms Policy.TeethAll.positions_ref
#print axioms Policy.TeethAll.replicate_facts
#print axioms Policy.TeethAll.every_output_at_meets_iff
#print axioms Policy.TeethAll.every_output_meets_iff
#print axioms Policy.TeethAll.every_short_output_meets_iff
#print axioms Policy.meetsPolicy_zeroWeights_of_scores
