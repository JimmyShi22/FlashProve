-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/PosGuards.lean

Guards on "true under a policy" (C, θ, cap) and, modulo 2^64 - 2^32 + 1 alone, on the relation pair
with the cost ledger, at weights whose logits are not all equal. A miss is a counted position whose
checked token is not the first choice, a hit one whose checked token is. Here a miss costs 2,047 or
2,048 more than a hit, and the clip, the mean and cap each decide a request.

The weights are `wts σ τ` (Inst/Model/SanityRef.lean), for σ t < 5,120 and τ j < 202,048: token t is
embedded in channel σ t, channel j votes for token τ j, all layers are zero. At the reference scales
(`Cm.sRef`, Cm/Rel2Guards.lean) the logits at a position with the token a are 2,047 at the token
τ (σ a) and 0 elsewhere (`lg_pos`, Cm/RelTrue.lean).

* For any logits with 2,047 at one token and 0 elsewhere: `gap_peak`. For all such σ, τ: `cost_pos`,
  `true_pos_under`, `guard_pos` (for a policy with `PolCond`), `one_miss`.
* `xOne_iff`, `real_gap`, `guard_real_gap`: every token votes for token 0; `xOne`
  (Inst/Model/ProgramRGuards.lean) misses at position 0 alone.
* `xStep_iff`, `step_gap`: token 1 votes for token 1, every other for token 0; `xStep` misses at
  position 0 alone, where by `lg_pos` the logits differ from those at the other positions.

The policies written out in `real_gap` and `step_gap` are looser than exact match
(Policy/Rel/TrueGuards.lean): they have 257 ≤ θ and 257 ≤ C, so at the all-zero weights, at every
lawful table, they admit `x1` (Inst/Model/RequestGuards2.lean; `TrueGuards.zero_all`), which exact
match refuses there (`LedgerGuards.guard_budget`).

Limits:
* The weights are made up, at the reference scales alone. All 48 layers are zero, so the logits at a
  position depend on that position's token alone: the tokens before it are not read.
* In `xOne_iff` the logits are the same at every position.
* `step_gap` is on "true under a policy" alone and moves θ alone; its third clause rests on y alone.
* Both requests miss with the gap 2,048; none is written out with the gap 2,047.
-/
import Cm.Rel2Guards
import Policy.Rel.LedgerGuards
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.PosGuards

open Inst.Model Inst.Model.SanityRef Inst.Model.ProgramRGuards

/-- Where one token f has the logit 2,047 and all others 0: the gap of w is 0 at w = f; at every
other w it is 2,047, and 1 more if f < w. -/
theorem gap_peak {V : ℕ} {l : ℕ → ℤ} {f : ℕ} (hf : f < V)
    (hl : ∀ v < V, l v = if v = f then 2047 else 0) {w : ℕ} (hw : w < V) :
    gapOf V l w = if w = f then 0 else 2047 + if f < w then 1 else 0 := by
  split
  · rename_i h0
    rw [h0]
    refine (gapOf_eq_zero_iff V l hf).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [hl v hv, hl f hf, if_pos rfl]
      split <;> norm_num
    · rw [hl v (lt_trans hv hf), hl f hf, if_pos rfl, if_neg (Nat.ne_of_lt hv)]
      norm_num
  · rename_i h0
    refine le_antisymm ?_ ?_
    · obtain ⟨j, hj, e⟩ := (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).2
      unfold gapOf
      rw [← e]
      show l j - l w + (if j < w then 1 else 0) ≤ _
      rw [hl j (by omega), hl w hw, if_neg h0]
      by_cases c : j = f
      · rw [c, if_pos rfl]
        split_ifs <;> norm_num
      · rw [if_neg c]
        split_ifs <;> norm_num
    · have := le_gapOf V l (w := w) hf
      rwa [hl f hf, if_pos rfl, hl w hw, if_neg h0, sub_zero] at this

/- In this section the weights are `wts σ τ`, at the reference scales, with σ t < 5,120 for all t
(`hσ`); in `cost_pos` and `one_miss` also τ j < 202,048 for all j (`hτ`). Under both, the first
choice at a position that holds the token a is τ (σ a) (`lg_pos`, `gap_peak`). -/

section
variable (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120) (hτ : ∀ j, τ j < 202048)
include hσ hτ

/-- The cost of position t at the weights `wts σ τ`: 2^8 at a hit; at a miss 2^8 + 2,047, and 1 more
if the first choice is below the checked token. -/
theorem cost_pos (x : Instance ppref) {t : ℕ} (ht : t < ppref.T) :
    costOf (lg ppref tbRef (wts σ τ) x.prompt) x t =
      2 ^ 8 + if x.w t = τ (σ (x.prompt ⟨t, ht⟩)) then 0
        else 2047 + if τ (σ (x.prompt ⟨t, ht⟩)) < x.w t then 1 else 0 := by
  unfold costOf
  rw [gap_peak (V := ppref.V) (l := lg ppref tbRef (wts σ τ) x.prompt t) (hτ _)
    (fun v hv => Cm.lg_pos σ τ x.prompt hσ t ht hv) (x.w_lt t), add_comm]

omit hτ in
/-- At the reference scales and the weights `wts σ τ`, under every policy: a request is true if and
only if it has its form and the policy's clauses hold of the integer program's logits (which
`lg_pos` gives). -/
theorem true_pos_under (pol : AcceptancePolicy) (x : Instance ppref) :
    IsTrueUnder Cm.sRef pol (Cm.Idx.ofIndex ⟨wts σ τ, wts_wf σ τ⟩) x ↔
      Head3 x ∧ PolOK (lg ppref tbRef (wts σ τ) x.prompt) pol x := by
  rw [isTrueUnder_ofIndex]
  show (RunsK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wts σ τ) x.prompt ∧ Head3 x ∧
      PolOK (lgK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wts σ τ) x.prompt) pol x) ↔ _
  rw [kap_ref, Cm.lgK_ref]
  exact ⟨fun h => h.2, fun h => ⟨Cm.runsK_ref _ _ (runs_wts σ τ x.prompt hσ), h⟩⟩

/-- One miss. If the counted position t0 checks a token that is not the first choice there, every
other counted position checks the first choice, and 2^8 ≤ C: the request is true under the policy if
and only if it has its form; the cost of the miss (2^8 + 2,047, or 2^8 + 2,048), clipped at C, is at
most 2^8 + NB (θ - 2^8); cap is at least 1 if that cost is above C; and y has gap 0 if e = 1,024. -/
theorem one_miss (pol : AcceptancePolicy) (x : Instance ppref) {t0 : ℕ} (h0 : t0 ∈ x.cnt) (ht0 : t0 < ppref.T)
    (hC : 2 ^ 8 ≤ pol.C)
    (hit : ∀ t (ht : t < ppref.T), t ∈ x.cnt → t ≠ t0 → x.w t = τ (σ (x.prompt ⟨t, ht⟩)))
    (miss : x.w t0 ≠ τ (σ (x.prompt ⟨t0, ht0⟩))) :
    IsTrueUnder Cm.sRef pol (Cm.Idx.ofIndex ⟨wts σ τ, wts_wf σ τ⟩) x ↔
      Head3 x ∧
      (min (2 ^ 8 + (2047 + if τ (σ (x.prompt ⟨t0, ht0⟩)) < x.w t0 then 1 else 0)) (pol.C : ℤ) ≤
        2 ^ 8 + (x.NB : ℤ) * ((pol.theta : ℤ) - 2 ^ 8)) ∧
      ((pol.C : ℤ) < 2 ^ 8 + (2047 + if τ (σ (x.prompt ⟨t0, ht0⟩)) < x.w t0 then 1 else 0) →
        1 ≤ pol.cap) ∧
      (x.e = ppref.T →
        gapOf ppref.V (lg ppref tbRef (wts σ τ) x.prompt (ppref.T - 1)) x.y.val = 0) := by
  rw [true_pos_under σ τ hσ]
  have hT : ∀ t ∈ x.cnt, t < ppref.T := fun t ht => by
    have h1 := lt_of_lt_of_le (Finset.mem_Ico.1 ht).2 (min_le_right _ _)
    omega
  have hc : ∀ t ∈ x.cnt, t ≠ t0 → costOf (lg ppref tbRef (wts σ τ) x.prompt) x t = 2 ^ 8 :=
    fun t ht hne => by rw [cost_pos σ τ hσ hτ x (hT t ht), if_pos (hit t _ ht hne), add_zero]
  have hc0 : costOf (lg ppref tbRef (wts σ τ) x.prompt) x t0 =
      2 ^ 8 + (2047 + if τ (σ (x.prompt ⟨t0, ht0⟩)) < x.w t0 then 1 else 0) := by
    rw [cost_pos σ τ hσ hτ x ht0, if_neg miss]
  have hC' : (2 ^ 8 : ℤ) ≤ (pol.C : ℤ) := by exact_mod_cast hC
  have hsw := sweep (lg ppref tbRef (wts σ τ) x.prompt) pol x t0 h0 hC hc
  rw [hc0] at hsw
  have hsub : (x.cnt.filter fun t => (pol.C : ℤ) < costOf (lg ppref tbRef (wts σ τ) x.prompt) x t) ⊆
      {t0} := fun t ht => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 ht
    by_contra hne
    rw [hc t h1 fun e => hne (Finset.mem_singleton.2 e)] at h2
    exact absurd h2 (not_lt.2 hC')
  constructor
  · rintro ⟨h3, hp⟩
    refine ⟨h3, hsw.1 hp.a, fun hlt => ?_, hp.c h3.1⟩
    have hm : t0 ∈ x.cnt.filter fun t =>
        (pol.C : ℤ) < costOf (lg ppref tbRef (wts σ τ) x.prompt) x t :=
      Finset.mem_filter.2 ⟨h0, by rw [hc0]; exact hlt⟩
    exact le_trans (Finset.card_pos.2 ⟨t0, hm⟩) hp.b
  · rintro ⟨h3, ha, hb, hy⟩
    refine ⟨h3, ⟨hsw.2 ha, ?_, fun _ => hy⟩⟩
    by_cases hlt : (pol.C : ℤ) <
        2 ^ 8 + (2047 + if τ (σ (x.prompt ⟨t0, ht0⟩)) < x.w t0 then 1 else 0)
    · exact le_trans (Finset.card_le_card hsub) (by rw [Finset.card_singleton]; exact hb hlt)
    · rw [Finset.filter_false_of_mem fun t ht => ?_]
      · exact Nat.zero_le _
      · by_cases e : t = t0
        · rw [e, hc0]
          exact hlt
        · rw [hc t ht e]
          exact not_lt.2 hC'

omit hτ in
/-- The same as `true_pos_under` for "has a witness modulo 2^64 - 2^32 + 1", for a policy with
`PolCond`. -/
theorem guard_pos {pol : AcceptancePolicy} (hpol : PolCond pol) (x : Instance ppref) :
    LedgerGuards.HasWitness Cm.sRef pol (Cm.Idx.ofIndex ⟨wts σ τ, wts_wf σ τ⟩) x ↔
      Head3 x ∧ PolOK (lg ppref tbRef (wts σ τ) x.prompt) pol x :=
  (LedgerGuards.hasWitness_iff Cm.lawful_sRef hpol _ x).trans (true_pos_under σ τ hσ pol x)

end

/-! ## An instance, at the reference scales -/

/-- the index of the weights at which every token votes for token 0 -/
def idx0 : Cm.Idx := Cm.Idx.ofIndex ⟨wts (fun _ => 0) (fun _ => 0), wts_wf _ _⟩

/-- The request `xOne` at these weights, at 2^8 ≤ C. Its one miss costs 2,304: it is true if and
only if min(2,304, C) ≤ 2^8 + 1,023 (θ - 2^8), and 1 ≤ cap if C < 2,304. -/
theorem xOne_iff (pol : AcceptancePolicy) (hC : 2 ^ 8 ≤ pol.C) :
    IsTrueUnder Cm.sRef pol idx0 xOne ↔
      min 2304 (pol.C : ℤ) ≤ 2 ^ 8 + 1023 * ((pol.theta : ℤ) - 2 ^ 8) ∧
      ((pol.C : ℤ) < 2304 → 1 ≤ pol.cap) := by
  have e1 : (2 : ℤ) ^ 8 + (2047 + if 0 < xOne.w 0 then 1 else 0) = 2304 := by
    rw [w_one]
    norm_num
  have hy : gapOf ppref.V (lg ppref tbRef (wts (fun _ => 0) (fun _ => 0)) xOne.prompt (ppref.T - 1))
      xOne.y.val = 0 := by
    rw [gap_peak (V := ppref.V)
      (l := lg ppref tbRef (wts (fun _ => 0) (fun _ => 0)) xOne.prompt (ppref.T - 1)) (f := 0)
      (by decide)
      (fun v hv => Cm.lg_pos (fun _ => 0) (fun _ => 0) xOne.prompt (fun _ => by norm_num)
        (ppref.T - 1) (by decide) hv)
      xOne.y.isLt]
    rfl
  have key := one_miss (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num)
    pol xOne (t0 := 0) (by unfold Instance.cnt; decide) (by decide) hC
    (fun t ht hc hne => by rw [w_one, if_neg hne]) (by rw [w_one]; norm_num)
  have key' : IsTrueUnder Cm.sRef pol idx0 xOne ↔
      Head3 xOne ∧
      (min ((2 : ℤ) ^ 8 + (2047 + if 0 < xOne.w 0 then 1 else 0)) (pol.C : ℤ) ≤
        2 ^ 8 + (xOne.NB : ℤ) * ((pol.theta : ℤ) - 2 ^ 8)) ∧
      ((pol.C : ℤ) < (2 : ℤ) ^ 8 + (2047 + if 0 < xOne.w 0 then 1 else 0) → 1 ≤ pol.cap) ∧
      (xOne.e = ppref.T →
        gapOf ppref.V (lg ppref tbRef (wts (fun _ => 0) (fun _ => 0)) xOne.prompt (ppref.T - 1))
          xOne.y.val = 0) := key
  rw [key', e1, nb_one, Nat.cast_ofNat]
  exact ⟨fun h => ⟨h.2.1, h.2.2.1⟩, fun h => ⟨head3_one, h.1, h.2, fun _ => hy⟩⟩

/-- The clip, the mean and cap each decide `xOne`, whose miss has the gap 2,048. -/
theorem real_gap :
    IsTrueUnder Cm.sRef ⟨2304, 259, 0⟩ idx0 xOne ∧
    ¬ IsTrueUnder Cm.sRef ⟨2304, 258, 0⟩ idx0 xOne ∧
    IsTrueUnder Cm.sRef ⟨300, 257, 1⟩ idx0 xOne ∧
    ¬ IsTrueUnder Cm.sRef ⟨300, 257, 0⟩ idx0 xOne ∧
    ¬ IsTrueUnder Cm.sRef ⟨2000, 257, 1⟩ idx0 xOne := by
  refine ⟨(xOne_iff _ (by norm_num)).2 ⟨by norm_num, by norm_num⟩, fun h => ?_,
    (xOne_iff _ (by norm_num)).2 ⟨by norm_num, by norm_num⟩, fun h => ?_, fun h => ?_⟩
  · have h1 := ((xOne_iff _ (by norm_num)).1 h).1
    norm_num at h1
  · have h1 := ((xOne_iff _ (by norm_num)).1 h).2
    norm_num at h1
  · have h1 := ((xOne_iff _ (by norm_num)).1 h).1
    norm_num at h1

/-- The same for "has a witness modulo 2^64 - 2^32 + 1". -/
theorem guard_real_gap :
    LedgerGuards.HasWitness Cm.sRef ⟨2304, 259, 0⟩ idx0 xOne ∧
    ¬ LedgerGuards.HasWitness Cm.sRef ⟨2304, 258, 0⟩ idx0 xOne ∧
    LedgerGuards.HasWitness Cm.sRef ⟨300, 257, 1⟩ idx0 xOne ∧
    ¬ LedgerGuards.HasWitness Cm.sRef ⟨300, 257, 0⟩ idx0 xOne ∧
    ¬ LedgerGuards.HasWitness Cm.sRef ⟨2000, 257, 1⟩ idx0 xOne := by
  have w := fun (pol : AcceptancePolicy) (hp : PolCond pol) =>
    LedgerGuards.hasWitness_iff Cm.lawful_sRef hp idx0 xOne
  obtain ⟨a, b, c, d, e⟩ := real_gap
  exact ⟨(w _ ⟨by norm_num, by norm_num, by norm_num⟩).2 a,
    fun h => b ((w _ ⟨by norm_num, by norm_num, by norm_num⟩).1 h),
    (w _ ⟨by norm_num, by norm_num, by norm_num⟩).2 c,
    fun h => d ((w _ ⟨by norm_num, by norm_num, by norm_num⟩).1 h),
    fun h => e ((w _ ⟨by norm_num, by norm_num, by norm_num⟩).1 h)⟩

/-! ## An instance, at the reference scales, whose logits differ from position to position -/

/-- token 1 goes to 1, every other number to 0: as σ, the channel of a token; as τ, a channel's
vote -/
def vote (a : ℕ) : ℕ := if a = 1 then 1 else 0

theorem vote_le (a : ℕ) : vote a ≤ 1 := by
  unfold vote
  split <;> norm_num

/-- the index of the weights at which token 1 votes for token 1 and every other token for token 0 -/
def idx1 : Cm.Idx := Cm.Idx.ofIndex ⟨wts vote vote, wts_wf _ _⟩

/-- x_0 = 0, all other tokens are 1, y = 1; r = 0, e = 1,024 -/
def xStep : Instance ppref :=
  ⟨fun t => if t.val = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨0, by decide⟩, ⟨1024, by decide⟩⟩

theorem nb_step : xStep.NB = 1023 := by decide
theorem head3_step : Head3 xStep := by unfold Head3; decide

/-- every position checks token 1 -/
theorem w_step (t : ℕ) : xStep.w t = 1 := by
  unfold Instance.w Instance.tok
  split
  · show ((if t + 1 = 0 then (⟨0, by decide⟩ : Fin ppref.V)
        else ⟨1, by decide⟩) : Fin ppref.V).val = 1
    rw [if_neg (Nat.succ_ne_zero t)]
  · rfl

/-- the token at position t: 0 at t = 0, else 1 -/
theorem prompt_step {t : ℕ} (ht : t < ppref.T) :
    (xStep.prompt ⟨t, ht⟩).val = if t = 0 then 0 else 1 := by
  show ((if t = 0 then (⟨0, by decide⟩ : Fin ppref.V) else ⟨1, by decide⟩) : Fin ppref.V).val = _
  split <;> rfl

/-- The request `xStep` at these weights, at 2^8 ≤ C. Position 0 holds token 0, so the first choice
there is token 0, and it checks token 1: a miss at the cost 2,304. Every other position holds token
1, so the first choice there is token 1, and it checks token 1. The request is true if and only if
min(2,304, C) ≤ 2^8 + 1,023 (θ - 2^8), and 1 ≤ cap if C < 2,304. -/
theorem xStep_iff (pol : AcceptancePolicy) (hC : 2 ^ 8 ≤ pol.C) :
    IsTrueUnder Cm.sRef pol idx1 xStep ↔
      min 2304 (pol.C : ℤ) ≤ 2 ^ 8 + 1023 * ((pol.theta : ℤ) - 2 ^ 8) ∧
      ((pol.C : ℤ) < 2304 → 1 ≤ pol.cap) := by
  have hσ : ∀ t, vote t < 5120 := fun t => lt_of_le_of_lt (vote_le t) (by norm_num)
  have hτ : ∀ j, vote j < 202048 := fun j => lt_of_le_of_lt (vote_le j) (by norm_num)
  have v0 : vote (vote (xStep.prompt ⟨0, by decide⟩).val) = 0 := by
    rw [prompt_step]
    rfl
  have e1 : (2 : ℤ) ^ 8 +
      (2047 + if vote (vote (xStep.prompt ⟨0, by decide⟩).val) < xStep.w 0 then 1 else 0) =
      2304 := by
    rw [v0, w_step]
    norm_num
  have hy : gapOf ppref.V (lg ppref tbRef (wts vote vote) xStep.prompt (ppref.T - 1))
      xStep.y.val = 0 := by
    rw [gap_peak (V := ppref.V) (l := lg ppref tbRef (wts vote vote) xStep.prompt (ppref.T - 1))
      (f := vote (vote (xStep.prompt ⟨ppref.T - 1, by decide⟩).val)) (hτ _)
      (fun v hv => Cm.lg_pos vote vote xStep.prompt hσ (ppref.T - 1) (by decide) hv)
      xStep.y.isLt, prompt_step]
    rfl
  have key := one_miss vote vote hσ hτ pol xStep (t0 := 0) (by unfold Instance.cnt; decide)
    (by decide) hC
    (fun t ht _ hne => by rw [w_step, prompt_step, if_neg hne]; rfl)
    (by rw [w_step, v0]; norm_num)
  rw [show IsTrueUnder Cm.sRef pol idx1 xStep ↔ _ from key, e1, nb_step, Nat.cast_ofNat]
  exact ⟨fun h => ⟨h.2.1, h.2.2.1⟩, fun h => ⟨head3_step, h.1, h.2, fun _ => hy⟩⟩

/-- The mean decides `xStep`: true at (2304, 259, 0), not at (2304, 258, 0). At the weights of
`xOne_iff`, where every token votes for token 0, it is true under no policy: y is not the first
choice at the last position. -/
theorem step_gap :
    IsTrueUnder Cm.sRef ⟨2304, 259, 0⟩ idx1 xStep ∧
    ¬ IsTrueUnder Cm.sRef ⟨2304, 258, 0⟩ idx1 xStep ∧
    ∀ pol, ¬ IsTrueUnder Cm.sRef pol idx0 xStep := by
  refine ⟨(xStep_iff _ (by norm_num)).2 ⟨by norm_num, by norm_num⟩, fun h => ?_, fun pol h => ?_⟩
  · have h1 := ((xStep_iff _ (by norm_num)).1 h).1
    norm_num at h1
  · have h1 := ((true_pos_under (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) pol xStep).1 h).2.c
      (by decide) rfl
    rw [gap_peak (V := ppref.V)
      (l := lg ppref tbRef (wts (fun _ => 0) (fun _ => 0)) xStep.prompt (ppref.T - 1)) (f := 0)
      (by decide)
      (fun v hv => Cm.lg_pos (fun _ => 0) (fun _ => 0) xStep.prompt (fun _ => by norm_num)
        (ppref.T - 1) (by decide) hv)
      xStep.y.isLt] at h1
    exact absurd h1 (by decide)

end Policy.PosGuards
