-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/RequestGuards2.lean: more sanity lemmas for the relations on a request: every stretch
occurs; which policies are "exact match"; the reply is determined by what comes before it (at exact
match); a reply none of whose tokens is the first choice. Four definitions (two synthetic requests
`xz`, `x1`; two settings `ppCap`, `ppMean` with a synthetic policy, all else as in `ppRef` of
Inst/Model/Scales.lean), of which files of Cm/ use `xz` (Cm/RelTrue.lean, Cm/TargetPartBite2.lean),
and theorems; of these `reply_unique` is used in Cm/RelTrue.lean.
The relations: Inst/Model/ProgramR.lean (`RinfR`: with the acceptance policy; `RinfS`: every covered
token is the least token of largest logit; `RinfS0`: `RinfS` without `Head3`, the clause that the
request is well-formed: r < e ≤ T, and y = 0 if e < T). Lemmas of
Inst/Model/ProgramRGuards.lean and Inst/Model/RequestGuards.lean are used.
  1  `xz`, `zero_range`: for all valid settings, at the all-zero index: the request of 1,024 tokens
     0 with y = 0 is in `RinfR` at exact match for every r < e (`ProgramRGuards.all_exact` is the
     case r = 0, e = 1,024).
     `zero_range_not`: not every request is in `RinfR` at exact match.
     `free_at_empty`: without `Head3` the relation excludes nothing at e ≤ r: at the all-zero index
     and valid settings every prompt with every y is in `RinfS0` (a case of
     `RequestGuards.modelS_empty`: in general, wherever the program runs). It is `Head3` that keeps
     this out of `RinfS` and `RinfR`.
  2  `exact_match_conv`: the converse of `exact_match` (Inst/Model/ProgramR.lean): at θ = 2^8 ≤ C,
     gap 0 at every counted position, and of y at the last if e = T, gives (a), (b), (c).
     `exact_match_conv_fails`: below that it fails: at cap = 0 and C < 2^8 nothing with a counted
     position meets the policy, so there `exact_match` holds vacuously.
     `rinfR_iff_rinfS`: so for T > 0, at θ = 2^8 ≤ C with cap = 0 or 2^8 < C the relation with the
     policy is "every covered token is the least token of largest logit": a family of policies, of
     which `AcceptancePolicy.exact` is one (`RinfS_iff_exact`).
  3  `argmin_unique`, `reply_unique`: two members of `RinfS0` (so of `RinfS`) at one index with the
     same r, e and the same tokens 0 .. r have the same tokens up to number e (x_T := y): at most
     one stretch follows x_0 .. x_r. (In words: "what the integer model decodes
     greedily after x_0 .. x_r": no greedy decoder is defined here.) It is in the place of "y is
     unique", which holds on next-token requests. It uses Inst/Model/Causal.lean.
  4  `polOK_of_const`, `x1`, `budget`: a reply none of whose tokens is the first choice. (From
     exact match to (512, 2^8 + 1, 0) C and θ change together; that each number is read:
     Inst/Model/ProgramRGuards.lean.)
  5  `ppCap`, `ppMean`, `tables_differ_in_policy`: the relation at given settings reads their
     policy: three valid settings with the reference scales and final normalisation, which differ
     only in the policy: `ppRef` (2^8, 2^8, 0), `ppCap` (2^8, 2^8, 1), `ppMean` (300, 2^8 + 1, 0):
     `ProgramRGuards`' request `xOne` (one counted position checks a token that is not the first
     choice) is in the last two relations only.
Limits: Parts 1, 4 and 5 are at the all-zero index: all logits are 0, the gap 1 is a lost tie, and
which position's logits meet which token is not seen (the head of
Inst/Model/ProgramRGuards.lean). Part 2 says nothing on which policies the implementation's verifier
accepts (by a reading, no theorem, it requires θ ≤ C, cap ≤ T and more: Inst/Model/ProgTests.lean:
`PolTests`; the policy of valid settings passes them). Part 3 needs both requests in the relation:
it does not say that a stretch exists.
`ppCap` and `ppMean` are the reference settings with another policy.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.ProgramRGuards
import Inst.Model.RequestGuards
import Inst.Model.Causal

set_option autoImplicit false

namespace Inst.Model.RequestGuards2

open ScalesSanity ProgramRGuards

/-! ## 1. Every stretch -/

/-- 1,024 tokens 0, the announced token 0, any r and e -/
def xz (rF eF : Fin (ppref.T + 1)) : Instance ppref :=
  ⟨fun _ => ⟨0, by decide⟩, ⟨0, by decide⟩, rF, eF⟩

theorem xz_w (rF eF : Fin (ppref.T + 1)) (t : ℕ) : (xz rF eF).w t = 0 := by
  unfold Instance.w Instance.tok
  split <;> rfl

/-- `RinfR` at exact match holds of `xz` at every stretch r < e, at all valid settings, at the
all-zero index. -/
theorem zero_range {pp : ScalesAndPolicy} (h : Lawful pp) (rF eF : Fin (ppref.T + 1)) (hre : rF.val < eF.val) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) AcceptancePolicy.exact iZero (xz rF eF) :=
  (RinfS_iff_exact ppref (by decide) pp.kap pp.nf (fun _ => tbRef) iZero (xz rF eF)).1
    (zero_true_of h _ ⟨hre, Nat.lt_succ_iff.1 eF.isLt, fun _ => rfl⟩ fun t _ _ => xz_w rF eF t)

/-- Not everything is in it: one covered position whose checked token is not 0 takes the request out
(of `RinfR` at the policy `AcceptancePolicy.exact`, at the all-zero index; at some other valid policies it does
not: ProgramRGuards.lean: `one_cap`). -/
theorem zero_range_not (pp : ScalesAndPolicy) (x : Instance ppref) {t : ℕ} (hr : x.r ≤ t)
    (he : t < x.e) (hw : x.w t ≠ 0) :
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) AcceptancePolicy.exact iZero x := fun hR => by
  have h :=
    ((RinfS_iff_exact ppref (by decide) pp.kap pp.nf (fun _ => tbRef) iZero x).2 hR).2.2 t hr he
  rw [gap_zero' (lg_zero _ _ _ _ t) (x.w_lt t), if_neg hw] at h
  exact absurd h one_ne_zero

/-- Without `Head3` every y is in the relation at e ≤ r: here at the all-zero index and valid
settings; in general wherever the program runs. -/
theorem free_at_empty {pp : ScalesAndPolicy} (h : Lawful pp) (prompt : Fin ppref.T → Fin ppref.V)
    (y : Fin ppref.V) (rF eF : Fin (ppref.T + 1)) (hre : eF.val ≤ rF.val) :
    RinfS0 ppref pp.kap pp.nf (fun _ => tbRef) iZero ⟨prompt, y, rF, eF⟩ :=
  (RequestGuards.modelS_empty ppref pp.kap pp.nf (fun _ => tbRef) iZero.val
      ⟨prompt, y, rF, eF⟩ hre).2
    (runs_iZero h prompt)

/-! ## 2. Which policies are "exact match" -/

/-- the converse of `exact_match`, under θ = 2^8 ≤ C, and gap 0 of y at the last position if
e = T -/
theorem exact_match_conv {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)
    (hθ : pol.theta = 2 ^ 8) (hC : 2 ^ 8 ≤ pol.C) (hg : ∀ t ∈ x.cnt, gapOf P.V (lg t) (x.w t) = 0)
    (hc : x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0) : PolOK lg pol x := by
  have hc8 : ∀ t ∈ x.cnt, costOf lg x t = 2 ^ 8 :=
    fun t ht => by unfold costOf; rw [hg t ht, zero_add]
  have hC' : (2 : ℤ) ^ 8 ≤ (pol.C : ℤ) := by exact_mod_cast hC
  have hθ' : (pol.theta : ℤ) = 2 ^ 8 := by rw [hθ]; norm_num
  refine ⟨?_, ?_, fun _ => hc⟩
  · have hs : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) = ∑ _t ∈ x.cnt, (2 : ℤ) ^ 8 :=
      Finset.sum_congr rfl fun t ht => by rw [hc8 t ht, min_eq_left hC']
    rw [hs, Finset.sum_const, x.card_cnt, nsmul_eq_mul, hθ']
    exact le_of_eq (mul_comm _ _)
  · have hf : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t) = ∅ :=
      Finset.filter_false_of_mem fun t ht => by rw [hc8 t ht]; exact not_lt.2 hC'
    rw [hf]
    exact Nat.zero_le _

/-- and it fails below: cap = 0, C < 2^8, one counted position: nothing meets the policy, whatever
the gaps -/
theorem exact_match_conv_fails {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)
    (hcap : pol.cap = 0) (hC : pol.C < 2 ^ 8) {t : ℕ} (ht : t ∈ x.cnt) :
    ¬ PolOK lg pol x := fun h => by
  have hg : 0 ≤ gapOf P.V (lg t) (x.w t) := gapOf_nonneg _ _ (x.w_lt t)
  have hC' : (pol.C : ℤ) < 2 ^ 8 := by exact_mod_cast hC
  have hm : t ∈ x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t :=
    Finset.mem_filter.2 ⟨ht, by unfold costOf; omega⟩
  have h1 := Finset.card_pos.2 ⟨t, hm⟩
  have h2 := h.b
  omega

/-- The policies of exact match: if 0 < T, θ = 2^8 ≤ C, and cap = 0 or 2^8 < C, the relation with
the policy is "every covered token is the least token of largest logit at its position". -/
theorem rinfR_iff_rinfS (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (pol : AcceptancePolicy) (hθ : pol.theta = 2 ^ 8) (hC : 2 ^ 8 ≤ pol.C)
    (hc : pol.cap = 0 ∨ 2 ^ 8 < pol.C) (i : Index P) (x : Instance P) :
    RinfR P κ nf tbs pol i x ↔ RinfS P κ nf tbs i x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun t hr he => ?_⟩
    by_cases ht : t < min x.e (P.T - 1)
    · exact exact_match _ pol x hθ hc h3 t (Finset.mem_Ico.2 ⟨hr, ht⟩)
    · have hle := h2.2.1
      have e1 : t = P.T - 1 := by
        rcases Nat.lt_or_ge t (P.T - 1) with h | h
        · exact absurd (lt_min he h) ht
        · omega
      have e2 : x.e = P.T := by omega
      rw [e1, x.w_last hT]
      exact h3.c h2.1 e2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, exact_match_conv _ pol x hθ hC (fun t ht => ?_) fun he => ?_⟩
    · have := Finset.mem_Ico.1 ht
      exact h3 t this.1 (lt_of_lt_of_le this.2 (min_le_left _ _))
    · have := h3 (P.T - 1) (by have := h2.1; omega) (by omega)
      rwa [x.w_last hT] at this

/-! ## 3. The reply is determined by what comes before it (at exact match: `RinfS0`; under some
valid policies it is not: no theorem of this file states it; at the all-zero index it follows from
`ProgramRGuards.rinfR_zero_iff` at cap = 1 (`xAll`, `xOne`)) -/

/-- two tokens of gap 0 under the same logits are the same token -/
theorem argmin_unique {V : ℕ} {l : ℕ → ℤ} {w w' : ℕ} (hw : w < V) (hw' : w' < V)
    (h : gapOf V l w = 0) (h' : gapOf V l w' = 0) : w = w' := by
  obtain ⟨a1, a2⟩ := (gapOf_eq_zero_iff V l hw).1 h
  obtain ⟨b1, b2⟩ := (gapOf_eq_zero_iff V l hw').1 h'
  rcases Nat.lt_trichotomy w w' with c | c | c
  · exact absurd (a1 w' hw') (not_le.2 (b2 w c))
  · exact c
  · exact absurd (b1 w hw) (not_le.2 (a2 w' c))

/-- For two members of `RinfS0` at one index: the tokens 0 .. r, with r and e, determine the tokens
up to number e (x_T := y): at most one stretch follows x_0 .. x_r. For `RinfS0`, the relation
without `Head3`. -/
theorem reply_unique (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (i : Index P) (x x' : Instance P) (hr : x.r = x'.r) (he : x.e = x'.e)
    (h : RinfS0 P κ nf tbs i x) (h' : RinfS0 P κ nf tbs i x') (h0 : ∀ t ≤ x.r, x.tok t = x'.tok t) :
    ∀ t ≤ x.e, x.tok t = x'.tok t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hte
    by_cases htr : t ≤ x.r
    · exact h0 t htr
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hs1 : x.r ≤ s := by omega
      have hs2 : s < x.e := by omega
      have hp : ∀ u (hu : u < P.T),
          u ≤ s → x.prompt ⟨u, hu⟩ = x'.prompt ⟨u, hu⟩ := fun u hu hus => by
        have := ih u (by omega) (by omega)
        unfold Instance.tok at this
        rw [dif_pos hu, dif_pos hu] at this
        exact Fin.ext this
      have g := h.2 s hs1 hs2
      have g' := h'.2 s (hr ▸ hs1) (he ▸ hs2)
      rw [← lgK_causal P κ nf tbs i.val hp (le_refl s)] at g'
      exact argmin_unique (x.w_lt s) (x'.w_lt s) g g'

/-! ## 4. A reply none of whose tokens is the first choice -/

/-- If all counted positions have one cost k ≤ C, θ, and y has gap 0 at the last if e = T, the
policy holds. -/
theorem polOK_of_const {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (k : ℤ)
    (hk : ∀ t ∈ x.cnt, costOf lg x t = k) (hC : k ≤ pol.C) (hθ : k ≤ pol.theta)
    (hc : x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0) : PolOK lg pol x := by
  refine ⟨?_, ?_, fun _ => hc⟩
  · have hs : ∑ t ∈ x.cnt, min (costOf lg x t) (pol.C : ℤ) = ∑ _t ∈ x.cnt, k :=
      Finset.sum_congr rfl fun t ht => by rw [hk t ht, min_eq_left hC]
    rw [hs, Finset.sum_const, x.card_cnt, nsmul_eq_mul, mul_comm (x.NB : ℤ) k]
    exact mul_le_mul_of_nonneg_right hθ (Int.natCast_nonneg _)
  · have hf : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t) = ∅ :=
      Finset.filter_false_of_mem fun t ht => by rw [hk t ht]; exact not_lt.2 hC
    rw [hf]
    exact Nat.zero_le _

/-- all tokens 1, r = 0, e = 1,023, y = 0 -/
def x1 : Instance ppref :=
  ⟨fun _ => ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1023, by decide⟩⟩
theorem nb_x1 : x1.NB = 1023 := by decide
theorem x1_w {t : ℕ} (ht : t ∈ x1.cnt) : x1.w t = 1 := by
  have h2 : t < 1023 := by
    have := (Finset.mem_Ico.1 ht).2
    exact lt_of_lt_of_le this (min_le_left _ _)
  unfold Instance.w Instance.tok
  rw [dif_pos (show t + 1 < ppref.T by show t + 1 < 1024; omega)]
  rfl

/-- A policy that is not exact match admits what exact match rejects: at valid settings and the
all-zero index, a reply none of whose 1,023 tokens is the first choice (each gap is 1, each cost
2^8 + 1) is in the relation at (C, θ, cap) = (512, 2^8 + 1, 0), and not at exact match. -/
theorem budget {pp : ScalesAndPolicy} (h : Lawful pp) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨512, 257, 0⟩ iZero x1 ∧
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) AcceptancePolicy.exact iZero x1 := by
  refine ⟨⟨runs_iZero h _,
      ⟨by decide, by decide, fun _ => rfl⟩,
      polOK_of_const _ _ _ 257 (fun t ht => ?_) (by norm_num)
        (by norm_num) (fun e => absurd e (by decide))⟩,
    zero_range_not pp x1 (t := 0) (Nat.zero_le _) (by decide) (by decide)⟩
  rw [cost_zero, x1_w ht]
  norm_num

/-! ## 5. The relation at given settings reads their policy -/

/-- the reference settings with the limit cap = 1; with the clip 300 and the mean 2^8 + 1 -/
def ppCap : ScalesAndPolicy := { ppRef with pol := ⟨256, 256, 1⟩ }
def ppMean : ScalesAndPolicy := { ppRef with pol := ⟨300, 257, 0⟩ }

theorem ppCap_lawful : Lawful ppCap :=
  ⟨⟨lawful_ref.ff, lawful_ref.sh, lawful_ref.one, lawful_ref.nf, by decide⟩, lawful_ref.km⟩
theorem ppMean_lawful : Lawful ppMean :=
  ⟨⟨lawful_ref.ff, lawful_ref.sh, lawful_ref.one, lawful_ref.nf, by decide⟩, lawful_ref.km⟩

/-- Two valid settings that differ only in the policy can have different relations (shown of three
named settings: `xOne` at the all-zero index is in `RinfPP ppCap` and `RinfPP ppMean` and not in
`RinfPP ppRef`; it is no general rule: under every policy of exact match the relation is the same,
`rinfR_iff_rinfS` above). -/
theorem tables_differ_in_policy :
    (ppCap.w = ppRef.w ∧ ppCap.nf = ppRef.nf ∧ ppMean.w = ppRef.w ∧ ppMean.nf = ppRef.nf) ∧
    RinfPP ppCap iZero xOne ∧
    RinfPP ppMean iZero xOne ∧
    ¬ RinfPP ppRef iZero xOne :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, one_cap ppCap_lawful, one_mean ppMean_lawful, one_not_exact lawful_ref⟩

end Inst.Model.RequestGuards2
