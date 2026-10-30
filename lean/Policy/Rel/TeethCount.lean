-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/TeethCount.lean

A guard on "true under a policy" (`IsTrueUnder`, Policy/Rel/True.lean): each of a policy's three
numbers (C, θ, cap) alone can decide a request. Each theorem names two policies that differ in one
number, and one request at one index that is true under the one and not under the other. In
particular clause (b), the count, refuses a request that clause (a), the mean, admits, at policies
with θ < C, which Policy/Rel/Teeth.lean does not show.

At the weights `wtsAB a b` of Policy/Rel/Teeth.lean the logits are the same for every prompt and
position (`lg_wtsAB`), so the cost of a position depends on its checked token alone. Token 0 costs
k = 2^8 + 2,047 (a + b). Token 1 costs 2^8 if 1 ≤ a: it is then the first choice. In the request
`xMiss m` the tokens x_1 .. x_m are 0 and all others 1, with r = 0, e = 1,023, y = 0. For m ≤ 1,023
it has m counted positions at the cost k and 1,023 - m at the cost 2^8.

Main names:
* `xMiss_w`, `gap_one`, `cost_xMiss`: the checked tokens, the gap of token 1, the cost of a
  position.
* `xMiss_iff`: for 1 ≤ a, 2^8 ≤ C and m ≤ 1,023, `xMiss m` is true under a policy if and only if
  m min(k, C) + (1,023 - m) 2^8 ≤ 1,023 θ, and m ≤ cap if C < k. `xMiss_iTeeth_iff`: the same at the
  index `iTeeth` and C < 16,767,233, in natural numbers.
* `cap_alone_decides`, `theta_alone_decides`, `C_alone_decides`: see their docstrings. Each has
  hypotheses on the policy's numbers; none holds for every policy.

Limits: those of Policy/Rel/Teeth.lean (made-up weights with the same logits at every position; the
reference scales alone; nothing at a trained model; nothing on a protocol, a prover or a verifier;
the clauses and the cost, a gap plus 2^8, are this library's definitions, and that they are what the
programs test is no theorem: the head of Inst/Model/ProgramR.lean). Further: the costly tokens stand
at the start of the request. Nothing is shown on where in a reply a costly token may stand.

Terms: lean/GLOSSARY.md.

-/
import Policy.Rel.Teeth
noncomputable section

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.Teeth

open Inst.Model Inst.Model.SanityRef Inst.Model.ProgramRGuards Inst.Model.RequestGuards2

/-! ## 1. A request with m costly positions -/

/-- The tokens x_1 .. x_m are 0, all others 1; y = 0, r = 0, e = 1,023. -/
def xMiss (m : ℕ) : Instance ppref :=
  ⟨fun t => if 1 ≤ t.val ∧ t.val ≤ m then ⟨0, by decide⟩ else ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨1023, by decide⟩⟩

/-- The counted positions are 0 .. 1,022. -/
theorem cnt_xMiss (m : ℕ) : (xMiss m).cnt = Finset.Ico 0 1023 := rfl

theorem nb_xMiss (m : ℕ) : (xMiss m).NB = 1023 := rfl

/-- A position t < 1,023 checks token 0 if t < m, and token 1 otherwise. -/
theorem xMiss_w {m t : ℕ} (ht : t < 1023) : (xMiss m).w t = if t < m then 0 else 1 := by
  unfold Instance.w Instance.tok
  rw [dif_pos (show t + 1 < ppref.T by show t + 1 < 1024; omega)]
  show ((if 1 ≤ t + 1 ∧ t + 1 ≤ m then (⟨0, by decide⟩ : Fin ppref.V)
    else ⟨1, by decide⟩) : Fin ppref.V).val = _
  by_cases c : t < m
  · rw [if_pos ⟨by omega, by omega⟩, if_pos c]
  · rw [if_neg (fun h => c (by omega)), if_neg c]

/-- Under the logits of `lg_wtsAB`, for a, b with `Votes` and 1 ≤ a (the hypothesis `ha`), token 1
is the first choice: its gap is 0. -/
theorem gap_one {a b : ℤ} (h : Votes a b) (ha : 1 ≤ a) {l : ℕ → ℤ}
    (hl : ∀ v < ppref.V, l v = if v = 1 then 2047 * a else if v = 0 then -(2047 * b) else 0) :
    gapOf ppref.V l 1 = 0 := by
  obtain ⟨-, -, b0, -⟩ := h
  have l1 : l 1 = 2047 * a := by rw [hl 1 (by decide), if_pos rfl]
  refine (gapOf_eq_zero_iff ppref.V l (by decide)).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [l1, hl v hv]
    split_ifs <;> omega
  · obtain rfl : v = 0 := by omega
    rw [l1, hl 0 (by decide), if_neg (by norm_num), if_pos rfl]
    omega

/-- For a, b with `Votes` and 1 ≤ a: a position t < 1,023 of `xMiss m` costs 2^8 + 2,047 (a + b) if
t < m, and 2^8 otherwise. -/
theorem cost_xMiss {a b : ℤ} (h : Votes a b) (ha : 1 ≤ a) {m t : ℕ} (ht : t < 1023) :
    costOf (lg ppref tbRef (wtsAB a b) (xMiss m).prompt) (xMiss m) t =
      if t < m then 2 ^ 8 + 2047 * (a + b) else 2 ^ 8 := by
  have hT : t < ppref.T := by show t < 1024; omega
  unfold costOf
  rw [xMiss_w ht]
  split
  · rw [gap_zero h (fun v hv => lg_wtsAB a b _ t hT hv), add_comm]
  · rw [gap_one h ha (fun v hv => lg_wtsAB a b _ t hT hv), zero_add]

/-- Hypotheses: a, b meet `Votes`, 1 ≤ a, 2^8 ≤ C, m ≤ 1,023. With k = 2^8 + 2,047 (a + b): `xMiss
m` is true under the policy if and only if m min(k, C) + (1,023 - m) 2^8 ≤ 1,023 θ (clause (a)), and
m ≤ cap if C < k (clause (b)). Clause (c) asks nothing, since e = 1,023. -/
theorem xMiss_iff {a b : ℤ} (h : Votes a b) (ha : 1 ≤ a) (pol : AcceptancePolicy) (hC : 2 ^ 8 ≤ pol.C) {m : ℕ}
    (hm : m ≤ 1023) :
    IsTrueUnder Cm.sRef pol (idxAB h) (xMiss m) ↔
      (m : ℤ) * min (2 ^ 8 + 2047 * (a + b)) (pol.C : ℤ) + (1023 - m : ℤ) * 2 ^ 8 ≤
        (pol.theta : ℤ) * 1023 ∧
      ((pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b) → m ≤ pol.cap) := by
  have hC' : (2 : ℤ) ^ 8 ≤ (pol.C : ℤ) := by exact_mod_cast hC
  have h3 : Head3 (xMiss m) :=
    ⟨show 0 < 1023 by norm_num, show 1023 ≤ 1024 by norm_num, fun _ => rfl⟩
  have hlt : ∀ t ∈ Finset.Ico 0 1023, t < 1023 := fun t ht => (Finset.mem_Ico.1 ht).2
  have hs : ∑ t ∈ (xMiss m).cnt,
      min (costOf (lg ppref tbRef (wtsAB a b) (xMiss m).prompt) (xMiss m) t) (pol.C : ℤ) =
      (m : ℤ) * min (2 ^ 8 + 2047 * (a + b)) (pol.C : ℤ) + (1023 - m : ℤ) * 2 ^ 8 := by
    rw [cnt_xMiss, ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) hm,
      Finset.sum_congr rfl (fun t ht => by
        rw [cost_xMiss h ha (lt_of_lt_of_le (Finset.mem_Ico.1 ht).2 hm),
          if_pos (Finset.mem_Ico.1 ht).2]),
      Finset.sum_congr (s₁ := Finset.Ico m 1023) rfl (fun t ht => by
        rw [cost_xMiss h ha (Finset.mem_Ico.1 ht).2,
          if_neg (not_lt.2 (Finset.mem_Ico.1 ht).1), min_eq_left hC']),
      Finset.sum_const, Finset.sum_const, Nat.card_Ico, Nat.card_Ico, nsmul_eq_mul, nsmul_eq_mul,
      Nat.sub_zero, Nat.cast_sub hm]
    norm_num
  have hb : ((xMiss m).cnt.filter fun t => (pol.C : ℤ) <
      costOf (lg ppref tbRef (wtsAB a b) (xMiss m).prompt) (xMiss m) t).card ≤ pol.cap ↔
      ((pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b) → m ≤ pol.cap) := by
    rw [cnt_xMiss]
    by_cases c : (pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b)
    · have e : (Finset.Ico 0 1023).filter (fun t => (pol.C : ℤ) <
          costOf (lg ppref tbRef (wtsAB a b) (xMiss m).prompt) (xMiss m) t) = Finset.Ico 0 m := by
        ext t
        rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
        constructor
        · rintro ⟨⟨-, h1⟩, h2⟩
          rw [cost_xMiss h ha h1] at h2
          by_contra hn
          rw [if_neg (fun x => hn ⟨Nat.zero_le _, x⟩)] at h2
          exact absurd h2 (not_lt.2 hC')
        · rintro ⟨-, h1⟩
          have h2 : t < 1023 := lt_of_lt_of_le h1 hm
          exact ⟨⟨Nat.zero_le _, h2⟩, by rw [cost_xMiss h ha h2, if_pos h1]; exact c⟩
      rw [e, Nat.card_Ico, Nat.sub_zero]
      exact ⟨fun x _ => x, fun x => x c⟩
    · rw [Finset.filter_false_of_mem fun t ht => by
        rw [cost_xMiss h ha (hlt t ht)]
        split
        · exact c
        · exact not_lt.2 hC']
      exact ⟨fun _ x => absurd x c, fun _ => Nat.zero_le _⟩
  rw [true_iff h]
  constructor
  · rintro ⟨-, hp⟩
    have ha' := hp.a
    rw [hs, nb_xMiss] at ha'
    exact ⟨by exact_mod_cast ha', hb.1 hp.b⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h3, ⟨?_, hb.2 h2, fun _ e => absurd (show 1023 = 1024 from e) (by norm_num)⟩⟩
    rw [hs, nb_xMiss]
    exact_mod_cast h1

/-- `xMiss_iff` at the index `iTeeth`, where k = 16,767,233, under the hypotheses 2^8 ≤ C <
16,767,233 and m ≤ 1,023, in natural numbers: m C + (1,023 - m) 2^8 ≤ 1,023 θ, and m ≤ cap. -/
theorem xMiss_iTeeth_iff (pol : AcceptancePolicy) (hC0 : 2 ^ 8 ≤ pol.C) (hC : pol.C < 16767233) {m : ℕ}
    (hm : m ≤ 1023) :
    IsTrueUnder Cm.sRef pol iTeeth (xMiss m) ↔
      m * pol.C + (1023 - m) * 2 ^ 8 ≤ pol.theta * 1023 ∧ m ≤ pol.cap := by
  have hC' : (pol.C : ℤ) < 16767233 := by exact_mod_cast hC
  have key : m * pol.C + (1023 - m) * 2 ^ 8 ≤ pol.theta * 1023 ↔
      (m : ℤ) * (pol.C : ℤ) + (1023 - m : ℤ) * 2 ^ 8 ≤ (pol.theta : ℤ) * 1023 := by
    rw [← Nat.cast_le (α := ℤ)]
    push_cast [Nat.cast_sub hm]
    exact Iff.rfl
  unfold iTeeth
  rw [xMiss_iff _ (by norm_num) pol hC0 hm, cost_number, min_eq_right (le_of_lt hC'), key]
  exact ⟨fun x => ⟨x.1, x.2 hC'⟩, fun x => ⟨x.1, fun _ => x.2⟩⟩

/-! ## 2. Two policies that differ in one number -/

/-- **cap alone decides.** Hypotheses: 2^8 ≤ C < 16,767,233, cap < 1,023, and `room`: cap + 1 costs
of C and 1,022 - cap costs of 2^8 add up to at most 1,023 θ. Then at `iTeeth` the request with
cap + 1 costly positions is not true under (C, θ, cap) and is true under (C, θ, cap + 1). The two
policies have the same clause (a), so it is clause (b) that refuses. The request with cap costly
positions is true under (C, θ, cap). -/
theorem cap_alone_decides (pol : AcceptancePolicy) (hC0 : 2 ^ 8 ≤ pol.C) (hC : pol.C < 16767233)
    (hcap : pol.cap < 1023)
    (room : (pol.cap + 1) * pol.C + (1022 - pol.cap) * 2 ^ 8 ≤ pol.theta * 1023) :
    ¬ IsTrueUnder Cm.sRef pol iTeeth (xMiss (pol.cap + 1)) ∧
      IsTrueUnder Cm.sRef ⟨pol.C, pol.theta, pol.cap + 1⟩ iTeeth (xMiss (pol.cap + 1)) ∧
      IsTrueUnder Cm.sRef pol iTeeth (xMiss pol.cap) := by
  have e0 : 1023 - (pol.cap + 1) = 1022 - pol.cap := by omega
  refine ⟨fun t => ?_, ?_, ?_⟩
  · have := ((xMiss_iTeeth_iff pol hC0 hC (by omega)).1 t).2
    omega
  · exact (xMiss_iTeeth_iff ⟨pol.C, pol.theta, pol.cap + 1⟩ hC0 hC (by omega)).2
      ⟨by rw [e0]; exact room, le_refl _⟩
  · refine (xMiss_iTeeth_iff pol hC0 hC (le_of_lt hcap)).2 ⟨?_, le_refl _⟩
    have e1 : (pol.cap + 1) * pol.C = pol.cap * pol.C + pol.C := by ring
    have e2 : 1023 - pol.cap = (1022 - pol.cap) + 1 := by omega
    rw [e1] at room
    rw [e2]
    omega

/-- **θ alone decides.** Hypotheses: a, b meet `Votes`, and θ < k ≤ theta' ≤ C for the cost
k = 2^8 + 2,047 (a + b). Then at `idxAB h` the request `xTeeth`, whose 1,023 counted positions all
cost k, is not true under (C, θ, cap) and is true under (C, theta', cap). The two policies have the
same clause (b), so it is clause (a) that refuses. -/
theorem theta_alone_decides {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) {theta' : ℕ}
    (hθ : (pol.theta : ℤ) < 2 ^ 8 + 2047 * (a + b))
    (hθ' : 2 ^ 8 + 2047 * (a + b) ≤ (theta' : ℤ)) (hC : theta' ≤ pol.C) :
    ¬ IsTrueUnder Cm.sRef pol (idxAB h) xTeeth ∧
      IsTrueUnder Cm.sRef ⟨pol.C, theta', pol.cap⟩ (idxAB h) xTeeth := by
  have h1 : pol.theta < pol.C := by
    have : (pol.theta : ℤ) < (theta' : ℤ) := lt_of_lt_of_le hθ hθ'
    exact lt_of_lt_of_le (by exact_mod_cast this) hC
  exact ⟨teeth_mean h pol h1 hθ _ _ (by decide),
    passes h ⟨pol.C, theta', pol.cap⟩ hθ' hC _ _ (by decide) (by decide)⟩

/-- **C alone decides.** Hypotheses: 2^8 ≤ C, 1 ≤ cap, `room`: one cost of C and 1,022 of 2^8 add up
to at most 1,023 θ; C' < 16,767,233, and `tight`: one cost of C' and 1,022 of 2^8 add up to more
than 1,023 θ. Then at `iTeeth` the request with one costly position is true under (C, θ, cap) and
not true under (C', θ, cap): the larger clip lets more of the one cost into the mean. -/
theorem C_alone_decides (pol : AcceptancePolicy) (hC0 : 2 ^ 8 ≤ pol.C) (hcap : 1 ≤ pol.cap)
    (room : pol.C + 1022 * 2 ^ 8 ≤ pol.theta * 1023) {C' : ℕ} (hC' : C' < 16767233)
    (tight : pol.theta * 1023 < C' + 1022 * 2 ^ 8) :
    IsTrueUnder Cm.sRef pol iTeeth (xMiss 1) ∧
      ¬ IsTrueUnder Cm.sRef ⟨C', pol.theta, pol.cap⟩ iTeeth (xMiss 1) := by
  refine ⟨(xMiss_iTeeth_iff pol hC0 (by omega) (by norm_num)).2 ⟨by omega, hcap⟩, fun t => ?_⟩
  have := ((xMiss_iTeeth_iff ⟨C', pol.theta, pol.cap⟩ (show 2 ^ 8 ≤ C' by omega) hC'
    (by norm_num)).1 t).1
  have t' : 1 * C' + (1023 - 1) * 2 ^ 8 ≤ pol.theta * 1023 := this
  omega

end Policy.Teeth
