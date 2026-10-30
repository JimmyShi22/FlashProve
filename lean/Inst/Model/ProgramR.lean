-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgramR.lean: the relations on a request: a stretch of a reply under an acceptance
policy (`RinfR`), and at exact match (`RinfS`).

A request (`Instance`, Inst/Model/Program.lean) is T tokens, an announced token y and two numbers r,
e. The covered positions are r ≤ t < e; the checked token of position t is token t + 1, and y at the
last position; the counted positions are the covered ones below T − 1. For logits l, the gap of a
token w is max over v of l[v] − l[w] + [v < w] (`gapOf`); it is 0 exactly at the least token of
largest logit. The cost of a position is its checked token's gap + 2^8 (`costOf`). A policy (`AcceptancePolicy`)
is three numbers: the clip C, the bound theta on the mean cost, the limit cap.

`RinfR` says: the integer program runs on the tokens (`RunsK`: no range condition fails), the
request has its form (`Head3`: r < e ≤ T, and y = 0 if e < T), and `PolOK` holds: (a) the costs of
the counted positions, each clipped at C, sum to at most theta times their number; (b) at most cap
of them cost more than C; (c) if r < e = T, then y has gap 0 at the last position. `RinfS` says: the
program runs, the request has its form, and the checked token has gap 0 at every covered position.
By `RinfS_iff_exact`, for T > 0, `RinfS` is `RinfR` at the policy `AcceptancePolicy.exact`, C = theta = 2^8 and
cap = 0. At given settings `RinfR` is `RinfPP` (Inst/Model/Scales.lean); outside Inst/Model/
`RinfPP` is named in Policy/Rel/LedgerRelLaws.lean (`Spec.ledger_lang`).

Sanity lemmas: for T > 0, at r = T − 1, e = T, `RinfR` is `RinfK`, "y is the next token", whatever
the policy (`RinfR_next`); at theta = 2^8 and (cap = 0 or C > 2^8), if `PolOK` holds, every counted
token has gap 0 (`exact_match`; one direction only, the converse and where it fails are in
Inst/Model/RequestGuards2.lean). More are in Inst/Model/ProgramRGuards.lean,
Inst/Model/RequestGuards.lean and Inst/Model/Causal.lean.

To audit the relation, read `AcceptancePolicy`, `Instance.tok`, `Instance.w`, `Instance.cnt`, `Instance.NB`,
`gapOf`, `costOf`, `Head3`, `PolOK`, `RinfR`, `RinfS`, `ModelS`, `RinfS0`, `AcceptancePolicy.exact`, with
`Instance`, `Instance.nextOf`, `Instance.r`, `Instance.e`, `RunsK`, `lgK` of
Inst/Model/Program.lean and `AcceptancePolicy.OK`, `ModelR`, `RinfR0` of Inst/Model/ProgramRPol.lean.

Notation: `c`, `b`: of type `ℕ → ℤ`, two of the fields of `Hid`, the six hidden numbers of a
position (Inst/Model/Head/PolicyDefs.lean).

Limits:
- The definitions follow the implementation's text at its step table (the policy lines sh = 8,
  sT = sh − 4), where cost = gap + 2^sh. That they, and this library's protocol for the output head,
  agree with the implementation's text and its verifier's source is by reading; no theorem can say
  it.
- The cost is a definition. That text's cost is the greater of gap + 2^sh and nll, the negative
  log-probability of the checked token in the unit of the logits; that at the step table the first
  is the greater rests on its own argument over the real numbers (it uses ln V < 16): no Lean file
  has it. That `costOf` is the least cost that the test on the looked-up values admits is not proved
  in this library; what is proved is `cost_le_hidden` (Inst/Model/Head/PolicySound.lean): at a
  counted position `costOf` ≤ c + 2^37 b, for hidden numbers that satisfy the head's relations, and
  2 ≤ V. Also proved: `step2` (Inst/Model/Head/PolicyHonest.lean): if 2 V ≤ 2^24, the table's values
  at gap + 2^8 add up to at most 2^24.
- sh = 8 is a constant here. The implementation's verifier admits sh = 7 as well (by a reading);
  that is not covered here. It is not the field `sh` of `Params` and `LayerScale`, the shift of
  attention's exponential.
- `AcceptancePolicy` holds any natural numbers. The implementation's conditions on them (theta ≤ C, cap ≤ T and
  the like) are in no definition here: they are `PolTests` (Inst/Model/ProgTests.lean) and the field
  `pol` of `Lawful` (Inst/Model/Scales.lean). `AcceptancePolicy.OK`, which the head's theorems assume, is wider.
- `ModelS` and `RinfS0` are `RinfS` without the form, and say less than they seem to. At e ≤ r no
  position is covered, and they say only that the program runs, whatever y is; at e < T they do not
  read y (`modelS_empty`, `modelS_y`, Inst/Model/RequestGuards.lean; for a policy `polOK_of_le`,
  `polOK_y_unread`, Inst/Model/ProgramRPol.lean). Quote them as "exact match on the stretch" only
  together with `Head3`.
- As a protocol, a counted position goes through the cost ledger (six hidden numbers for each
  position) even at exact match, in the implementation (by a reading of its text) and in
  Inst/Model/Head/ (Inst/Model/Head/Trace.lean, Inst/Model/Head/PolicyHonest.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Program
import Inst.Model.Sanity

set_option autoImplicit false

namespace Inst.Model

/-- The three numbers of the acceptance policy: the clip, the bound on the mean cost, the limit on
the number of positions above the clip. -/
structure AcceptancePolicy where
  C : ℕ
  theta : ℕ
  cap : ℕ

namespace Instance
variable {P : Params} (x : Instance P)
/-- x_t for t < T; x_T := y (and y beyond) -/
def tok (t : ℕ) : ℕ := if h : t < P.T then (x.prompt ⟨t, h⟩).val else x.y.val
/-- the checked token of position t -/
def w (t : ℕ) : ℕ := x.tok (t + 1)
/-- the counted positions: covered, and below T − 1: their checked token is a token of the
request -/
def cnt : Finset ℕ := Finset.Ico x.r (min x.e (P.T - 1))
def NB : ℕ := min x.e (P.T - 1) - x.r
theorem card_cnt : x.cnt.card = x.NB := Nat.card_Ico _ _
theorem tok_lt (t : ℕ) : x.tok t < P.V := by unfold tok; split <;> exact Fin.isLt _
theorem w_lt (t : ℕ) : x.w t < P.V := x.tok_lt _
end Instance

/-! ## The gap, the cost, the policy: for any logits -/

section Gap
variable (V : ℕ) (l : ℕ → ℤ)

/-- the logit gap of the token w: max_(v < V) (l[v] − l[w] + [v < w]) -/
def gapOf (w : ℕ) : ℤ := maxTo (fun v => l v - l w + if v < w then 1 else 0) (V - 1)

theorem gapOf_nonneg {w : ℕ} (hw : w < V) : 0 ≤ gapOf V l w := by
  have h := (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).1 w (by omega)
  simpa using h

theorem le_gapOf {w v : ℕ} (hv : v < V) : l v - l w + (if v < w then 1 else 0) ≤ gapOf V l w :=
  (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).1 v (by omega)

/-- for w < V, the gap of w is 0 exactly if w is the least token of largest logit -/
theorem gapOf_eq_zero_iff {w : ℕ} (hw : w < V) :
    gapOf V l w = 0 ↔ (∀ v < V, l v ≤ l w) ∧ ∀ v < w, l v < l w := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have := le_gapOf V l (w := w) hv
      rw [h] at this
      split at this <;> omega
    · have := le_gapOf V l (w := w) (lt_trans hv hw)
      rw [h, if_pos hv] at this
      omega
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ (gapOf_nonneg V l hw)
    obtain ⟨j, hj, e⟩ := (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).2
    unfold gapOf
    rw [← e]
    show l j - l w + (if j < w then 1 else 0) ≤ 0
    have hjV : j < V := by omega
    split
    · rename_i hjw
      have := h2 j hjw
      omega
    · have := h1 j hjV
      omega

end Gap

section Policy
variable {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)

/-- the cost of a counted position, at the step table: gap + 2^sh, sh = 8. A definition: that it is
the cost of the implementation's text at the step table is argued there over the real numbers, and
is in no Lean file (the comment at the top). -/
def costOf (t : ℕ) : ℤ := gapOf P.V (lg t) (x.w t) + 2 ^ 8

/-- the request's form: r < e ≤ T; y = 0 where no covered position reads it. (e ≤ T is given by the
type of eF already; the type admits r = T, which r < e excludes.) -/
def Head3 : Prop := x.r < x.e ∧ x.e ≤ P.T ∧ (x.e < P.T → x.y.val = 0)

/-- The policy's three clauses (a), (b), (c) of the comment at the top. -/
structure PolOK : Prop where
  a : ∑ t ∈ x.cnt, min (costOf lg x t) pol.C ≤ pol.theta * x.NB
  b : (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t).card ≤ pol.cap
  /-- the premise r < e: without a covered position nothing is tested at position T − 1 -/
  c : x.r < x.e → x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0

end Policy

/-! ## The relation -/

/-- R for a stretch of a reply: the logits are defined (no range condition fails, at all T
positions), the request has its form, and (a), (b), (c) hold of the integer program's logits. -/
def RinfR (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (i : Index P) (x : Instance P) : Prop :=
  RunsK P κ nf tbs i.val x.prompt ∧ Head3 x ∧ PolOK (lgK P κ nf tbs i.val x.prompt) pol x

/-- Exact match: every covered token is the least token of largest logit at its position, for a
request of the right form on which the program runs. As a relation, for T > 0, it is RinfR at exact
match (`RinfS_iff_exact`); as a protocol, a counted position goes through the cost ledger even at
exact match (the comment at the top). -/
def RinfS (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (i : Index P) (x : Instance P) : Prop :=
  RunsK P κ nf tbs i.val x.prompt ∧
  Head3 x ∧
  ∀ t, x.r ≤ t → t < x.e → gapOf P.V (lgK P κ nf tbs i.val x.prompt t) (x.w t) = 0

/-- Exact match without the request's form. (The same with a policy `pol` in the place of exact
match is `ModelR`, and on an index `RinfR0`: Inst/Model/ProgramRPol.lean.) The request's form
(`Head3`) is a public test of the verifier on the instance. -/
def ModelS (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (w : Weights) (x : Instance P) : Prop :=
  RunsK P κ nf tbs w x.prompt ∧
  ∀ t, x.r ≤ t → t < x.e → gapOf P.V (lgK P κ nf tbs w x.prompt t) (x.w t) = 0
def RinfS0 (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (i : Index P) (x : Instance P) : Prop :=
  ModelS P κ nf tbs i.val x
theorem RinfS_iff (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (i : Index P) (x : Instance P) :
    RinfS P κ nf tbs i x ↔ Head3 x ∧ RinfS0 P κ nf tbs i x :=
  ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
instance {P : Params} (x : Instance P) : Decidable (Head3 x) := by unfold Head3; infer_instance

/-- Sanity lemma: for T > 0, at r = T − 1, e = T, `RinfR` is the relation "y is the next token"
(RinfK), whatever the policy. -/
theorem RinfR_next (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (pol : AcceptancePolicy) (i : Index P) (x : Instance P)
    (hr : x.r = P.T - 1) (he : x.e = P.T) :
    RinfR P κ nf tbs pol i x ↔ RinfK P κ nf tbs i x := by
  have hc : x.cnt = ∅ := by
    unfold Instance.cnt
    rw [hr, he]
    exact Finset.Ico_eq_empty (by omega)
  have hN : x.NB = 0 := by rw [← x.card_cnt, hc]; rfl
  have hz := gapOf_eq_zero_iff P.V (lgK P κ nf tbs i.val x.prompt (P.T - 1)) x.y.isLt
  constructor
  · rintro ⟨h1, _, h3⟩
    have hre : x.r < x.e := by omega
    exact ⟨h1, x.y.isLt, (hz.1 (h3.c hre he)).1, (hz.1 (h3.c hre he)).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1,
      ⟨by omega, by omega, fun h => absurd h (by omega)⟩,
      ⟨?_, ?_, fun _ _ => hz.2 ⟨h2.2.1, h2.2.2⟩⟩⟩
    · rw [hc, hN]; simp
    · rw [hc]; simp

/-- Sanity lemma: if `PolOK` holds at θ = 2^8 and (cap = 0 or C > 2^8), every counted token is the
least token of largest logit at its position. -/
theorem exact_match {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)
    (hθ : pol.theta = 2 ^ 8) (hc : pol.cap = 0 ∨ 2 ^ 8 < pol.C) (h : PolOK lg pol x) :
    ∀ t ∈ x.cnt, gapOf P.V (lg t) (x.w t) = 0 := by
  have hg : ∀ t, 0 ≤ gapOf P.V (lg t) (x.w t) := fun t => gapOf_nonneg _ _ (x.w_lt t)
  have hle : pol.cap = 0 → ∀ t ∈ x.cnt, costOf lg x t ≤ pol.C := by
    intro h0 t ht
    by_contra hlt
    have hmem : t ∈ x.cnt.filter (fun t => (pol.C : ℤ) < costOf lg x t) :=
      Finset.mem_filter.2 ⟨ht, not_le.1 hlt⟩
    have h1 := Finset.card_pos.2 ⟨t, hmem⟩
    have h2 := h.b
    omega
  have hm : ∀ t ∈ x.cnt, (2 : ℤ) ^ 8 ≤ min (costOf lg x t) pol.C := by
    intro t ht
    have hc8 : (2 : ℤ) ^ 8 ≤ costOf lg x t := by unfold costOf; have := hg t; omega
    rcases hc with h0 | h1
    · rw [min_eq_left (hle h0 t ht)]; exact hc8
    · exact le_min hc8 (by exact_mod_cast le_of_lt h1)
  have hs : ∑ t ∈ x.cnt, (min (costOf lg x t) pol.C - 2 ^ 8) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, x.card_cnt, nsmul_eq_mul]
    have ha := h.a
    rw [hθ] at ha
    push_cast at ha
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun t ht => sub_nonneg.2 (hm t ht)).1
    (le_antisymm hs (Finset.sum_nonneg fun t ht => sub_nonneg.2 (hm t ht)))
  intro t ht
  have e : min (costOf lg x t) pol.C = 2 ^ 8 := by have := hz t ht; omega
  have e2 : costOf lg x t = 2 ^ 8 := by
    rcases hc with h0 | h1
    · rwa [min_eq_left (hle h0 t ht)] at e
    · rcases min_choice (costOf lg x t) (pol.C : ℤ) with h3 | h3
      · rwa [h3] at e
      · rw [h3] at e
        have : (pol.C : ℤ) = 2 ^ 8 := e
        have h4 : (2 : ℤ) ^ 8 < pol.C := by exact_mod_cast h1
        omega
  unfold costOf at e2
  omega

/-- Sanity lemma: for T > 0, on the request "the next token after these T tokens" the inner relation
of exact match (`ModelS`) is `ModelIsK`: Model_i(prompt) = y. -/
theorem ModelS_nextOf (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (w : Weights) (prompt : Fin P.T → Fin P.V) (y : Fin P.V) :
    ModelS P κ nf tbs w (Instance.nextOf prompt y) ↔ ModelIsK P κ nf tbs w prompt y.val := by
  have hw : (Instance.nextOf prompt y).w (P.T - 1) = y.val := by
    unfold Instance.w Instance.tok
    rw [dif_neg (by omega)]
    rfl
  have hz := gapOf_eq_zero_iff P.V (lgK P κ nf tbs w prompt (P.T - 1)) y.isLt
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := h2 (P.T - 1) (le_refl _) (show P.T - 1 < P.T by omega)
    rw [hw] at h3
    exact ⟨h1, y.isLt, (hz.1 h3).1, (hz.1 h3).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t hr he => ?_⟩
    have e : t = P.T - 1 := by
      have h1' : P.T - 1 ≤ t := hr
      have h2' : t < P.T := he
      omega
    rw [e, hw]
    exact hz.2 ⟨h2.2.1, h2.2.2⟩
theorem head3_nextOf {P : Params} (hT : 0 < P.T) (prompt : Fin P.T → Fin P.V) (y : Fin P.V) :
    Head3 (Instance.nextOf prompt y) :=
  ⟨show P.T - 1 < P.T by omega, le_refl _, fun h => absurd h (lt_irrefl _)⟩

/-- The policy of exact match: C = θ = 2^8, cap = 0. -/
def AcceptancePolicy.exact : AcceptancePolicy := ⟨2 ^ 8, 2 ^ 8, 0⟩

/-- for T > 0, the checked token of the last position is the announced token -/
theorem Instance.w_last {P : Params} (x : Instance P) (hT : 0 < P.T) : x.w (P.T - 1) = x.y.val := by
  unfold Instance.w Instance.tok
  rw [dif_neg (by omega)]

/-- For T > 0, `RinfS` is `RinfR` at the policy `AcceptancePolicy.exact`. -/
theorem RinfS_iff_exact (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (i : Index P) (x : Instance P) :
    RinfS P κ nf tbs i x ↔ RinfR P κ nf tbs AcceptancePolicy.exact i x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hc : ∀ t ∈ x.cnt, costOf (lgK P κ nf tbs i.val x.prompt) x t = 2 ^ 8 := fun t ht => by
      have := Finset.mem_Ico.1 ht
      unfold costOf
      rw [h3 t this.1 (lt_of_lt_of_le this.2 (min_le_left _ _)), zero_add]
    refine ⟨h1, h2, ⟨?_, ?_, fun _ he => ?_⟩⟩
    · rw [Finset.sum_congr rfl fun t ht => by rw [hc t ht], Finset.sum_const,
        x.card_cnt, nsmul_eq_mul]
      show (x.NB : ℤ) * min (2 ^ 8) ((2 ^ 8 : ℕ) : ℤ) ≤ ((2 ^ 8 : ℕ) : ℤ) * x.NB
      push_cast
      rw [min_self, mul_comm]
    · have hf : (x.cnt.filter fun t =>
            ((AcceptancePolicy.exact.C : ℕ) : ℤ) < costOf (lgK P κ nf tbs i.val x.prompt) x t) = ∅ :=
        Finset.filter_false_of_mem fun t ht => by
          rw [hc t ht]
          show ¬ (((2 ^ 8 : ℕ) : ℤ) < 2 ^ 8)
          norm_num
      rw [hf]
      exact Nat.zero_le _
    · have := h3 (P.T - 1) (by have := h2.1; omega) (by omega)
      rwa [x.w_last hT] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun t hr he => ?_⟩
    by_cases ht : t < min x.e (P.T - 1)
    · exact exact_match _ AcceptancePolicy.exact x rfl (Or.inl rfl) h3 t (Finset.mem_Ico.2 ⟨hr, ht⟩)
    · have hle := h2.2.1
      have e1 : t = P.T - 1 := by
        rcases Nat.lt_or_ge t (P.T - 1) with h | h
        · exact absurd (lt_min he h) ht
        · omega
      have e2 : x.e = P.T := by omega
      rw [e1, x.w_last hT]
      exact h3.c h2.1 e2

end Inst.Model
