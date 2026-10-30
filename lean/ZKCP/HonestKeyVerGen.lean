-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/HonestKeyVerGen.lean: under the hypotheses below, V itself is an adversarial verifier: so where
hiding still holds at V's own number of queries, Pr [ V accepts (x, π) | honest key for i0 ] ≤ Pr [
.. for i1 ] + 2 ζ(q, 0) (`Spec.ver_selfDist`): no scheme whose honest proofs are all one value can
be complete, sound under honest keys and hiding there.

This file is about the verifier V of a commit-and-prove argument in the random oracle model: what a
bound on the number of V's oracle queries implies.
Definitions, statements (in `Spec`) and proofs. For every relation and every scheme of
ZKCP/Defs.lean: no protocol is named; few imports on purpose (behind the model's modules Lean does
not elaborate these generic lemmas within its limits). Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.

Main names:
  `Spec.ver_selfDist`: V draws no coin and asks at most q queries on the fixed pair (x, π); privacy
    with any simulator S and bound ζ at i0 (environment Z0) and at i1 (Z1); pp i0 = pp i1 ⇒ Pr [ V
    accepts (x, π) | honest key for i0 ] ≤ Pr [ .. for i1 ] + 2 ζ(q, 0).
  `Spec.ver_const`: pp i0 = pp i1; completeness error α; the stronger privacy with some simulator at
    ζ; x true at i0 with witness w; `VerConst A i0 x w π0`; under an honest key for i1 V accepts (x,
    π0) with chance at most β; V: no coin, at most q queries ⇒ 1 ≤ α + β + 2 ζ(q, 0).
  Spec.ver_constNote the same from the definition in the form of the work that this protocol builds
    on (lean/CREDITS.md, "Further work"; IsZKCPArg); it asks something true at i1 too
  `Spec.ver_keyWrong`: x false at i1 ⇒ Pr [ V accepts (x, π0) | honest key for i1 ] ≤ the chance
    that `wrongExp` (ZKCP/HonestKey.lean), with the prover that returns (x, π0), ends accepted on an
    instance outside L(i1).
  `Spec.ver_constNamed`: pp i0 = pp i1; the definition in its named form at (α, ε, ζ); "from an
    honest key the extractor gives back the index" at δ; x true at i0 and false at i1;
    `VerConst A i0 x w π0`; C(i1) asks at most tC queries; V: no coin, at most q ⇒ 1 ≤ α + (δ +
    ε(tC, 0)) + 2 ζ(q, 0).

Why `VerConst` has this form: to ask that the prover be the algorithm "return π0" is an equation of
algorithms, which any prover that asks or draws something idle escapes, and which is refuted for
free of any prover that begins with a draw. Here constancy is asked of what the prover puts out.

Limits: how to read the statements above. In the random oracle model what V computes is beside the
point; what it asks is the point. The number of sessions in ζ(q, 0) is 0: the adversary that is
built asks for no proof.
This file says nothing for a V with coins, but for `Spec.ver_keyWrong`. (The built verifier signals
V's bit by one draw; with coins in V the bit would have to be replayed from the view.) "The honest
proofs of one true request under honest keys for one index are all one value" is the one kind of
triviality that is shut out: nothing on short proofs, on proofs that take two values, on what V
computes. This file does not say that any scheme meets the premises.
-/
import ZKCP.Main
import ZKCP.ManyOfOne
import ZKCP.HonestKey

set_option autoImplicit false

namespace TopC
open ZKCP
open scoped ENNReal

section
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- run a Boolean oracle algorithm as an adversarial verifier; say "true" by one draw from a set of
one -/
def verAdv : OComp lam Bool → AdvVerifier lam X Pf
  | .pure b => if b then .sample 0 (fun _ => .halt) else .halt
  | .query q k => .query q fun r => verAdv (k r)
  | .sample n k => .sample n fun r => verAdv (k r)

/-- V's verdict on a fixed pair (x, π) under an honest key for i -/
def verKey (A : Arg lam I X W IVK ISK Pf) (i : I) (x : X) (π : Pf) : OComp lam Bool :=
  (A.C i).bind fun k => A.V k.1 x π

/-- the honest proofs of (x, w) under honest keys for i are all the one value π0: of what is put
out, not of the algorithm -/
def VerConst (A : Arg lam I X W IVK ISK Pf) (i : I) (x : X) (w : W) (π0 : Pf) : Prop :=
  ∀ f : Oracle lam, ∀ k ∈ ((A.C i).run f).support, ∀ π ∈ ((A.P k.2 x w).run f).support, π = π0

end

namespace Spec

/-- Under the hypotheses below, V itself is a distinguisher -/
def ver_selfDist : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (i0 i1 : I),
    R.pp i0 = R.pp i1 →
    ∀ (Z0 Z1 : ViewEnv lam IVK X W Pf), PrivacyFor R A S ζ i0 Z0 → PrivacyFor R A S ζ i1 Z1 →
      ∀ (x : X) (π : Pf) (q : ℕ), (∀ ivk, (A.V ivk x π).QueryBound q) →
        (∀ ivk, (A.V ivk x π).DrawsNoCoin) →
        Pr (verKey A i0 x π) (fun _ => {b | b = true}) ≤
          Pr (verKey A i1 x π) (fun _ => {b | b = true}) + (ζ q 0 + ζ q 0)

/-- honest proofs that are all one value, from completeness and the stronger privacy (not all
hypotheses are named here: see the statement below) -/
def ver_const : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (S : Simulator lam PP IVK X Pf)
      (α β : ℝ≥0∞) (ζ : ℕ → ℕ → ℝ≥0∞),
    HasCompletenessError R A α → HasStrongIndexPrivacyWith R A S ζ →
    ∀ (π0 : Pf) (i0 i1 : I), R.pp i0 = R.pp i1 →
      ∀ (x : X) (w : W), R.rel i0 x w → VerConst A i0 x w π0 →
        Pr (verKey A i1 x π0) (fun _ => {b | b = true}) ≤ β →
        ∀ q : ℕ, (∀ ivk, (A.V ivk x π0).QueryBound q) →
          (∀ ivk, (A.V ivk x π0).DrawsNoCoin) → 1 ≤ α + β + (ζ q 0 + ζ q 0)

/-- the same from the definition in the form of the work that this protocol builds on
(lean/CREDITS.md, "Further work") -/
def ver_constNote : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (α β : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    IsZKCPArg R A α ε ζ →
    ∀ (π0 : Pf) (i0 i1 : I), R.pp i0 = R.pp i1 →
      ∀ (x : X) (w : W), R.rel i0 x w → VerConst A i0 x w π0 →
        ∀ (x1 : X) (w1 : W), R.rel i1 x1 w1 → Pr (verKey A i1 x π0) (fun _ => {b | b = true}) ≤ β →
          ∀ q : ℕ, (∀ ivk, (A.V ivk x π0).QueryBound q) →
            (∀ ivk, (A.V ivk x π0).DrawsNoCoin) → 1 ≤ α + β + (ζ q 0 + ζ q 0)

/-- V's verdict on a fixed false pair is an outcome of the honest-key experiment -/
def ver_keyWrong : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (i1 : I) (x : X) (π0 : Pf),
    (¬ ∃ w, R.rel i1 x w) →
    Pr (verKey A i1 x π0) (fun _ => {b | b = true}) ≤
      Pr (wrongExp A i1 fun _ => .pure (x, π0)) (fun _ => {o | o.1 = true ∧ o.2 ∉ R.L (some i1)})

/-- Under the hypotheses below, the named form, "i* = i" and a bound on V's own queries shut out
honest proofs that are all one value, where the index matters -/
def ver_constNamed : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : IndexedRelation I X W PP)
      (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf)
      (S : Simulator lam PP IVK X Pf) (α δ : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    IsZKCPArgWith R A E S α ε ζ → HasExtractionError A E δ →
    ∀ (π0 : Pf) (i0 i1 : I), R.pp i0 = R.pp i1 →
      ∀ (x : X) (w : W), R.rel i0 x w → VerConst A i0 x w π0 → (¬ ∃ w, R.rel i1 x w) →
        ∀ tC : ℕ, (A.C i1).QueryBound tC →
          ∀ q : ℕ, (∀ ivk, (A.V ivk x π0).QueryBound q) →
            (∀ ivk, (A.V ivk x π0).DrawsNoCoin) → 1 ≤ α + (δ + ε tC 0) + (ζ q 0 + ζ q 0)

end Spec

section
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

theorem verAdv_qb :
    ∀ (m : OComp lam Bool) (t : ℕ), m.QueryBound t → (verAdv (X := X) (Pf := Pf) m).QueryBound t
  | .pure b, t, _ => by cases b <;> simp [verAdv, AdvVerifier.QueryBound]
  | .query _ _, 0, h => h.elim
  | .query _ k, t + 1, h => fun r => verAdv_qb (k r) t (h r)
  | .sample _ k, t, h => fun r => verAdv_qb (k r) t (h r)

theorem verAdv_real (A : Arg lam I X W IVK ISK Pf) (Z : ViewEnv lam IVK X W Pf)
    (isk : ISK) (f : Oracle lam) :
    ∀ (m : OComp lam Bool), m.DrawsNoCoin →
      ∀ (n : ℕ) (v : View lam IVK X Pf), v.coins = [] →
        prob ((realLoop A Z isk (verAdv m) n v).run f) {v' | v'.coins ≠ []} =
          prob (m.run f) {b | b = true}
  | .pure true, _, n, v, hv => by
      show prob ((PMF.uniformOfFintype (Fin (0 + 1))).bind fun r =>
            PMF.pure { v with coins := v.coins ++ [r.val] }) _ =
        prob (PMF.pure true) _
      rw [prob_bind, prob_pure]
      simp [prob_pure, expect_const]
  | .pure false, _, n, v, hv => by
      show prob (PMF.pure v) _ = prob (PMF.pure false) _
      rw [prob_pure, prob_pure]
      simp [hv]
  | .query q k, h, n, v, hv => verAdv_real A Z isk f (k (f q)) (h (f q)) n _ hv
  | .sample _ _, h, _, _, _ => h.elim

theorem verAdv_ideal (S : Simulator lam PP IVK X Pf) (Z Z' : ViewEnv lam IVK X W Pf) :
    ∀ (m : OComp lam Bool) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop S Z (verAdv m) n v s = idealLoop S Z' (verAdv m) n v s
  | .pure true, n, v, s => rfl
  | .pure false, n, v, s => rfl
  | .query q k, n, v, s => by
      show (S.answer s q).bind _ = (S.answer s q).bind _
      exact congrArg _ (funext fun out => verAdv_ideal S Z Z' (k out.1) n _ out.2)
  | .sample m k, n, v, s => by
      show (PMF.uniformOfFintype (Fin (m + 1))).bind _ = (PMF.uniformOfFintype (Fin (m + 1))).bind _
      exact congrArg _ (funext fun r => verAdv_ideal S Z Z' (k r) n _ s)

theorem verKey_real (A : Arg lam I X W IVK ISK Pf) (Z : ViewEnv lam IVK X W Pf) (i : I) (x : X)
    (π : Pf) (hn : ∀ ivk, (A.V ivk x π).DrawsNoCoin) :
    Pr (realExp A (fun ivk => verAdv (A.V ivk x π)) Z i 0) (fun _ => {v' | v'.coins ≠ []}) =
      Pr (verKey A i x π) (fun _ => {b | b = true}) := by
  unfold Pr PrCoins
  refine congrArg _ (funext fun f => ?_)
  have e : realExp A (fun ivk => verAdv (A.V ivk x π)) Z i 0 =
      (A.C i).bind fun k => realLoop A Z k.2 (verAdv (A.V k.1 x π)) 0 ⟨k.1, [], [], []⟩ := rfl
  rw [e, verKey, run_bind, run_bind, prob_bind, prob_bind]
  exact expect_congr _ fun k => verAdv_real A Z k.2 f _ (hn k.1) 0 _ rfl

/-- a law whose outcomes are all a is the point law at a -/
theorem ver_pmfPure {α : Type} (p : PMF α) (a : α) (h : ∀ b ∈ p.support, b = a) :
    p = PMF.pure a := by
  have hs : p.support = {a} := by
    refine Set.Subset.antisymm (fun b hb => h b hb) ?_
    obtain ⟨b, hb⟩ := p.support_nonempty
    intro c hc
    rw [Set.mem_singleton_iff.1 hc, ← h b hb]
    exact hb
  ext b
  by_cases hb : b = a
  · rw [hb, (p.apply_eq_one_iff a).2 hs, PMF.pure_apply, if_pos rfl]
  · rw [(p.apply_eq_zero_iff b).2 (by rw [hs]; exact hb), PMF.pure_apply, if_neg hb]

/-- where the honest proofs are all π0, every event of V's verdict on the fixed pair (x, π0) is no
more likely than in an honest run -/
theorem verKey_complete (A : Arg lam I X W IVK ISK Pf) (π0 : Pf) (i0 : I) (x : X) (w : W)
    (hP : VerConst A i0 x w π0) (E : Set Bool) :
    Pr (verKey A i0 x π0) (fun _ => E) ≤ Pr (completenessExp A i0 x w) (fun _ => E) := by
  unfold Pr PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob (((A.C i0).bind fun k => A.V k.1 x π0).run f) E ≤
    prob (((A.C i0).bind fun k => (A.P k.2 x w).bind fun π => A.V k.1 x π).run f) E
  rw [run_bind, prob_bind, run_bind, prob_bind]
  refine expect_le_on_support _ fun k hk => ?_
  rw [run_bind, ver_pmfPure _ π0 (hP f k hk), PMF.pure_bind]

/-- the last step of the three: accept and refuse add up to 1 -/
theorem verKey_sum (A : Arg lam I X W IVK ISK Pf) (i0 : I) (x : X) (π0 : Pf) (α γ : ℝ≥0∞)
    (c : Pr (verKey A i0 x π0) (fun _ => {b | b = false}) ≤ α)
    (d : Pr (verKey A i0 x π0) (fun _ => {b | b = true}) ≤ γ) : 1 ≤ α + γ := by
  have s := Pr_add_compl (verKey A i0 x π0) {b | b = true}
  have ec : ({b : Bool | b = true})ᶜ = {b | b = false} := by ext b; cases b <;> simp
  rw [ec] at s
  calc
    (1 : ℝ≥0∞) =
        Pr (verKey A i0 x π0) (fun _ => {b | b = true}) +
          Pr (verKey A i0 x π0) (fun _ => {b | b = false}) := s.symm
    _ ≤ γ + α := add_le_add d c
    _ = α + γ := add_comm _ _

end

theorem ver_selfDist : Spec.ver_selfDist := by
  intro lam I X W PP IVK ISK Pf R A S ζ i0 i1 hpp Z0 Z1 h0 h1 x π q hq hn
  have a0 := le_add_of_SD_le
    (h0 q (fun ivk => verAdv (A.V ivk x π)) 0 fun ivk => verAdv_qb _ _ (hq ivk)).1
    {v' | v'.coins ≠ []}
  have a1 := le_add_of_SD_le'
    (h1 q (fun ivk => verAdv (A.V ivk x π)) 0 fun ivk => verAdv_qb _ _ (hq ivk)).1
    {v' | v'.coins ≠ []}
  have e : idealExp R S (fun ivk => verAdv (A.V ivk x π)) Z0 i0 0 =
      idealExp R S (fun ivk => verAdv (A.V ivk x π)) Z1 i1 0 := by
    unfold idealExp
    rw [hpp]
    exact congrArg _ (funext fun out => verAdv_ideal S Z0 Z1 _ 0 _ out.2)
  simp only [verKey_real A _ _ x π hn] at a0 a1
  rw [e] at a0
  calc _ ≤ _ := a0
    _ ≤ (Pr (verKey A i1 x π) (fun _ => {b | b = true}) + ζ q 0) + ζ q 0 := add_le_add a1 le_rfl
    _ = _ := by rw [add_assoc]

theorem ver_const : Spec.ver_const := by
  intro lam I X W PP IVK ISK Pf R A S α β ζ hc hp π0 i0 i1 hpp x w hx hP hβ q hq hn
  have d := ver_selfDist lam I X W PP IVK ISK Pf R A S ζ i0 i1 hpp (fun _ => none) (fun _ => none)
    (hp i0 _ fun _ _ _ hh => by cases hh) (hp i1 _ fun _ _ _ hh => by cases hh) x π0 q hq hn
  have c := le_trans (verKey_complete A π0 i0 x w hP {b | b = false}) (hc i0 x w hx)
  have := verKey_sum A i0 x π0 α _ c (le_trans d (add_le_add hβ le_rfl))
  rwa [← add_assoc] at this

theorem ver_constNote : Spec.ver_constNote := by
  intro lam I X W PP IVK ISK Pf R A α β ε ζ h π0 i0 i1 hpp x w hx hP x1 w1 hx1 hβ q hq hn
  obtain ⟨S, hS⟩ := h.indexPrivacy
  have d := ver_selfDist lam I X W PP IVK ISK Pf R A S ζ i0 i1 hpp _ _
    (hS i0 (fun _ _ => (x, w)) fun _ => hx) (hS i1 (fun _ _ => (x1, w1)) fun _ => hx1) x π0 q hq hn
  have c := le_trans (verKey_complete A π0 i0 x w hP {b | b = false}) (h.completeness i0 x w hx)
  have := verKey_sum A i0 x π0 α _ c (le_trans d (add_le_add hβ le_rfl))
  rwa [← add_assoc] at this

theorem ver_keyWrong : Spec.ver_keyWrong := by
  intro lam I X W PP IVK ISK Pf R A i1 x π0 hx'
  classical
  unfold Pr PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob (((A.C i1).bind fun k => A.V k.1 x π0).run f) _ ≤
    prob (((A.C i1).bind fun k =>
        (A.V k.1 x π0).bind fun b => (.pure (b, x) : OComp lam (Bool × X))).run f) _
  rw [run_bind, prob_bind, run_bind, prob_bind]
  refine expect_mono _ fun k => ?_
  rw [run_bind, prob_bind, prob_eq_expect]
  refine expect_mono _ fun b => ?_
  show _ ≤ prob (PMF.pure (b, x)) _
  rw [prob_pure]
  cases b
  · simp
  · have : ((true, x) : Bool × X) ∈ {o : Bool × X | o.1 = true ∧ o.2 ∉ R.L (some i1)} := ⟨rfl, hx'⟩
    rw [if_pos this]
    split <;> simp

theorem ver_constNamed : Spec.ver_constNamed := by
  intro lam I X W PP IVK ISK Pf R A E S α δ ε ζ h he π0 i0 i1 hpp x w hx hP hx' tC hC q hq hn
  have hβ := le_trans (ver_keyWrong lam I X W PP IVK ISK Pf R A i1 x π0 hx')
    (false_instance_of_extraction (tP := 0) he h.indexBinding i1 hC
      (fun _ => .pure (x, π0)) fun _ => trivial)
  exact ver_const lam I X W PP IVK ISK Pf R A S α _ ζ h.completeness h.indexPrivacy π0 i0 i1
    hpp x w hx hP hβ q hq hn

/-- arithmetic for the numerals -/
theorem ver_inv8 (k : ℕ) (h : 3 ≤ k) : ((2 : ℝ≥0∞) ^ k)⁻¹ ≤ 8⁻¹ := by
  have e : (8 : ℝ≥0∞) = 2 ^ 3 := by norm_num
  rw [e]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two h)

theorem ver_five8 : (8 : ℝ≥0∞)⁻¹ + (8⁻¹ + 8⁻¹) + (8⁻¹ + 8⁻¹) < 1 := by
  have e : (8 : ℝ≥0∞)⁻¹ + (8⁻¹ + 8⁻¹) + (8⁻¹ + 8⁻¹) = 5 / 8 := by rw [div_eq_mul_inv]; ring
  rw [e, ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  norm_num

end TopC
