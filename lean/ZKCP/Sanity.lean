-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Sanity.lean: the definitions of ZKCP/Defs.lean are satisfiable, and not by every scheme.
Definitions are cited by their names in ZKCP/Defs.lean.

  `privacy_of_oblivious`   a scheme whose C and P use only pp(i) and x has perfect (strong) index
      privacy.
  `toy_main_with`, `toy_main`   a trivial scheme is a ZK-CP-ARG (`IsZKCPArg`, ZKCP/Defs.lean) with
      all three errors 0 (the first in the form `IsZKCPArgWith`).
  `leakIndex_not_private`, `leakWitness_not_private`, `acceptAll_not_binding`,
  `blindExtractor_not_binding`   four schemes that must fail, fail.

The toy that hashes is in ZKCP/HashToy.lean.
-/
import ZKCP.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

section General
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}

/-- The simulator that runs C' and P' themselves, on a lazily sampled oracle. -/
def lazySim (C' : PP → OComp lam (IVK × ISK)) (P' : ISK → X → OComp lam Pf) :
    Simulator lam PP IVK X Pf where
  St := ISK × Cache lam
  init := fun pp _ => ((C' pp).lazyRun fun _ => none).map fun out => (out.1.1, (out.1.2, out.2))
  answer := fun s q => (lazyAnswer s.2 q).map fun out => (out.1, (s.1, out.2))
  prove := fun s x => ((P' s.1 x).lazyRun s.2).map fun out => (out.1, (s.1, out.2))

lemma realLoop_eq_idealLoop {C' : PP → OComp lam (IVK × ISK)} {P' : ISK → X → OComp lam Pf}
    (hP : ∀ isk x w, A.P isk x w = P' isk x) (Z : ViewEnv lam IVK X W Pf) (isk : ISK)
    (E : Set (View lam IVK X Pf)) (Vt : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : View lam IVK X Pf) (c : Cache lam), PrFrom c (realLoop A Z isk Vt n v) E =
      prob (idealLoop (lazySim C' P') Z Vt n v (isk, c)) E := by
  induction Vt with
  | halt => intro n v c; simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
  | query q k ih =>
    intro n v c
    simp only [realLoop, idealLoop, PrFrom_query, prob_bind, lazySim, expect_map]
    exact expect_congr _ fun out => ih _ _ _ _
  | sample m k ih =>
    intro n v c
    simp only [realLoop, idealLoop, PrFrom_sample, prob_bind]
    exact expect_congr _ fun r => ih _ _ _ _
  | request k ih =>
    intro n v c
    cases n with
    | zero => simp only [realLoop, idealLoop, pure_eq, PrFrom_pure, prob_pure]
    | succ n =>
      simp only [realLoop, idealLoop]
      cases Z v with
      | none => simp only [pure_eq, PrFrom_pure, prob_pure]
      | some xw =>
        simp only [PrFrom_bind, prob_bind, lazySim, expect_map, hP]
        exact expect_congr _ fun out => ih _ _ _ _ _

open Classical in
lemma prob_pure_inconsistent_eq_zero
    {v : View lam IVK X Pf} {c : Cache lam} (h : TraceIn v.trace c) :
    prob (PMF.pure v) {v : View lam IVK X Pf | ¬ v.trace.Consistent} = 0 := by
  rw [prob_pure, if_neg]
  exact fun hn => hn h.consistent

/-- Under the hypotheses below, the lazy simulator answers consistently: V~'s trace is always inside
the simulator's table. -/
lemma lazySim_consistent (C' : PP → OComp lam (IVK × ISK)) (P' : ISK → X → OComp lam Pf)
    (Z : ViewEnv lam IVK X W Pf) (isk : ISK) (Vt : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : View lam IVK X Pf) (c : Cache lam), TraceIn v.trace c →
      prob (idealLoop (lazySim C' P') Z Vt n v (isk, c)) {v | ¬ v.trace.Consistent} = 0 := by
  induction Vt with
  | halt => intro n v c h; simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
  | query q k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind, lazySim, expect_map]
    exact expect_lazyAnswer_eq_zero c q _ fun r c' hc hq => ih r n _ c' ((h.mono hc).snoc hq)
  | sample m k ih =>
    intro n v c h
    simp only [idealLoop, prob_bind]
    have : ∀ r, prob
          (idealLoop (lazySim C' P') Z (k r) n { v with coins := v.coins ++ [r.val] } (isk, c))
          {v | ¬ v.trace.Consistent} = 0 :=
      fun r => ih r n _ c h
    simp only [this, expect_zero]
  | request k ih =>
    intro n v c h
    cases n with
    | zero => simp only [idealLoop]; exact prob_pure_inconsistent_eq_zero h
    | succ n =>
      simp only [idealLoop]
      cases Z v with
      | none => exact prob_pure_inconsistent_eq_zero h
      | some xw =>
        simp only [prob_bind, lazySim, expect_map]
        exact expect_lazyRun_eq_zero _ c _ fun a c' hc => ih _ _ n _ c' (h.mono hc)

/-- If C uses only pp(i) and P uses only (isk, x), the scheme has strong index privacy with error
0. -/
theorem privacy_of_oblivious {C' : PP → OComp lam (IVK × ISK)} {P' : ISK → X → OComp lam Pf}
    (hC : ∀ i, A.C i = C' (R.pp i)) (hP : ∀ isk x w, A.P isk x w = P' isk x) :
    HasStrongIndexPrivacyWith R A (lazySim C' P') fun _ _ => 0 := by
  intro i Z _ tV Vt N _
  constructor
  · refine le_of_eq (SD_self_eq_zero fun E => ?_)
    rw [Pr_eq_PrFrom]
    simp only [realExp, idealExp, bind_eq, PrFrom_bind, prob_bind, hC]
    simp only [lazySim, expect_map]
    exact expect_congr _ fun out => realLoop_eq_idealLoop hP Z _ E _ _ _ _
  · simp only [idealExp, prob_bind]
    simp only [lazySim, expect_map]
    have : ∀ out : (IVK × ISK) × Cache lam,
        prob (idealLoop (lazySim C' P') Z (Vt out.1.1) N ⟨out.1.1, [], [], []⟩ (out.1.2, out.2))
          {v | ¬ v.trace.Consistent} = 0 := fun out =>
      lazySim_consistent C' P' Z _ _ N _ _ (TraceIn.nil _)
    exact (expect_congr _ this).trans (expect_zero _)

end General

/-! ## A trivial scheme that satisfies the definition -/
section Toy

/-- Toy relation: two indices with the same public parameters; L(i) = {true}; every w is a
witness. -/
def toyR : IndexedRelation Bool Bool Bool Unit where
  rel := fun _ x _ => x = true
  pp := fun _ => ()

/-- Toy scheme: empty key, empty proof, V checks the public condition x = true itself. -/
def toyArg (lam : ℕ) : Arg lam Bool Bool Bool Unit Unit Unit where
  C := fun _ => .pure ((), ())
  P := fun _ _ _ => .pure ()
  V := fun _ x _ => .pure x

def toyExt (lam : ℕ) : Extractor lam Bool Bool Bool Unit Unit :=
  ⟨fun _ _ => some false, fun _ _ _ _ _ => false⟩

/-- The form `IsZKCPArgWith` (named form), proved for the trivial toy. -/
theorem toy_main_with (lam : ℕ) : IsZKCPArgWith toyR (toyArg lam) (toyExt lam)
    (lazySim (fun _ => .pure ((), ())) (fun _ _ => .pure ())) 0 (fun _ _ => 0) (fun _ _ => 0) where
  completeness := by
    intro i x w hR
    have hx : x = true := hR
    subst hx
    simp [completenessExp, sessionExp, toyArg, OComp.bind, Pr, PrCoins, OComp.run, prob_pure]
  indexBinding := by
    intro tC tP St Ct Pt _ _
    have hb : ∀ x : Bool,
        (⟨x, some false, x, false⟩ : BindingOutcome Bool Bool Bool) ∉ bindingBad toyR := by
      intro x; simp [bindingBad, toyR, IndexedRelation.L, IndexedRelation.rel']
    have h0 : ∀ f : Oracle lam,
        PrCoins f (bindingExp (toyArg lam) (toyExt lam) Ct Pt) (bindingBad toyR) = 0 := by
      intro f
      simp only [PrCoins, bindingExp, bind_eq, pure_eq, run_bind, prob_bind, OComp.run, prob_pure,
        toyArg, toyExt, expect_pure, hb, if_false, expect_zero]
    simp [Pr, h0]
  indexPrivacy := privacy_of_oblivious (fun _ => rfl) (fun _ _ _ => rfl)

theorem toy_main (lam : ℕ) : IsZKCPArg toyR (toyArg lam) 0 (fun _ _ => 0) (fun _ _ => 0) :=
  (toy_main_with lam).toIsZKCPArg

/-- The toy also meets the refined form of completeness (`HasRefinedCompletenessError`,
ZKCP/Defs.lean) with (α_C, α_P) = (0, 0). -/
theorem toy_refined (lam : ℕ) : HasRefinedCompletenessError toyR (toyArg lam) 0 0 := by
  intro i
  have h0 : ∀ f : Oracle lam, badKeys toyR (toyArg lam) 0 i f = ∅ := by
    intro f
    ext key
    simp only [badKeys, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, w, hR, hlt⟩
    have hx : x = true := hR
    subst hx
    simp [PrCoins, sessionExp, toyArg, OComp.bind, OComp.run, prob_pure] at hlt
  simp [Pr, PrCoins, h0, prob]

end Toy

/-! ## Schemes that must fail, and do -/
section Negative

/-- If two real views are distinguished with certainty by an event E, and both are within z of the
same ideal view, then z ≥ 1/2. -/
lemma half_le_of_two_worlds {α : Type} {X₁ X₂ : Set α → ℝ≥0∞} {p : PMF α} {z : ℝ≥0∞}
    (E : Set α) (h₁ : X₁ E = 1) (h₂ : X₂ Eᶜ = 1)
    (d₁ : SD X₁ (fun T => prob p T) ≤ z) (d₂ : SD X₂ (fun T => prob p T) ≤ z) : 1 / 2 ≤ z := by
  by_contra hlt
  have hz : z < 1 / 2 := not_le.1 hlt
  have a₁ := le_add_of_SD_le d₁ E
  have a₂ := le_add_of_SD_le d₂ Eᶜ
  rw [h₁] at a₁
  rw [h₂] at a₂
  have s : (1 : ℝ≥0∞) + 1 ≤ 1 + (z + z) := by
    calc (1 : ℝ≥0∞) + 1 ≤ (prob p E + z) + (prob p Eᶜ + z) := add_le_add a₁ a₂
      _ = (prob p E + prob p Eᶜ) + (z + z) := by ring
      _ = 1 + (z + z) := by rw [prob_add_compl]
  have s' : (1 : ℝ≥0∞) ≤ z + z := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 s
  have : z + z < 1 := by
    calc z + z < 1 / 2 + 1 / 2 := ENNReal.add_lt_add hz hz
      _ = 1 := ENNReal.add_halves 1
  exact absurd s' (not_le.2 this)

/-- The trivial relation on a one-bit index: every (i, x, w) is in R, and pp reveals nothing. -/
def trivR (W : Type) : IndexedRelation Bool Unit W Unit where
  rel := fun _ _ _ => True
  pp := fun _ => ()

/-- A scheme that publishes the index as its key. -/
def leakIndex (lam : ℕ) : Arg lam Bool Unit Unit Bool Unit Unit where
  C := fun i => .pure (i, ())
  P := fun _ _ _ => .pure ()
  V := fun _ _ _ => .pure true

/-- For `trivR Unit`: Publishing i in ivk violates `HasIndexPrivacy`: no simulator does
better than ζ(0,0) = 1/2, already against the verifier that makes no query and requests no
session. -/
theorem leakIndex_not_private (lam : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : HasIndexPrivacy (trivR Unit) (leakIndex lam) ζ) : 1 / 2 ≤ ζ 0 0 := by
  classical
  obtain ⟨S, hS⟩ := h
  let Z : Env Bool Unit Unit Unit := fun _ _ => ((), ())
  let Vt : Bool → AdvVerifier lam Unit Unit := fun _ => .halt
  have d₁ := (hS true Z (fun _ => trivial) 0 Vt 0 (fun _ => trivial)).1
  have d₂ := (hS false Z (fun _ => trivial) 0 Vt 0 (fun _ => trivial)).1
  have e : idealExp (trivR Unit) S Vt (Z.onView false) false 0 =
      idealExp (trivR Unit) S Vt (Z.onView true) true 0 := by
    simp only [idealExp, idealLoop, Vt, trivR]
  rw [e] at d₂
  refine half_le_of_two_worlds {v | v.ivk = true} ?_ ?_ d₁ d₂
  · simp [realExp, realLoop, leakIndex, Vt, OComp.bind, Pr, PrCoins, OComp.run, prob_pure]
  · simp [realExp, realLoop, leakIndex, Vt, OComp.bind, Pr, PrCoins, OComp.run, prob_pure]

/-- A scheme whose proof is the witness. -/
def leakWitness (lam : ℕ) : Arg lam Bool Unit Bool Unit Unit Bool where
  C := fun _ => .pure ((), ())
  P := fun _ _ w => .pure w
  V := fun _ _ _ => .pure true

/-- For `trivR Bool` (every (i, x, w) is in R): Sending w as the proof violates ZKCP/Defs.lean,
`HasIndexPrivacy`, which hides the witnesses too: ζ(0,1) ≥ 1/2 for every simulator. -/
theorem leakWitness_not_private (lam : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : HasIndexPrivacy (trivR Bool) (leakWitness lam) ζ) : 1 / 2 ≤ ζ 0 1 := by
  classical
  obtain ⟨S, hS⟩ := h
  let Z : Bool → Env Bool Unit Bool Bool := fun w _ _ => ((), w)
  let Vt : Unit → AdvVerifier lam Unit Bool := fun _ => .request fun _ _ => .halt
  have d₁ := (hS true (Z true) (fun _ => trivial) 0 Vt 1 (fun _ _ _ => trivial)).1
  have d₂ := (hS true (Z false) (fun _ => trivial) 0 Vt 1 (fun _ _ _ => trivial)).1
  have e : idealExp (trivR Bool) S Vt ((Z false).onView true) true 1 =
      idealExp (trivR Bool) S Vt ((Z true).onView true) true 1 := by
    simp only [idealExp, idealLoop, Vt, Z, Env.onView]
  rw [e] at d₂
  refine half_le_of_two_worlds {v | v.sessions = [((), true)]} ?_ ?_ d₁ d₂
  · simp [realExp, realLoop, leakWitness, Vt, Z, Env.onView, OComp.bind, Pr,
      PrCoins, OComp.run, prob_pure]
  · simp [realExp, realLoop, leakWitness, Vt, Z, Env.onView, OComp.bind, Pr,
      PrCoins, OComp.run, prob_pure]

/-- A relation with an instance (false) that is in no L(i). -/
def someFalseR : IndexedRelation Unit Bool Unit Unit where
  rel := fun _ x _ => x = true
  pp := fun _ => ()

/-- A scheme whose verifier accepts everything. -/
def acceptAll (lam : ℕ) (I : Type) : Arg lam I Bool Unit Unit Unit Unit where
  C := fun _ => .pure ((), ())
  P := fun _ _ _ => .pure ()
  V := fun _ _ _ => .pure true

/-- For the relation `someFalseR`: A verifier that accepts everything has binding error 1, for every
extractor, already against adversaries that make no query. -/
theorem acceptAll_not_binding (lam : ℕ) (ε : ℕ → ℕ → ℝ≥0∞)
    (h : HasIndexBinding someFalseR (acceptAll lam Unit) ε) : 1 ≤ ε 0 0 := by
  classical
  obtain ⟨E, hE⟩ := h
  have := hE 0 0 Unit (.pure ((), ())) (fun _ => .pure (false, ())) trivial (fun _ => trivial)
  refine le_trans (le_of_eq ?_) this
  have hb : ∀ (o : Option Unit) (w : Unit),
      (⟨true, o, false, w⟩ : BindingOutcome Unit Bool Unit) ∈ bindingBad someFalseR := by
    intro o w
    refine ⟨rfl, Or.inl ?_⟩
    cases o <;> simp [someFalseR, IndexedRelation.L]
  simp [bindingExp, acceptAll, OComp.withTrace, OComp.bind, Pr, PrCoins, OComp.run, prob_pure, hb]

/-- The relation x = i on one-bit indices: every instance is in some L(i), but in only one. -/
def eqR : IndexedRelation Bool Bool Unit Unit where
  rel := fun i x _ => x = i
  pp := fun _ => ()

lemma mem_bad_iff (b : Bool) (o : Option Bool) (x : Bool) (w : Unit) :
    (⟨b, o, x, w⟩ : BindingOutcome Bool Bool Unit) ∈ bindingBad eqR ↔ b = true ∧ o ≠ some x := by
  cases o with
  | none => simp [bindingBad, eqR, IndexedRelation.L, IndexedRelation.rel']
  | some i =>
    simp only [bindingBad, eqR, IndexedRelation.L, IndexedRelation.rel', Set.mem_setOf_eq,
      exists_const, or_self, ne_eq, Option.some.injEq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun e => h2 e.symm⟩

/-- E_i cannot see the session. For the relation `eqR`: With an empty key and a verifier that
accepts everything, the prover picks x by a coin after i* is fixed. Every x is in some L(i), yet
every extractor errs with probability at least 1/2. -/
theorem blindExtractor_not_binding (lam : ℕ) (ε : ℕ → ℕ → ℝ≥0∞)
    (h : HasIndexBinding eqR (acceptAll lam Bool) ε) : 1 / 2 ≤ ε 0 0 := by
  classical
  obtain ⟨E, hE⟩ := h
  have := hE 0 0 Unit (.pure ((), ())) (fun _ => .sample 1 fun r => .pure (decide (r = 0), ()))
    trivial (fun _ _ => trivial)
  refine le_trans ?_ this
  have h0 : ∀ f : Oracle lam, (1 : ℝ≥0∞) / 2 ≤
      PrCoins f (bindingExp (acceptAll lam Bool) E (.pure ((), ()))
          (fun _ : Unit => .sample 1 fun r => .pure (decide (r = 0), ())))
        (bindingBad eqR) := by
    intro f
    simp only [PrCoins, bindingExp, acceptAll, OComp.withTrace, OComp.bind, bind_eq, pure_eq,
      OComp.run, prob_bind, prob_pure, expect_uniform, Fintype.card_fin]
    cases hE0 : E.Ei () [] with
    | none =>
      simp only [mem_bad_iff]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
      exact le_trans (by simp)
        (Finset.single_le_sum (f := fun _ : Fin (1 + 1) => ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ * 1)
          (fun _ _ => zero_le _) (Finset.mem_univ 0))
    | some b => cases b <;> simp [mem_bad_iff]
  calc (1 : ℝ≥0∞) / 2 = ∫⁻ _ : Oracle lam, 1 / 2 ∂(U lam) := by simp
    _ ≤ _ := lintegral_mono h0

end Negative

end ZKCP
