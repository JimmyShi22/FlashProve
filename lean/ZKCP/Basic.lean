-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Basic.lean: first consequences of the definitions of ZKCP/Defs.lean.

Not part of those definitions. Definitions are cited by their names in ZKCP/Defs.lean; a proposition
of the work that this protocol builds on (lean/CREDITS.md, "Further work"): both claims are
stated and proved in this file, under its heading below; its last sentence (with
`HasCompletenessError` alone) stands in no declaration here, and ZKCP/Adaptive41.lean refutes it
for adaptive choices by an example.

  * completeness_of_refined, sessions_of_refined : the proposition of that work, both claims;
  * indexBinding_iff_sound : in `HasIndexBinding`, the "knowledge" half for w follows
    from x ∈ L(i*), because the extractor is a pair of arbitrary functions;
  * HasStrongIndexPrivacyWith.toHasIndexPrivacyWith, IsZKCPArgWith.toIsZKCPArg : the stronger, named
    form implies index privacy (ZKCP/Defs.lean, `HasIndexPrivacy`) and IsZKCPArg;
  * privacy_randomised_env : under the hypotheses of its statement, the bound of `HasIndexPrivacy`
    passes to mixtures of deterministic environments (that a randomised environment with memory is
    such a mixture is argued, not proved in Lean);
  * tools on expectations, statistical distance and lazily filled tables that ZKCP/Sanity.lean,
    ZKCP/HashToy.lean and other files use.
-/
import ZKCP.Lemmas
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

/-! ### Tools -/
section Tools
variable {lam : ℕ} {α β : Type}

lemma expect_zero (p : PMF α) : expect p (fun _ => 0) = 0 := expect_const p 0

lemma expect_comm (p : PMF α) (q : PMF β) (F : α → β → ℝ≥0∞) :
    (expect p fun a => expect q fun b => F a b) = expect q fun b => expect p fun a => F a b := by
  unfold expect
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

lemma expect_finset_sum {ι : Type} (s : Finset ι) (p : PMF α) (F : ι → α → ℝ≥0∞) :
    (expect p fun a => ∑ i ∈ s, F i a) = ∑ i ∈ s, expect p (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect]
  | insert i s hi ih => simp only [Finset.sum_insert hi, expect_add, ih]

lemma expect_le_of_le (p : PMF α) {F : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, F a ≤ c) : expect p F ≤ c :=
  le_trans (expect_mono p h) (le_of_eq (expect_const p c))

lemma expect_le_add (p : PMF α) {A B H : α → ℝ≥0∞} (h : ∀ a, A a ≤ B a + H a) :
    expect p A ≤ expect p B + expect p H := by
  rw [← expect_add]; exact expect_mono p h

open Classical in
lemma expect_le_prob_add (p : PMF α) (F : α → ℝ≥0∞) (S : Set α) (c : ℝ≥0∞)
    (h1 : ∀ a, F a ≤ 1) (h2 : ∀ a, a ∉ S → F a ≤ c) : expect p F ≤ prob p S + c := by
  rw [prob_eq_expect, ← expect_const p c, ← expect_add]
  refine expect_mono p fun a => ?_
  by_cases h : a ∈ S
  · simp only [if_pos h]; exact le_trans (h1 a) le_self_add
  · simp only [if_neg h, zero_add]; exact h2 a h

lemma expect_prob_pure (p : PMF α) (E : Set α) :
    (expect p fun a => prob (PMF.pure a) E) = prob p E := by
  classical
  rw [prob_eq_expect]; simp only [prob_pure]

lemma PrFrom_le_one (c : Cache lam) (m : OComp lam α) (E : Set α) : PrFrom c m E ≤ 1 := by
  calc PrFrom c m E ≤ ∫⁻ _, 1 ∂(U lam) := lintegral_mono fun _ => prob_le_one _ _
    _ = 1 := by simp

lemma Pr_add_compl (m : OComp lam α) (E : Set α) : Pr m (fun _ => E) + Pr m (fun _ => Eᶜ) = 1 := by
  unfold Pr PrCoins
  rw [← lintegral_add_left (measurable_prob_run m E)]
  simp [prob_add_compl]

lemma SD_le_of_forall {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞}
    (h₁ : ∀ E, X E ≤ Y E + z) (h₂ : ∀ E, Y E ≤ X E + z) : SD X Y ≤ z := by
  refine iSup_le fun E => max_le ?_ ?_
  · exact tsub_le_iff_left.2 (h₁ E)
  · exact tsub_le_iff_left.2 (h₂ E)

lemma le_add_of_SD_le' {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} (h : SD X Y ≤ z) (E : Set α) :
    Y E ≤ X E + z := by
  have h1 : Y E - X E ≤ z :=
    le_trans (le_trans (le_max_right _ _) (le_iSup (fun E => max (X E - Y E) (Y E - X E)) E)) h
  rw [add_comm]; exact tsub_le_iff_right.1 h1

/-- The distance between two mixtures with the same weights is at most the largest distance between
their components. -/
lemma SD_mixture_le {σ : Type} (μ : PMF σ) (X Y : σ → Set α → ℝ≥0∞)
    (z : ℝ≥0∞) (h : ∀ s, SD (X s) (Y s) ≤ z) :
    SD (fun T => expect μ fun s => X s T) (fun T => expect μ fun s => Y s T) ≤ z := by
  refine SD_le_of_forall (fun T => ?_) (fun T => ?_)
  · rw [← expect_const μ z, ← expect_add]
    exact expect_mono μ fun s => le_add_of_SD_le (h s) T
  · rw [← expect_const μ z, ← expect_add]
    exact expect_mono μ fun s => le_add_of_SD_le' (h s) T

/-! Tables that only grow, and traces that they contain. -/

/-- Table c' extends table c. -/
def CacheLE (c c' : Cache lam) : Prop := ∀ q r, c q = some r → c' q = some r

lemma CacheLE.refl (c : Cache lam) : CacheLE c c := fun _ _ h => h

lemma CacheLE.trans {c c' c'' : Cache lam} (h : CacheLE c c') (h' : CacheLE c' c'') :
    CacheLE c c'' :=
  fun q r e => h' q r (h q r e)

lemma CacheLE.update {c : Cache lam} {q : Str} (hq : c q = none) (r : Digest lam) :
    CacheLE c (Function.update c q (some r)) := by
  intro q' r' e
  have hne : q' ≠ q := fun h => by rw [h, hq] at e; cases e
  rw [Function.update_of_ne hne]; exact e

/-- Every entry of the trace is in the table. -/
def TraceIn (tr : Trace lam) (c : Cache lam) : Prop := ∀ q r, (q, r) ∈ tr → c q = some r

lemma TraceIn.consistent {tr : Trace lam} {c : Cache lam} (h : TraceIn tr c) :
    Trace.Consistent tr := by
  intro q r r' h1 h2
  have e1 := h q r h1
  have e2 := h q r' h2
  rw [e1] at e2
  exact Option.some.inj e2

lemma TraceIn.mono {tr : Trace lam} {c c' : Cache lam} (h : TraceIn tr c) (hc : CacheLE c c') :
    TraceIn tr c' :=
  fun q r e => hc q r (h q r e)

lemma TraceIn.snoc {tr : Trace lam} {c : Cache lam} (h : TraceIn tr c) {q : Str} {r : Digest lam}
    (hq : c q = some r) : TraceIn (tr ++ [(q, r)]) c := by
  intro q' r' e
  rcases List.mem_append.1 e with e | e
  · exact h q' r' e
  · simp only [List.mem_singleton, Prod.mk.injEq] at e
    rw [e.1, e.2]; exact hq

lemma TraceIn.nil (c : Cache lam) : TraceIn [] c := fun _ _ h => by cases h

/-- A quantity that vanishes on every extension of c has expectation 0 after one lazy answer from
c. -/
lemma expect_lazyAnswer_eq_zero (c : Cache lam) (q : Str) (F : Digest lam × Cache lam → ℝ≥0∞)
    (h : ∀ r c', CacheLE c c' → c' q = some r → F (r, c') = 0) : expect (lazyAnswer c q) F = 0 := by
  unfold lazyAnswer
  cases hq : c q with
  | some r => simp only [expect_pure]; exact h r c (CacheLE.refl c) hq
  | none =>
    simp only [expect_map]
    have : ∀ r : Digest lam, F (r, Function.update c q (some r)) = 0 := fun r =>
      h r _ (CacheLE.update hq r) (Function.update_self _ _ _)
    simp only [this, expect_zero]

/-- A quantity that vanishes on every extension of c has expectation 0 after a whole lazy run from
c. -/
lemma expect_lazyRun_eq_zero (m : OComp lam α) : ∀ (c : Cache lam) (F : α × Cache lam → ℝ≥0∞),
    (∀ a c', CacheLE c c' → F (a, c') = 0) → expect (m.lazyRun c) F = 0 := by
  induction m with
  | pure a => intro c F h; simp only [OComp.lazyRun, expect_pure]; exact h a c (CacheLE.refl c)
  | query q k ih =>
    intro c F h
    simp only [OComp.lazyRun, expect_bind]
    exact expect_lazyAnswer_eq_zero c q _ fun r c' hc _ =>
      ih r c' F fun a c'' hc' => h a c'' (hc.trans hc')
  | sample n k ih =>
    intro c F h
    simp only [OComp.lazyRun, expect_bind]
    have : ∀ r, expect ((k r).lazyRun c) F = 0 := fun r => ih r c F h
    simp only [this, expect_zero]

end Tools

section General
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-! ### From refined completeness -/

/-- The first claim of the proposition of that work: [after that work: completeness error (α_C,
α_P) implies completeness error α_C + α_P.] -/
theorem completeness_of_refined {αC αP : ℝ≥0∞} (h : HasRefinedCompletenessError R A αC αP) :
    HasCompletenessError R A (αC + αP) := by
  intro i x w hR
  have key : ∀ f : Oracle lam, PrCoins f (completenessExp A i x w) {b | b = false} ≤
      PrCoins f (A.C i) (badKeys R A αP i f) + αP := by
    intro f
    have e : PrCoins f (completenessExp A i x w) {b | b = false} =
        expect ((A.C i).run f) fun key =>
          PrCoins f (sessionExp A key.1 key.2 x w) {b | b = false} := by
      simp only [PrCoins, completenessExp, bind_eq, run_bind, prob_bind]
    rw [e]
    refine expect_le_prob_add _ _ _ _ (fun key => prob_le_one _ _) fun key hb => ?_
    by_contra hc
    exact hb ⟨x, w, hR, not_le.1 hc⟩
  calc Pr (completenessExp A i x w) (fun _ => {b | b = false})
      ≤ ∫⁻ f, (PrCoins f (A.C i) (badKeys R A αP i f) + αP) ∂(U lam) := lintegral_mono key
    _ = Pr (A.C i) (fun f => badKeys R A αP i f) + αP := by
        rw [lintegral_add_right _ measurable_const]; simp [Pr]
    _ ≤ αC + αP := by gcongr; exact h i

/-- N honest sessions on one key, the pairs (x_j, w_j) chosen adaptively by Z from the earlier (x,
π, V's bit).
Output: true iff V accepted every session. -/
def sessionsLoop {i : I} (Z : List (X × Pf × Bool) → {xw : X × W // R.rel i xw.1 xw.2})
    (ivk : IVK) (isk : ISK) :
    ℕ → List (X × Pf × Bool) → OComp lam Bool
  | 0, _ => .pure true
  | n + 1, hist =>
      (A.P isk (Z hist).val.1 (Z hist).val.2).bind fun π =>
        (A.V ivk (Z hist).val.1 π).bind fun b =>
          (sessionsLoop Z ivk isk n (hist ++ [((Z hist).val.1, π, b)])).bind fun rest =>
            .pure (b && rest)

/-- The second claim of the proposition of that work: [after that work: for every i and adaptively
chosen pairs (x_j, w_j), j ≤ N, with (i, x_j, w_j) ∈ R, Pr[ some honest proof is rejected ] ≤ α_C +
N·α_P.]
The chooser Z may depend on the whole oracle f, on both keys, and on all earlier (x, π, V's bit)
(no measurability in f is asked of Z; the left side is Mathlib's ∫⁻).
The hypothesis is `HasRefinedCompletenessError` with (α_C, α_P). -/
theorem sessions_of_refined {αC αP : ℝ≥0∞} (h : HasRefinedCompletenessError R A αC αP) (i : I)
    (Z : Oracle lam → IVK × ISK → List (X × Pf × Bool) → {xw : X × W // R.rel i xw.1 xw.2})
    (N : ℕ) :
    ∫⁻ f, expect ((A.C i).run f)
        (fun key => PrCoins f (sessionsLoop R A (Z f key) key.1 key.2 N []) {b | b = false})
        ∂(U lam) ≤
      αC + N * αP := by
  have good : ∀ (f : Oracle lam) (key : IVK × ISK), key ∉ badKeys R A αP i f →
      ∀ (Z : List (X × Pf × Bool) → {xw : X × W // R.rel i xw.1 xw.2})
          (n : ℕ) (hist : List (X × Pf × Bool)),
        prob ((sessionsLoop R A Z key.1 key.2 n hist).run f) {b | b = false} ≤ n * αP := by
    intro f key hg Z n
    induction n with
    | zero => intro hist; simp [sessionsLoop, OComp.run, prob_pure]
    | succ n ih =>
      intro hist
      have hs : PrCoins f (sessionExp A key.1 key.2 (Z hist).val.1 (Z hist).val.2) {b | b = false} ≤
          αP := by
        by_contra hc
        exact hg ⟨_, _, (Z hist).property, not_le.1 hc⟩
      simp only [PrCoins, sessionExp, bind_eq, run_bind, prob_bind] at hs
      simp only [sessionsLoop, run_bind, prob_bind, OComp.run]
      have step : ∀ (π : Pf) (b : Bool),
          (expect ((sessionsLoop R A Z key.1 key.2 n (hist ++ [((Z hist).val.1, π, b)])).run f)
              fun rest => prob (PMF.pure (b && rest)) {b | b = false}) ≤
            prob (PMF.pure b) {b | b = false} + n * αP := by
        intro π b
        cases b with
        | false => simp [prob_pure, expect_const]
        | true =>
          refine le_trans (le_of_eq ?_)
            (le_trans (ih (hist ++ [((Z hist).val.1, π, true)])) le_add_self)
          simp only [Bool.true_and, expect_prob_pure]
      refine le_trans (expect_mono _ fun π => expect_mono _ fun b => step π b) ?_
      simp only [expect_add, expect_const, expect_prob_pure]
      calc _ ≤ αP + n * αP := by gcongr
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * αP := by push_cast; ring
  have key : ∀ f : Oracle lam,
      expect ((A.C i).run f) (fun key =>
        PrCoins f (sessionsLoop R A (Z f key) key.1 key.2 N []) {b | b = false}) ≤
        PrCoins f (A.C i) (badKeys R A αP i f) + N * αP := by
    intro f
    exact expect_le_prob_add _ _ _ _ (fun _ => prob_le_one _ _) fun key hb =>
      good f key hb (Z f key) N []
  calc _ ≤ ∫⁻ f, (PrCoins f (A.C i) (badKeys R A αP i f) + N * αP) ∂(U lam) := lintegral_mono key
    _ = Pr (A.C i) (fun f => badKeys R A αP i f) + N * αP := by
        rw [lintegral_add_right _ measurable_const]; simp [Pr]
    _ ≤ αC + N * αP := by gcongr; exact h i

/-! ### The witness clause of ZKCP/Defs.lean, `HasIndexBinding` -/

/-- The event "V accepts and x ∉ L(i*)": the event of ZKCP/Defs.lean, `HasIndexBinding`, without its
witness clause. -/
def soundBad : Set (BindingOutcome I X W) := {o | o.accept = true ∧ o.x ∉ R.L o.iStar}

open Classical in
/-- E with its witness part replaced by: "if x ∈ L(E_i(ivk, tr_C)), pick some valid witness". -/
def Extractor.withChosenWitness (E : Extractor lam I X W IVK Pf) :
    Extractor lam I X W IVK Pf where
  Ei := E.Ei
  Ew := fun ivk trC x π trP =>
    if h : ∃ w, R.rel' (E.Ei ivk trC) x w then h.choose else E.Ew ivk trC x π trP

lemma mem_L_iff (o : Option I) (x : X) : x ∈ R.L o ↔ ∃ w, R.rel' o x w := by
  cases o <;> simp [IndexedRelation.L, IndexedRelation.rel']

/-- `HasIndexBinding` asks only that the extractor be deterministic. Then its witness
clause adds nothing: the scheme meets that definition (index-binding *knowledge* soundness) with
error ε exactly when some extractor achieves error ε for the event "V accepts and x ∉ L(i*)"
alone. -/
theorem indexBinding_iff_sound (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBinding R A ε ↔ ∃ E : Extractor lam I X W IVK Pf,
      ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)),
        Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
          Pr (bindingExp A E Ct Pt) (fun _ => soundBad R) ≤ ε tC tP := by
  classical
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E, fun tC tP St Ct Pt h1 h2 => le_trans (Pr_mono _ ?_) (hE tC tP St Ct Pt h1 h2)⟩
    rintro o ⟨ho1, ho2⟩
    exact ⟨ho1, Or.inl ho2⟩
  · rintro ⟨E, hE⟩
    refine ⟨E.withChosenWitness R,
      fun tC tP St Ct Pt h1 h2 => le_trans ?_ (hE tC tP St Ct Pt h1 h2)⟩
    refine lintegral_mono fun f => ?_
    simp only [PrCoins, bindingExp, bind_eq, pure_eq, run_bind, prob_bind, OComp.run, prob_pure]
    refine expect_mono _ fun o1 => expect_mono _ fun o2 => expect_mono _ fun b => ?_
    have imp : ((⟨b,
            (E.withChosenWitness R).Ei o1.1.1 o1.2,
            o2.1.1,
            (E.withChosenWitness R).Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ : BindingOutcome I X W) ∈
          bindingBad R) →
        ((⟨b, E.Ei o1.1.1 o1.2, o2.1.1,
            E.Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ : BindingOutcome I X W) ∈
          soundBad R) := by
      rintro ⟨hb, hor⟩
      refine ⟨hb, ?_⟩
      rcases hor with hh | hh
      · exact hh
      · intro hmem
        apply hh
        have hex : ∃ w, R.rel' (E.Ei o1.1.1 o1.2) o2.1.1 w := (mem_L_iff R _ _).1 hmem
        simp only [Extractor.withChosenWitness]
        rw [dif_pos hex]
        exact hex.choose_spec
    by_cases hm : ((⟨b,
        (E.withChosenWitness R).Ei o1.1.1 o1.2,
        o2.1.1,
        (E.withChosenWitness R).Ew o1.1.1 o1.2 o2.1.1 o2.1.2 o2.2⟩ : BindingOutcome I X W) ∈
      bindingBad R)
    · rw [if_pos hm, if_pos (imp hm)]
    · rw [if_neg hm]; exact zero_le _

/-! ### Named extractor and simulator; randomised environments -/

variable {R A}

lemma Env.onView_isValid {Z : Env I X W Pf} {i : I} (h : Z.IsValid R i) :
    (Z.onView i : ViewEnv lam IVK X W Pf).IsValid R i := by
  intro v x w e
  simp only [Env.onView, Option.some.injEq] at e
  have := h v.sessions
  rw [e] at this
  exact this

/-- The stronger form of privacy implies `HasIndexPrivacyWith R A S ζ`, with the same simulator and
the same error: `Env` is a special case. -/
theorem HasStrongIndexPrivacyWith.toHasIndexPrivacyWith
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasStrongIndexPrivacyWith R A S ζ) :
    HasIndexPrivacyWith R A S ζ :=
  fun i Z hZ => h i (Z.onView i) (Env.onView_isValid hZ)

theorem IsZKCPArgWith.toIsZKCPArg {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf}
    {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A E S α ε ζ) : IsZKCPArg R A α ε ζ :=
  ⟨h.completeness, ⟨E, h.indexBinding⟩, ⟨S, h.indexPrivacy.toHasIndexPrivacyWith⟩⟩

/-! Larger bounds: every clause is monotone in its error. -/

theorem HasIndexBindingWith.mono {E : Extractor lam I X W IVK Pf} {ε ε' : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexBindingWith R A E ε) (hε : ∀ tC tP, ε tC tP ≤ ε' tC tP) :
    HasIndexBindingWith R A E ε' :=
  fun tC tP St Ct Pt hC hP => (h tC tP St Ct Pt hC hP).trans (hε tC tP)

theorem PrivacyFor.mono {S : Simulator lam PP IVK X Pf} {ζ ζ' : ℕ → ℕ → ℝ≥0∞} {i : I}
    {Z : ViewEnv lam IVK X W Pf} (h : PrivacyFor R A S ζ i Z) (hζ : ∀ tV N, ζ tV N ≤ ζ' tV N) :
    PrivacyFor R A S ζ' i Z :=
  fun tV Vt N hV => ⟨(h tV Vt N hV).1.trans (hζ tV N), (h tV Vt N hV).2⟩

/-- `IsZKCPArgWith` is monotone in its three bounds. -/
theorem IsZKCPArgWith.mono {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf}
    {α α' : ℝ≥0∞} {ε ε' ζ ζ' : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A E S α ε ζ) (hα : α ≤ α')
    (hε : ∀ tC tP, ε tC tP ≤ ε' tC tP) (hζ : ∀ tV N, ζ tV N ≤ ζ' tV N) :
    IsZKCPArgWith R A E S α' ε' ζ' :=
  ⟨fun i x w hR => (h.completeness i x w hR).trans hα, h.indexBinding.mono hε,
    fun i Z hZ => (h.indexPrivacy i Z hZ).mono hζ⟩

/-- IsZKCPArg (ZKCP/Defs.lean) is monotone in its three bounds. -/
theorem IsZKCPArg.mono {α α' : ℝ≥0∞} {ε ε' ζ ζ' : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArg R A α ε ζ)
    (hα : α ≤ α') (hε : ∀ tC tP, ε tC tP ≤ ε' tC tP) (hζ : ∀ tV N, ζ tV N ≤ ζ' tV N) :
    IsZKCPArg R A α' ε' ζ' := by
  obtain ⟨hc, ⟨E, hb⟩, ⟨S, hp⟩⟩ := h
  exact ⟨fun i x w hR => (hc i x w hR).trans hα,
    ⟨E, hb.mono hε⟩,
    ⟨S, fun i Z hZ => (hp i Z hZ).mono hζ⟩⟩

/-- A randomised environment with memory is a deterministic function of (seed, i, history), the seed
being drawn once at the start, outside the view. Both views are then mixtures over the seed, and,
under the hypotheses below, `HasIndexPrivacy` for deterministic environments gives the
same bound for the mixtures.
The first sentence is argued on paper, not proved in Lean; the theorem is the bound for the
mixtures. -/
theorem privacy_randomised_env {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : HasIndexPrivacyWith R A S ζ) {Seed : Type} (μ : PMF Seed) (Z : Seed → Env I X W Pf) (i : I)
    (hZ : ∀ s, (Z s).IsValid R i) (tV : ℕ) (Vt : IVK → AdvVerifier lam X Pf) (N : ℕ)
    (hV : ∀ ivk, (Vt ivk).QueryBound tV) :
    SD (fun T => expect μ fun s => Pr (realExp A Vt ((Z s).onView i) i N) (fun _ => T))
       (fun T => expect μ fun s => prob (idealExp R S Vt ((Z s).onView i) i N) T) ≤ ζ tV N :=
  SD_mixture_le μ _ _ _ fun s => (h i (Z s) (hZ s) tV Vt N hV).1

end General
end ZKCP
