-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/HonestKey.lean: what completeness and index binding give together on an honest key.

For every relation and every scheme of ZKCP/Defs.lean. Consequences of `HasCompletenessError` and
`HasIndexBinding`. The three statements are not part of that file's definitions; the third rests
on a definition outside ZKCP/Defs.lean (ZKCP/Optional.lean). Below, α is the scheme's completeness
error and ε its bound on index binding for the extractor E.

  `wrongExp A i Pt`   the experiment: (ivk, isk) ← C(i), the honest committer; (x', π') ← Pt(ivk,
      isk), any prover, which is given both keys; b ← V(ivk, x', π'); the outcome is (b, x').
  `honest_extracts`   for (i, x, w) in the relation: Pr[ x ∉ L(i*) | (ivk, isk) ← C(i) with trace
      tr; i* := E_i(ivk, tr) ] ≤ α + ε(tC, tP°). In particular i* ≠ ⊥ except with that probability.
      tC bounds the honest committer's queries at i; tP° (`tP0` in Lean) the honest prover's at (x,
      w), under every key that has a property `good`, which every key that C(i) can output has.
      (π₀: any proof.)
  `wrong_answer`   let, in addition, for every index the answer (`val`) be a function of the
      question (`key`). Then Pr[ b = 1, key x' = key x, val x' ≠ val x ] ≤ α + ε(tC, tP°) + ε(tC,
      tP), for every prover with at most tP queries.
  `false_instance_of_extraction`   the stronger statement, from a stronger hypothesis: if what is
      extracted from the honest committer's key and trace is the committed index except with
      probability δ (an optional requirement: i* = i for the honest committer; `HasExtractionError`,
      ZKCP/Optional.lean), then Pr[ b = 1, x' ∉ L(i) ] ≤ δ + ε(tC, tP): no false instance, chosen by
      the prover after key and oracle; no completeness, no tP°, no `good`, no unique answers.

`wrong_answer` is the weak form: one question, fixed before the oracle, to which the committed index
has an answer. Of the scheme it asks completeness and binding alone. Whoever has
`HasExtractionError` for a scheme should quote `false_instance_of_extraction`. All three bound a
probability that is also over the committer's coins: an average over honest keys, nothing on a
single key; the prover outputs one pair.

Limits: this file does not say that i* = i (the optional requirement of ZKCP/Optional.lean), only
that L(i*) contains the one instance x that is fixed beforehand. (i, x, w) is fixed before the
oracle. The wrong answer that `wrong_answer` bounds is an answer to x's question (key x' = key x).
The prover sees no honest proof (it has isk and can make some). Where α +
ε(tC, tP°) ≥ 1 `honest_extracts` and `wrong_answer` say nothing: the bounds are taken at the honest
parties' own numbers of queries. Nothing is said about a key that the committer did not make
honestly.
-/
import ZKCP.ManyOfOne

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf K Y : Type}

/-! ## Tools -/

theorem expect_le_on_support
    {α : Type} (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ G a) :
    expect p F ≤ expect p G :=
  ENNReal.tsum_le_tsum fun a => by
    by_cases ha : p a = 0
    · rw [ha, zero_mul, zero_mul]
    · gcongr
      exact h a ha

/-- an expectation that does not read the trace -/
theorem expect_withTrace {α : Type} (f : Oracle lam) (c : OComp lam α) (F : α → ℝ≥0∞) :
    expect (c.withTrace.run f) (fun o => F o.1) = expect (c.run f) F := by
  rw [← OComp.run_withTrace_fst f c, expect_map]

theorem mem_support_withTrace {α : Type} (f : Oracle lam) (c : OComp lam α)
    (o : α × Trace lam) (h : o ∈ (c.withTrace.run f).support) : o.1 ∈ (c.run f).support := by
  rw [← OComp.run_withTrace_fst f c, PMF.support_map]
  exact ⟨o, h, rfl⟩

theorem Pr_le_add {α β γ : Type} (a : OComp lam α) (b : OComp lam β) (c : OComp lam γ) (A : Set α)
    (B : Set β) (C : Set γ) (h : ∀ f, prob (a.run f) A ≤ prob (b.run f) B + prob (c.run f) C) :
    Pr a (fun _ => A) ≤ Pr b (fun _ => B) + Pr c (fun _ => C) := by
  unfold Pr PrCoins
  rw [← lintegral_add_left (measurable_prob_run b B)]
  exact lintegral_mono h

/-- An event may be enlarged on the outputs that the computation can produce. -/
theorem Pr_mono_support {α : Type} (c : OComp lam α) (A B : Set α)
    (h : ∀ f, ∀ o ∈ (c.run f).support, o ∈ A → o ∈ B) :
    Pr c (fun _ => A) ≤ Pr c (fun _ => B) := by
  classical
  refine lintegral_mono fun f => ?_
  show prob (c.run f) A ≤ prob (c.run f) B
  rw [prob_eq_expect, prob_eq_expect]
  refine expect_le_on_support _ fun o ho => ?_
  by_cases hA : o ∈ A
  · rw [if_pos hA, if_pos (h f o ho hA)]
  · rw [if_neg hA]
    exact zero_le _

variable (R : IndexedRelation I X W PP)
  (A : Arg lam I X W IVK ISK Pf) (E : Extractor lam I X W IVK Pf)

/-- The experiment with the honest committer and any prover, which is given both keys. -/
def wrongExp (i : I) (Pt : IVK × ISK → OComp lam (X × Pf)) : OComp lam (Bool × X) :=
  (A.C i).bind fun k => (Pt k).bind fun o => (A.V k.1 o.1 o.2).bind fun b => .pure (b, o.1)

/-- the honest committer as the committer of the binding experiment: its state is both keys -/
def honestC (i : I) : OComp lam (IVK × (IVK × ISK)) := (A.C i).mapO fun k => (k.1, k)

theorem queryBound_honestC (i : I) {tC : ℕ} (h : (A.C i).QueryBound tC) :
    (honestC A i).QueryBound tC :=
  OComp.QueryBound.mapO _ _ tC h

/-- the binding experiment with the honest committer, unfolded -/
theorem bindingExp_honestC (i : I) (Pt : IVK × ISK → OComp lam (X × Pf)) :
    bindingExp A E (honestC A i) Pt =
      (A.C i).withTrace.bind fun o =>
        (Pt o.1).withTrace.bind fun o' =>
            (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
                .pure ⟨b, E.Ei o.1.1 o.2, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ := by
  show ((A.C i).mapO fun k => (k.1, k)).withTrace.bind (fun o =>
      (Pt o.1.2).withTrace.bind fun o' =>
        (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
              E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)) = _
  rw [OComp.withTrace_mapO, OComp.mapO_bind]

variable {R A E}

/-! ## Whether what is extracted from the honest key has x in its language -/

open Classical in
/-- Let the scheme have completeness error α and index binding ε for E, let (i, x, w) be in the
relation, let the honest committer at i make at most tC queries, and the honest prover at (x, w) at
most tP0 under every key with the property `good`, which every key that C(i) can output has. Then
the index extracted from the honest committer's key and trace has x in its language, except with
probability α + ε(tC, tP0). (π₀: any proof; the type of proofs must not be empty.) -/
theorem honest_extracts {α : ℝ≥0∞} {ε : ℕ → ℕ → ℝ≥0∞} (hc : HasCompletenessError R A α)
    (hb : HasIndexBindingWith R A E ε) {i : I} {x : X} {w : W} (hr : R.rel i x w) {tC tP0 : ℕ}
    (hC : (A.C i).QueryBound tC) (good : ISK → Prop)
    (hg : ∀ f, ∀ k ∈ ((A.C i).run f).support, good k.2)
    (hP : ∀ isk, good isk → (A.P isk x w).QueryBound tP0) (π₀ : Pf) :
    Pr (A.C i).withTrace (fun _ => {o | x ∉ R.L (E.Ei o.1.1 o.2)}) ≤ α + ε tC tP0 := by
  let Pt : IVK × ISK → OComp lam (X × Pf) := fun k =>
    if good k.2 then (A.P k.2 x w).mapO fun π => (x, π) else .pure (x, π₀)
  have hPt : ∀ k, (Pt k).QueryBound tP0 := by
    intro k
    show (if good k.2 then
      (A.P k.2 x w).mapO fun π => (x, π) else .pure (x, π₀) : OComp lam (X × Pf)).QueryBound tP0
    split
    · exact OComp.QueryBound.mapO _ _ tP0 (hP _ ‹_›)
    · trivial
  refine le_trans ?_
    (add_le_add (hc i x w hr) (hb tC tP0 _ (honestC A i) Pt (queryBound_honestC A i hC) hPt))
  refine Pr_le_add _ _ _ _ _ _ fun f => ?_
  rw [bindingExp_honestC]
  have e1 : prob ((completenessExp A i x w).run f) {b | b = false} =
      expect ((A.C i).withTrace.run f) fun o =>
        prob ((sessionExp A o.1.1 o.1.2 x w).run f) {b | b = false} := by
    rw [expect_withTrace f (A.C i) fun k => prob ((sessionExp A k.1 k.2 x w).run f) {b | b = false}]
    show prob (((A.C i).bind fun key => sessionExp A key.1 key.2 x w).run f) _ = _
    rw [run_bind, prob_bind]
  rw [e1, run_bind, prob_bind, ← expect_add, prob_eq_expect]
  refine expect_le_on_support _ fun o ho => ?_
  have hgo : good o.1.2 := hg f o.1 (mem_support_withTrace f _ o ho)
  split_ifs with hx
  swap
  · exact zero_le _
  have hx' : x ∉ R.L (E.Ei o.1.1 o.2) := hx
  have ePt : Pt o.1 = (A.P o.1.2 x w).mapO fun π => (x, π) := if_pos hgo
  rw [ePt, OComp.withTrace_mapO, OComp.mapO_bind, run_bind, prob_bind]
  have e2 : ∀ o' : Pf × Trace lam,
      prob (((A.V o.1.1 x o'.1).bind fun b =>
            (.pure ⟨b, E.Ei o.1.1 o.2, x,
                E.Ew o.1.1 o.2 x o'.1 o'.2⟩ : OComp lam (BindingOutcome I X W))).run f)
          (bindingBad R) =
        prob ((A.V o.1.1 x o'.1).run f) {b | b = false}ᶜ := by
    intro o'
    rw [run_bind, prob_bind, prob_eq_expect]
    refine expect_congr _ fun b => ?_
    show prob (PMF.pure _) _ = _
    rw [prob_pure]
    cases b
    · rw [if_neg (fun h => Bool.noConfusion h.1),
        if_neg (show false ∉ ({b | b = false}ᶜ : Set Bool) from fun h => h rfl)]
    · rw [if_pos ⟨rfl, Or.inl hx'⟩,
        if_pos (show true ∈ ({b | b = false}ᶜ : Set Bool) from fun h => Bool.noConfusion h)]
  simp only [e2]
  rw [expect_withTrace f (A.P o.1.2 x w) fun π => prob ((A.V o.1.1 x π).run f) {b | b = false}ᶜ]
  have e3 : prob ((sessionExp A o.1.1 o.1.2 x w).run f) {b | b = false} =
      expect ((A.P o.1.2 x w).run f) fun π => prob ((A.V o.1.1 x π).run f) {b | b = false} := by
    show prob (((A.P o.1.2 x w).bind fun π => A.V o.1.1 x π).run f) _ = _
    rw [run_bind, prob_bind]
  rw [e3, ← expect_add]
  refine le_of_eq ?_
  rw [expect_congr _ fun π => prob_add_compl ((A.V o.1.1 x π).run f) {b | b = false}, expect_const]

/-! ## A wrong answer under an honest key -/

open Classical in
/-- The step with the cheating prover. If for every index the answer is a function of the question,
then Pr[ b = 1, key x' = key x, val x' ≠ val x ] in `wrongExp` is at most Pr[ x ∉ L(i*) ] for the
honest committer plus the probability of the bad event of index binding with the honest committer
and this prover. -/
theorem wrong_le (key : X → K) (val : X → Y)
    (huniq : ∀ i x x', x ∈ R.L (some i) → x' ∈ R.L (some i) → key x = key x' → val x = val x')
    (i : I) (x : X) (Pt : IVK × ISK → OComp lam (X × Pf)) :
    Pr (wrongExp A i Pt) (fun _ => {o | o.1 = true ∧ key o.2 = key x ∧ val o.2 ≠ val x}) ≤
      Pr (A.C i).withTrace (fun _ => {o | x ∉ R.L (E.Ei o.1.1 o.2)}) +
        Pr (bindingExp A E (honestC A i) Pt) (fun _ => bindingBad R) := by
  refine Pr_le_add _ _ _ _ _ _ fun f => ?_
  rw [bindingExp_honestC]
  have e1 : prob ((wrongExp A i Pt).run f) {o | o.1 = true ∧ key o.2 = key x ∧ val o.2 ≠ val x} =
      expect ((A.C i).withTrace.run f) fun o =>
        prob (((Pt o.1).bind fun o' =>
              (A.V o.1.1 o'.1 o'.2).bind fun b => (.pure (b, o'.1) : OComp lam (Bool × X))).run f)
            {o | o.1 = true ∧ key o.2 = key x ∧ val o.2 ≠ val x} := by
    rw [expect_withTrace f (A.C i) fun k =>
        prob (((Pt k).bind fun o' =>
            (A.V k.1 o'.1 o'.2).bind fun b => (.pure (b, o'.1) : OComp lam (Bool × X))).run f)
          {o | o.1 = true ∧ key o.2 = key x ∧ val o.2 ≠ val x}]
    unfold wrongExp
    rw [run_bind, prob_bind]
  rw [e1, run_bind (c := (A.C i).withTrace), prob_bind,
    prob_eq_expect ((A.C i).withTrace.run f), ← expect_add]
  refine expect_mono _ fun o => ?_
  split_ifs with hx
  · exact le_trans (prob_le_one _ _) le_self_add
  have hx' : x ∈ R.L (E.Ei o.1.1 o.2) := by
    by_contra hn
    exact hx hn
  rw [zero_add, run_bind, prob_bind, run_bind, prob_bind, ← expect_withTrace f (Pt o.1)]
  refine expect_mono _ fun o' => ?_
  rw [run_bind, prob_bind, run_bind, prob_bind]
  refine expect_mono _ fun b => ?_
  show prob (PMF.pure _) _ ≤ prob (PMF.pure _) _
  rw [prob_pure, prob_pure]
  split_ifs with h1 h2
  · exact le_refl _
  · exfalso
    refine h2 ⟨h1.1, Or.inl fun hin => ?_⟩
    cases hE : E.Ei o.1.1 o.2 with
    | none => rw [hE] at hx'; exact hx'
    | some j =>
      have a1 : x ∈ R.L (some j) := hE ▸ hx'
      have a2 : o'.1.1 ∈ R.L (some j) := hE ▸ hin
      exact h1.2.2 (huniq j _ _ a2 a1 h1.2.1)
  · exact zero_le _
  · exact le_refl _

/-- Under the hypotheses of `honest_extracts`, and if for every index the answer is a function of
the question: for every prover with at most tP queries, which is given both keys, a wrong answer to
the question of x is accepted with probability at most α + ε(tC, tP0) + ε(tC, tP). -/
theorem wrong_answer {α : ℝ≥0∞} {ε : ℕ → ℕ → ℝ≥0∞} (hc : HasCompletenessError R A α)
    (hb : HasIndexBindingWith R A E ε) (key : X → K) (val : X → Y)
    (huniq : ∀ i x x', x ∈ R.L (some i) → x' ∈ R.L (some i) → key x = key x' → val x = val x')
    {i : I} {x : X} {w : W} (hr : R.rel i x w) {tC tP0 tP : ℕ} (hC : (A.C i).QueryBound tC)
    (good : ISK → Prop) (hg : ∀ f, ∀ k ∈ ((A.C i).run f).support, good k.2)
    (hP : ∀ isk, good isk → (A.P isk x w).QueryBound tP0) (π₀ : Pf)
    (Pt : IVK × ISK → OComp lam (X × Pf)) (hPt : ∀ k, (Pt k).QueryBound tP) :
    Pr (wrongExp A i Pt) (fun _ => {o | o.1 = true ∧ key o.2 = key x ∧ val o.2 ≠ val x}) ≤
      α + ε tC tP0 + ε tC tP :=
  le_trans (wrong_le (E := E) key val huniq i x Pt)
    (add_le_add (honest_extracts hc hb hr hC good hg hP π₀)
      (hb tC tP _ (honestC A i) Pt (queryBound_honestC A i hC) hPt))

/-! ## The stronger statement, from i* = i for the honest committer -/

open Classical in
/-- **The stronger statement, from the optional requirement i* = i for the honest committer**
(`HasExtractionError`, ZKCP/Optional.lean) with error δ, and index binding ε for E. Let the honest
committer at i make at most tC queries. For every prover with at most tP queries, which is given
both keys and chooses its instance after key and oracle, a false instance is accepted with
probability at most δ + ε(tC, tP). No completeness, no budget of the honest prover and no `good` is
needed. -/
theorem false_instance_of_extraction {δ : ℝ≥0∞} {ε : ℕ → ℕ → ℝ≥0∞} (he : HasExtractionError A E δ)
    (hb : HasIndexBindingWith R A E ε) (i : I) {tC tP : ℕ} (hC : (A.C i).QueryBound tC)
    (Pt : IVK × ISK → OComp lam (X × Pf)) (hPt : ∀ k, (Pt k).QueryBound tP) :
    Pr (wrongExp A i Pt) (fun _ => {o | o.1 = true ∧ o.2 ∉ R.L (some i)}) ≤ δ + ε tC tP := by
  refine le_trans ?_
    (add_le_add (he i) (hb tC tP _ (honestC A i) Pt (queryBound_honestC A i hC) hPt))
  refine Pr_le_add _ _ _ _ _ _ fun f => ?_
  rw [bindingExp_honestC]
  have e1 : prob ((wrongExp A i Pt).run f) {o | o.1 = true ∧ o.2 ∉ R.L (some i)} =
      expect ((A.C i).withTrace.run f) fun o =>
        prob (((Pt o.1).bind fun o' =>
              (A.V o.1.1 o'.1 o'.2).bind fun b => (.pure (b, o'.1) : OComp lam (Bool × X))).run f)
            {o | o.1 = true ∧ o.2 ∉ R.L (some i)} := by
    rw [expect_withTrace f (A.C i) fun k =>
        prob (((Pt k).bind fun o' =>
            (A.V k.1 o'.1 o'.2).bind fun b => (.pure (b, o'.1) : OComp lam (Bool × X))).run f)
          {o | o.1 = true ∧ o.2 ∉ R.L (some i)}]
    unfold wrongExp
    rw [run_bind, prob_bind]
  rw [e1, run_bind (c := (A.C i).withTrace), prob_bind,
    prob_eq_expect ((A.C i).withTrace.run f), ← expect_add]
  refine expect_mono _ fun o => ?_
  split_ifs with hx
  · exact le_trans (prob_le_one _ _) le_self_add
  have hx' : E.Ei o.1.1 o.2 = some i := by
    by_contra hn
    exact hx hn
  rw [zero_add, run_bind, prob_bind, run_bind, prob_bind, ← expect_withTrace f (Pt o.1)]
  refine expect_mono _ fun o' => ?_
  rw [run_bind, prob_bind, run_bind, prob_bind]
  refine expect_mono _ fun b => ?_
  show prob (PMF.pure _) _ ≤ prob (PMF.pure _) _
  rw [prob_pure, prob_pure]
  split_ifs with h1 h2
  · exact le_refl _
  · exfalso
    refine h2 ⟨h1.1, Or.inl ?_⟩
    show o'.1.1 ∉ R.L (E.Ei o.1.1 o.2)
    rw [hx']
    exact h1.2
  · exact zero_le _
  · exact le_refl _

end ZKCP
