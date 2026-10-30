-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/SameRun.lean: Defs.lean's properties depend on honest algorithms only via output distributions.

Two schemes (C, P, V) and (C', P', V') with the same types are in the relation `Arg.SameRun` if, for
every oracle f and every input, C and C' have the same output distribution over their coins, and so
have P and P', V and V'. How many queries they make, and which, is not compared. Then every property
below is true of the one if and only if it is true of the other, with the same relation, the same
extractor, the same simulator and the same bounds: ZKCP/Defs.lean, completeness
(hasCompletenessError_iff, isPerfectlyComplete_iff, hasRefinedCompletenessError_iff), index binding
(hasIndexBindingWith_iff, hasIndexBinding_iff), index privacy (hasIndexPrivacyWith_iff,
hasIndexPrivacy_iff) and its stronger form (hasStrongIndexPrivacyWith_iff), the primitive
(isZKCPArg_iff, isZKCPArgRefined_iff) and the named form (isZKCPArgWith_iff); completeness against
an adaptive environment (ZKCP/Adaptive.lean); index binding for many sessions (ZKCP/Optional.lean).
Why. In each of these experiments the honest algorithms enter by `bind` only: they are run, their
outputs passed on, and no trace of theirs is taken; the traces that the extractor gets are those of
the adversarial committer and prover, the view contains the queries of the adversarial verifier. So
for every f the two experiments have the same output distribution, and a probability `Pr` depends on
nothing else (`Pr_congr`).
The exception. The statement that the extracted index is the committed one (`HasExtractionError`,
ZKCP/Optional.lean) gives the extractor the trace of the honest committer.
`hasExtractionError_iff_of` names a condition that suffices there: that for every f what the
extractor computes from key and trace has the same distribution.

Limits: The relation does not preserve properties of the algorithms themselves. A bound on the
number of queries of an honest algorithm, or that the verifier draws no coin, can be true of one
scheme and false of another in the relation; and the exception above is real. The last section:
`Not.same`, `Not.queryBound`, `Not.drawsNoCoin`, `Not.extraction`. No statement here is on a
construction: nothing here says that two given schemes are in the relation, but for the two toys
`Not.A0`, `Not.A1` of the last section (`Not.same`). In these definitions (exactly: those of the
list above, not `HasExtractionError`) budgets of queries are those of the adversaries, and the
queries of the honest algorithms occur nowhere. (The bounds of a theorem of this library are
formulas whose constants count typed queries of the honest side; that is a matter of the proofs, not
of the definitions.)

After ZKCP/Defs.lean.
Definitions are cited by their names in ZKCP/Defs.lean.
-/
import ZKCP.Lemmas
import ZKCP.Adaptive
import ZKCP.Optional
import ZKCP.Main

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- Two schemes whose algorithms have the same output distribution, for every oracle and every
input. Nothing is said of their queries. -/
structure Arg.SameRun (A A' : Arg lam I X W IVK ISK Pf) : Prop where
  C : ∀ i f, (A.C i).run f = (A'.C i).run f
  P : ∀ isk x w f, (A.P isk x w).run f = (A'.P isk x w).run f
  V : ∀ ivk x π f, (A.V ivk x π).run f = (A'.V ivk x π).run f

/-- A probability of the form Pr depends on the computation through its output distributions
only. -/
theorem Pr_congr {α : Type} {c c' : OComp lam α}
    (h : ∀ f, c.run f = c'.run f) (E : Oracle lam → Set α) : Pr c E = Pr c' E := by
  unfold Pr PrCoins
  simp only [h]

/-- Under hc, hg: c then g, and c' then g', have equal output distributions under f. -/
theorem run_bind_congr {α β : Type} {c c' : OComp lam α} {g g' : α → OComp lam β} (f : Oracle lam)
    (hc : c.run f = c'.run f) (hg : ∀ a, (g a).run f = (g' a).run f) :
    (c.bind g).run f = (c'.bind g').run f := by
  rw [run_bind, run_bind, hc]
  simp only [hg]

namespace Arg.SameRun
variable {A A' : Arg lam I X W IVK ISK Pf} (h : A.SameRun A')
include h

omit h in
theorem refl (A : Arg lam I X W IVK ISK Pf) : A.SameRun A :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem trans {A'' : Arg lam I X W IVK ISK Pf} (h' : A'.SameRun A'') : A.SameRun A'' :=
  ⟨fun i f => (h.C i f).trans (h'.C i f),
    fun k x w f => (h.P k x w f).trans (h'.P k x w f),
    fun v x π f => (h.V v x π f).trans (h'.V v x π f)⟩

theorem symm : A'.SameRun A :=
  ⟨fun i f => (h.C i f).symm, fun k x w f => (h.P k x w f).symm, fun v x π f => (h.V v x π f).symm⟩

/-! ## The experiments -/

theorem sessionExp_run (ivk : IVK) (isk : ISK) (x : X) (w : W) (f : Oracle lam) :
    (sessionExp A ivk isk x w).run f = (sessionExp A' ivk isk x w).run f :=
  run_bind_congr f (h.P isk x w f) fun π => h.V ivk x π f

theorem completenessExp_run (i : I) (x : X) (w : W) (f : Oracle lam) :
    (completenessExp A i x w).run f = (completenessExp A' i x w).run f :=
  run_bind_congr f (h.C i f) fun key => h.sessionExp_run key.1 key.2 x w f

theorem bindingExp_run {St : Type} (E : Extractor lam I X W IVK Pf) (Ct : OComp lam (IVK × St))
    (Pt : St → OComp lam (X × Pf)) (f : Oracle lam) :
    (bindingExp A E Ct Pt).run f = (bindingExp A' E Ct Pt).run f :=
  run_bind_congr f rfl fun _ =>
    run_bind_congr f rfl fun _ => run_bind_congr f (h.V _ _ _ f) fun _ => rfl

theorem realLoop_run (Z : ViewEnv lam IVK X W Pf) (isk : ISK) (f : Oracle lam) :
    ∀ (Vt : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf),
      (realLoop A Z isk Vt n v).run f = (realLoop A' Z isk Vt n v).run f
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      simp only [realLoop, OComp.run]
      exact realLoop_run Z isk f (k (f q)) n _
  | .sample m k, n, v => by
      simp only [realLoop, OComp.run]
      exact congrArg _ (funext fun r => realLoop_run Z isk f (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop]
      cases Z v with
      | none => rfl
      | some xw =>
        exact run_bind_congr f (h.P isk xw.1 xw.2 f) fun π => realLoop_run Z isk f (k xw.1 π) n _

theorem realExp_run (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X W Pf) (i : I)
    (N : ℕ) (f : Oracle lam) :
    (realExp A Vt Z i N).run f = (realExp A' Vt Z i N).run f :=
  run_bind_congr f (h.C i f) fun key => h.realLoop_run Z key.2 f (Vt key.1) N _

theorem adaptiveLoop_run (ivk : IVK) (isk : ISK) (f : Oracle lam) :
    ∀ (E : CEnv lam X W Pf) (n : ℕ),
      (adaptiveLoop A ivk isk E n).run f = (adaptiveLoop A' ivk isk E n).run f
  | .halt, _ => rfl
  | .query q k, n => by
      simp only [adaptiveLoop, OComp.run]
      exact adaptiveLoop_run ivk isk f (k (f q)) n
  | .sample m k, n => by
      simp only [adaptiveLoop, OComp.run]
      exact congrArg _ (funext fun r => adaptiveLoop_run ivk isk f (k r) n)
  | .session _ _ _, 0 => rfl
  | .session x w k, n + 1 => by
      simp only [adaptiveLoop]
      exact run_bind_congr f (h.P isk x w f) fun π =>
        run_bind_congr f (h.V ivk x π f) fun b =>
          run_bind_congr f (adaptiveLoop_run ivk isk f (k π b) n) fun _ => rfl

theorem adaptiveExp_run (E : IVK → CEnv lam X W Pf) (i : I) (N : ℕ) (f : Oracle lam) :
    (adaptiveExp A E i N).run f = (adaptiveExp A' E i N).run f :=
  run_bind_congr f (h.C i f) fun key => h.adaptiveLoop_run key.1 key.2 f (E key.1) N

theorem verifyAll_run (ivk : IVK) (f : Oracle lam) :
    ∀ l : List (X × Pf), (verifyAll A ivk l).run f = (verifyAll A' ivk l).run f
  | [] => rfl
  | (x, π) :: rest =>
    run_bind_congr f (h.V ivk x π f) fun _ =>
      run_bind_congr f (verifyAll_run ivk f rest) fun _ => rfl

theorem multiBindingExp_run {St : Type} (Ei : IVK → Trace lam → Option I)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (List (X × Pf))) (f : Oracle lam) :
    (multiBindingExp A Ei Ct Pt).run f = (multiBindingExp A' Ei Ct Pt).run f :=
  run_bind_congr f rfl fun _ =>
    run_bind_congr f rfl fun pairs => run_bind_congr f (h.verifyAll_run _ f pairs) fun _ => rfl

/-! ## The properties: the same relation, extractor, simulator and bounds on both sides -/

variable (R : IndexedRelation I X W PP)

theorem hasCompletenessError_iff (α : ℝ≥0∞) :
    HasCompletenessError R A α ↔ HasCompletenessError R A' α := by
  unfold HasCompletenessError
  simp only [Pr_congr (h.completenessExp_run _ _ _)]

theorem isPerfectlyComplete_iff : IsPerfectlyComplete R A ↔ IsPerfectlyComplete R A' :=
  h.hasCompletenessError_iff R 0

theorem badKeys_eq (αP : ℝ≥0∞) (i : I) (f : Oracle lam) :
    badKeys R A αP i f = badKeys R A' αP i f := by
  unfold badKeys PrCoins
  simp only [h.sessionExp_run]

theorem hasRefinedCompletenessError_iff (αC αP : ℝ≥0∞) :
    HasRefinedCompletenessError R A αC αP ↔ HasRefinedCompletenessError R A' αC αP := by
  unfold HasRefinedCompletenessError
  simp only [h.badKeys_eq R, Pr_congr (h.C _)]

theorem hasIndexBindingWith_iff (E : Extractor lam I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWith R A E ε ↔ HasIndexBindingWith R A' E ε := by
  unfold HasIndexBindingWith
  simp only [Pr_congr (h.bindingExp_run E _ _)]

theorem hasIndexBinding_iff (ε : ℕ → ℕ → ℝ≥0∞) : HasIndexBinding R A ε ↔ HasIndexBinding R A' ε :=
  exists_congr fun E => h.hasIndexBindingWith_iff R E ε

theorem privacyFor_iff (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (i : I) (Z : ViewEnv lam IVK X W Pf) :
    PrivacyFor R A S ζ i Z ↔ PrivacyFor R A' S ζ i Z := by
  unfold PrivacyFor
  simp only [Pr_congr (h.realExp_run _ Z i _)]

theorem hasIndexPrivacyWith_iff (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) :
    HasIndexPrivacyWith R A S ζ ↔ HasIndexPrivacyWith R A' S ζ := by
  unfold HasIndexPrivacyWith
  simp only [h.privacyFor_iff R S ζ]

theorem hasStrongIndexPrivacyWith_iff (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) :
    HasStrongIndexPrivacyWith R A S ζ ↔ HasStrongIndexPrivacyWith R A' S ζ := by
  unfold HasStrongIndexPrivacyWith
  simp only [h.privacyFor_iff R S ζ]

theorem hasIndexPrivacy_iff (ζ : ℕ → ℕ → ℝ≥0∞) : HasIndexPrivacy R A ζ ↔ HasIndexPrivacy R A' ζ :=
  exists_congr fun S => h.hasIndexPrivacyWith_iff R S ζ

/-- For schemes in the relation, `IsZKCPArgWith` holds of one exactly if it holds of the other, with
the same extractor, simulator and three bounds. -/
theorem isZKCPArgWith_iff (E : Extractor lam I X W IVK Pf) (S : Simulator lam PP IVK X Pf)
    (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    IsZKCPArgWith R A E S α ε ζ ↔ IsZKCPArgWith R A' E S α ε ζ :=
  ⟨fun a =>
      ⟨(h.hasCompletenessError_iff R α).1 a.completeness,
        (h.hasIndexBindingWith_iff R E ε).1 a.indexBinding,
        (h.hasStrongIndexPrivacyWith_iff R S ζ).1 a.indexPrivacy⟩,
    fun a =>
      ⟨(h.hasCompletenessError_iff R α).2 a.completeness,
        (h.hasIndexBindingWith_iff R E ε).2 a.indexBinding,
        (h.hasStrongIndexPrivacyWith_iff R S ζ).2 a.indexPrivacy⟩⟩

/-- For schemes in the relation, `IsZKCPArg` holds of one exactly if it holds of the other. -/
theorem isZKCPArg_iff (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    IsZKCPArg R A α ε ζ ↔ IsZKCPArg R A' α ε ζ :=
  ⟨fun a =>
      ⟨(h.hasCompletenessError_iff R α).1 a.completeness,
        (h.hasIndexBinding_iff R ε).1 a.indexBinding,
        (h.hasIndexPrivacy_iff R ζ).1 a.indexPrivacy⟩,
    fun a =>
      ⟨(h.hasCompletenessError_iff R α).2 a.completeness,
        (h.hasIndexBinding_iff R ε).2 a.indexBinding,
        (h.hasIndexPrivacy_iff R ζ).2 a.indexPrivacy⟩⟩

theorem isZKCPArgRefined_iff (αC αP : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    IsZKCPArgRefined R A αC αP ε ζ ↔ IsZKCPArgRefined R A' αC αP ε ζ :=
  ⟨fun a =>
      ⟨(h.hasRefinedCompletenessError_iff R αC αP).1 a.completeness,
        (h.hasIndexBinding_iff R ε).1 a.indexBinding,
        (h.hasIndexPrivacy_iff R ζ).1 a.indexPrivacy⟩,
    fun a =>
      ⟨(h.hasRefinedCompletenessError_iff R αC αP).2 a.completeness,
        (h.hasIndexBinding_iff R ε).2 a.indexBinding,
        (h.hasIndexPrivacy_iff R ζ).2 a.indexPrivacy⟩⟩

/-- For schemes in the relation, completeness against an adaptive environment holds of one exactly
if it holds of the other. -/
theorem hasAdaptiveCompletenessError_iff (α : ℕ → ℕ → ℝ≥0∞) :
    HasAdaptiveCompletenessError R A α ↔ HasAdaptiveCompletenessError R A' α := by
  unfold HasAdaptiveCompletenessError
  simp only [Pr_congr (h.adaptiveExp_run _ _ _)]

/-- For schemes in the relation, index binding for many sessions holds of one exactly if it holds of
the other. -/
theorem hasSessionAugmentedBinding_iff (ε : ℕ → ℕ → ℕ → ℝ≥0∞) :
    HasSessionAugmentedBinding R A ε ↔ HasSessionAugmentedBinding R A' ε := by
  unfold HasSessionAugmentedBinding
  simp only [Pr_congr (h.multiBindingExp_run _ _ _)]

end Arg.SameRun

/-! ## The exception: a property that reads the trace of the honest committer -/

/-- The statement that the extracted index is the committed one runs the honest committer with its
trace. That two committers have the same outputs says nothing of their traces; that, for every
oracle, what the extractor computes from key and trace has the same distribution suffices. -/
theorem hasExtractionError_iff_of {A A' : Arg lam I X W IVK ISK Pf} (E : Extractor lam I X W IVK Pf)
    (hE : ∀ i f, ((A.C i).withTrace.run f).map (fun o => E.Ei o.1.1 o.2) =
      ((A'.C i).withTrace.run f).map (fun o => E.Ei o.1.1 o.2)) (δ : ℝ≥0∞) :
    HasExtractionError A E δ ↔ HasExtractionError A' E δ := by
  have key : ∀ (B : Arg lam I X W IVK ISK Pf) (i : I) (f : Oracle lam),
      prob ((B.C i).withTrace.run f) {o | E.Ei o.1.1 o.2 ≠ some i} =
        prob (((B.C i).withTrace.run f).map fun o => E.Ei o.1.1 o.2)
          {j | j ≠ some i} := fun B i f => by
    unfold prob
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  unfold HasExtractionError Pr PrCoins
  simp only [key, hE]

/-! ## What the relation does not carry -/

namespace Arg.SameRun.Not

/-- a scheme whose algorithms make no query and draw no coin -/
def A0 (lam : ℕ) : Arg lam Unit Unit Unit Unit Unit Unit where
  C := fun _ => .pure ((), ())
  P := fun _ _ _ => .pure ()
  V := fun _ _ _ => .pure true

/-- a scheme whose committer and verifier make a query, and whose verifier draws a coin, to no
effect -/
def A1 (lam : ℕ) : Arg lam Unit Unit Unit Unit Unit Unit where
  C := fun _ => .query [] fun _ => .pure ((), ())
  P := fun _ _ _ => .pure ()
  V := fun _ _ _ => .query [] fun _ => .sample 1 fun _ => .pure true

theorem same (lam : ℕ) : (A0 lam).SameRun (A1 lam) := by
  refine ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ f => ?_⟩
  simp [A0, A1, OComp.run]

/-- A bound on the honest verifier's queries is not carried. -/
theorem queryBound (lam : ℕ) :
    ((A0 lam).V () () ()).QueryBound 0 ∧ ¬ ((A1 lam).V () () ()).QueryBound 0 :=
  ⟨trivial, fun h => h⟩

/-- That the verifier draws no coin is not carried. -/
theorem drawsNoCoin (lam : ℕ) :
    ((A0 lam).V () () ()).DrawsNoCoin ∧ ¬ ((A1 lam).V () () ()).DrawsNoCoin :=
  ⟨trivial, fun h => h (fun _ => false)⟩

/-- an extractor that returns an index iff the committer has made a query -/
def E (lam : ℕ) : Extractor lam Unit Unit Unit Unit Unit where
  Ei := fun _ tr => if tr = [] then none else some ()
  Ew := fun _ _ _ _ _ => ()

/-- That the extracted index is the committed one is not carried: the exception is real. -/
theorem extraction (lam : ℕ) :
    HasExtractionError (A1 lam) (E lam) 0 ∧ ¬ HasExtractionError (A0 lam) (E lam) 0 := by
  refine ⟨fun i => ?_, fun h => ?_⟩
  · simp [Pr, PrCoins, A1, E, OComp.withTrace, OComp.bind, OComp.run, prob]
  · have := h ()
    simp [Pr, PrCoins, A0, E, OComp.withTrace, OComp.run, prob] at this

end Arg.SameRun.Not

end ZKCP
