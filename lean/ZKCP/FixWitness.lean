-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/FixWitness.lean: a scheme whose prover computes its witness.

`Arg.fixWitness A witness` is the scheme A (ZKCP/Defs.lean) with a prover that is handed no witness:
it computes `witness i x` from the index i, which it reads off the prover's key (`ISK`, here
`I × K`), and the instance x, and then runs A's prover. The committer and the verifier are A's.
Let R be A's relation, and `IsTrue i x` a property such that every (i, x, w) in R has `IsTrue i x`
and `witness i x` is a witness wherever `IsTrue i x` holds. Then, for the relation without witnesses
`languageRelation IsTrue` (ZKCP/LanguageRelation.lean), the new scheme has what A has for R, with
the same bounds:
  `HasCompletenessError.fixWitness`           completeness
  `HasIndexBindingWith.fixWitness`            index binding, with the index part of A's extractor
  `HasIndexBindingWith.fixWitness_of_event`   the same from a bound on the event "the verifier
                                              accepts and no index was extracted at which the
                                              instance is true"
  `HasStrongIndexPrivacyWith.fixWitness`      index privacy in the stronger form, with the same
                                              simulator, for an R without public parameters
  `HasExtractionError.fixWitness`             the honest committer's index is the extracted one
  `IsZKCPArgWith.fixWitness`                  the first, the second and the fourth together
Completeness and privacy run the honest prover under an honest key. They need that an honest
prover's key begins with the committed index; this is taken from `Arg.CommitsFromCoins`
(ZKCP/CommitsFromCoins.lean).
Limits. The file says nothing on how `witness` is computed or what that costs. Index binding is a
statement on the language alone: nothing is extracted but the index. Completeness says nothing on an
instance that is not true at the index. Nor does privacy: its environments choose true instances
only, and whether an instance is true depends on the index.
Words: the query log is the `Trace` that `withTrace` returns (ZKCP/Defs.lean).
-/
import ZKCP.LanguageRelation
import ZKCP.CommitsFromCoins

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W K IVK Pf : Type}

/-! ## 1. The scheme -/

/-- The same scheme with a prover that computes its witness from the index and the instance. It
takes the first part of the prover's key for the index; that this is the committed index is asked
only from section 3 on. -/
def Arg.fixWitness (A : Arg lam I X W IVK (I × K) Pf) (witness : I → X → W) :
    Arg lam I X Unit IVK (I × K) Pf where
  C := A.C
  P := fun secret x _ => A.P secret x (witness secret.1 x)
  V := A.V

/-- The extractor for the relation without witnesses: the index part of E. -/
def Extractor.forgetWitness (E : Extractor lam I X W IVK Pf) : Extractor lam I X Unit IVK Pf :=
  ⟨E.Ei, fun _ _ _ _ _ => ()⟩

/-- What the experiment of index binding produces, without the witness. -/
def BindingOutcome.forgetWitness (o : BindingOutcome I X W) : BindingOutcome I X Unit :=
  ⟨o.accept, o.iStar, o.x, ()⟩

/-- The environment that chooses the instances of Z and adds the computed witness to each. -/
def ViewEnv.addWitness (Z : ViewEnv lam IVK X Unit Pf) (witness : X → W) :
    ViewEnv lam IVK X W Pf :=
  fun v => (Z v).map fun xu => (xu.1, witness xu.1)

section Scheme
variable (A : Arg lam I X W IVK (I × K) Pf) (witness : I → X → W)

/-- The committer is A's. -/
theorem fixWitness_C : (A.fixWitness witness).C = A.C := rfl

/-- The verifier is A's. So it makes the same queries, and it samples nothing if A's does not. -/
theorem fixWitness_V : (A.fixWitness witness).V = A.V := rfl

/-- The prover is A's at the computed witness. So a bound on the queries of A's prover at all
witnesses holds for it. -/
theorem fixWitness_P (secret : I × K) (x : X) (u : Unit) :
    (A.fixWitness witness).P secret x u = A.P secret x (witness secret.1 x) := rfl

end Scheme

/-! ## 2. Index binding -/

/-- The experiment of index binding is A's, with the witness left out at the end. -/
theorem bindingExp_fixWitness (A : Arg lam I X W IVK (I × K) Pf) (witness : I → X → W)
    (E : Extractor lam I X W IVK Pf) {St : Type} (Ct : OComp lam (IVK × St))
    (Pt : St → OComp lam (X × Pf)) :
    bindingExp (A.fixWitness witness) E.forgetWitness Ct Pt
      = (bindingExp A E Ct Pt).mapO BindingOutcome.forgetWitness := by
  show (Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
      (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
        .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1, ()⟩ : BindingOutcome I X Unit))
    = (Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
      (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
        .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ :
          BindingOutcome I X W)).mapO BindingOutcome.forgetWitness
  rw [OComp.bind_mapO]
  refine congrArg _ (funext fun o => ?_)
  rw [OComp.bind_mapO]
  refine congrArg _ (funext fun o' => ?_)
  rw [OComp.bind_mapO]
  rfl

section Binding
variable {A : Arg lam I X W IVK (I × K) Pf} {E : Extractor lam I X W IVK Pf}
  {ε : ℕ → ℕ → ℝ≥0∞} {IsTrue : I → X → Prop}

/-- Index binding from a bound on the event "the verifier accepts, and no index was extracted at
which the instance is true" in A's experiment. The same bound; the index part of the same
extractor. -/
theorem HasIndexBindingWith.fixWitness_of_event (witness : I → X → W)
    (h : ∀ (tC tP : ℕ) (St : Type) (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
        Pr (bindingExp A E Ct Pt)
          (fun _ => {o | o.accept = true ∧ ¬ ∃ i, o.iStar = some i ∧ IsTrue i o.x}) ≤ ε tC tP) :
    HasIndexBindingWith (languageRelation IsTrue) (A.fixWitness witness) E.forgetWitness ε := by
  intro tC tP St Ct Pt hC hP
  rw [bindingExp_fixWitness, Pr_mapO, bindingBad_languageRelation]
  exact h tC tP St Ct Pt hC hP

/-- Index binding from A's index binding for a relation R all of whose triples (i, x, w) have
`IsTrue i x`. The same bound; the index part of the same extractor. -/
theorem HasIndexBindingWith.fixWitness {PP : Type} {R : IndexedRelation I X W PP}
    (witness : I → X → W) (hl : ∀ i x w, R.rel i x w → IsTrue i x)
    (h : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith (languageRelation IsTrue) (A.fixWitness witness) E.forgetWitness ε := by
  refine HasIndexBindingWith.fixWitness_of_event witness fun tC tP St Ct Pt hC hP =>
    le_trans (Pr_mono _ ?_) (h tC tP St Ct Pt hC hP)
  rintro ⟨b, _ | i, x, w⟩ ⟨hb, hn⟩
  · exact ⟨hb, Or.inl (Set.notMem_empty x)⟩
  · exact ⟨hb, Or.inl fun ⟨w', hw'⟩ => hn ⟨i, rfl, hl i x w' hw'⟩⟩

/-- What the extractor gives from the honest committer's key and query log is unchanged. So the
extraction error δ (`HasExtractionError`) carries over. -/
theorem HasExtractionError.fixWitness (witness : I → X → W) {δ : ℝ≥0∞}
    (h : HasExtractionError A E δ) :
    HasExtractionError (A.fixWitness witness) E.forgetWitness δ := h

end Binding

/-! ## 3. Under an honest key -/

section Honest
variable {bound : ℕ} {A : Arg lam I X W IVK (I × Fin (bound + 1)) Pf}
  {commit : I → Fin (bound + 1) → OComp lam IVK}

/-- The committer keeps its form. -/
theorem Arg.CommitsFromCoins.fixWitness (hC : A.CommitsFromCoins commit) (witness : I → X → W) :
    (A.fixWitness witness).CommitsFromCoins commit := ⟨hC.committer, hC.noCoin⟩

/-- For a committer of the form `Arg.CommitsFromCoins` (`hC`), two continuations of the committer at
the index i that agree on all keys of the prover that begin with i give the same algorithm. -/
theorem Arg.CommitsFromCoins.bind_congr (hC : A.CommitsFromCoins commit) (i : I) {β : Type}
    {F G : IVK × (I × Fin (bound + 1)) → OComp lam β}
    (h : ∀ key coins, F (key, (i, coins)) = G (key, (i, coins))) :
    (A.C i).bind F = (A.C i).bind G := by
  rw [hC.committer i]
  show OComp.sample bound (fun coins =>
      ((commit i coins).mapO fun key => (key, (i, coins))).bind F)
    = OComp.sample bound fun coins => ((commit i coins).mapO fun key => (key, (i, coins))).bind G
  refine congrArg _ (funext fun coins => ?_)
  rw [OComp.mapO_bind, OComp.mapO_bind]
  exact congrArg _ (funext fun key => h key coins)

/-- For a committer of the form `Arg.CommitsFromCoins` (`hC`), the experiment of completeness is A's
at the computed witness. -/
theorem completenessExp_fixWitness (hC : A.CommitsFromCoins commit) (witness : I → X → W) (i : I)
    (x : X) (u : Unit) :
    completenessExp (A.fixWitness witness) i x u = completenessExp A i x (witness i x) := by
  show (A.C i).bind (fun key => sessionExp (A.fixWitness witness) key.1 key.2 x u)
    = (A.C i).bind fun key => sessionExp A key.1 key.2 x (witness i x)
  exact hC.bind_congr i fun _ _ => rfl

/-- Completeness, with the same error, if `witness i x` is a witness wherever `IsTrue i x`, and the
committer has the form `Arg.CommitsFromCoins`. -/
theorem HasCompletenessError.fixWitness {PP : Type} {R : IndexedRelation I X W PP}
    {IsTrue : I → X → Prop} {witness : I → X → W} {α : ℝ≥0∞} (hC : A.CommitsFromCoins commit)
    (hw : ∀ i x, IsTrue i x → R.rel i x (witness i x)) (h : HasCompletenessError R A α) :
    HasCompletenessError (languageRelation IsTrue) (A.fixWitness witness) α := by
  intro i x u hr
  rw [completenessExp_fixWitness hC]
  exact h i x (witness i x) (hw i x hr)

/-! ## 4. Index privacy -/

/-- The sessions of the real experiment under a prover's key that begins with i are A's, for the
environment that adds the computed witness. -/
theorem realLoop_fixWitness (A : Arg lam I X W IVK (I × K) Pf) (witness : I → X → W)
    (Z : ViewEnv lam IVK X Unit Pf) (i : I) (rest : K) :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf),
      realLoop (A.fixWitness witness) Z (i, rest) a n v
        = realLoop A (Z.addWitness (witness i)) (i, rest) a n v
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      simp only [realLoop]
      exact congrArg _ (funext fun r => realLoop_fixWitness A witness Z i rest (k r) n _)
  | .sample m k, n, v => by
      simp only [realLoop]
      exact congrArg _ (funext fun r => realLoop_fixWitness A witness Z i rest (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop, ViewEnv.addWitness]
      cases Z v with
      | none => rfl
      | some xu =>
          exact congrArg ((A.P (i, rest) xu.1 (witness i xu.1)).bind)
            (funext fun π => realLoop_fixWitness A witness Z i rest (k xu.1 π) n _)

/-- For a committer of the form `Arg.CommitsFromCoins` (`hC`), the real experiment is A's, for the
environment that adds the computed witness. -/
theorem realExp_fixWitness (hC : A.CommitsFromCoins commit) (witness : I → X → W)
    (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X Unit Pf) (i : I) (N : ℕ) :
    realExp (A.fixWitness witness) Vt Z i N = realExp A Vt (Z.addWitness (witness i)) i N := by
  show (A.C i).bind (fun key =>
      realLoop (A.fixWitness witness) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩)
    = (A.C i).bind fun key =>
      realLoop A (Z.addWitness (witness i)) key.2 (Vt key.1) N ⟨key.1, [], [], []⟩
  exact hC.bind_congr i fun key coins => realLoop_fixWitness A witness Z i coins (Vt key) N _

/-- The ideal experiment does not read witnesses: its sessions (`idealLoop`). -/
theorem idealLoop_addWitness {PP : Type} (S : Simulator lam PP IVK X Pf)
    (Z : ViewEnv lam IVK X Unit Pf) (witness : X → W) :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop S Z a n v s = idealLoop S (Z.addWitness witness) a n v s
  | .halt, _, _, _ => rfl
  | .query q k, n, v, s => by
      simp only [idealLoop]
      exact congrArg _ (funext fun out => idealLoop_addWitness S Z witness (k out.1) n _ out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop]
      exact congrArg _ (funext fun r => idealLoop_addWitness S Z witness (k r) n _ s)
  | .request _, 0, _, _ => rfl
  | .request k, n + 1, v, s => by
      simp only [idealLoop, ViewEnv.addWitness]
      cases Z v with
      | none => rfl
      | some xu =>
          exact congrArg ((S.prove s xu.1).bind)
            (funext fun out => idealLoop_addWitness S Z witness (k xu.1 out.1) n _ out.2)

/-- The ideal experiment does not read witnesses (`idealExp`; `R : IndexedRelation I X W Unit`). -/
theorem idealExp_addWitness (R : IndexedRelation I X W Unit) (IsTrue : I → X → Prop)
    (S : Simulator lam Unit IVK X Pf) (Vt : IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam IVK X Unit Pf) (witness : X → W) (i : I) (N : ℕ) :
    idealExp (languageRelation IsTrue) S Vt Z i N = idealExp R S Vt (Z.addWitness witness) i N := by
  show (S.init (R.pp i) N).bind (fun out =>
      idealLoop S Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)
    = (S.init (R.pp i) N).bind fun out =>
      idealLoop S (Z.addWitness witness) (Vt out.1) N ⟨out.1, [], [], []⟩ out.2
  exact congrArg _ (funext fun out => idealLoop_addWitness S Z witness (Vt out.1) N _ out.2)

variable {R : IndexedRelation I X W Unit} {IsTrue : I → X → Prop} {witness : I → X → W}
  {S : Simulator lam Unit IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}

/-- Index privacy at one index and one environment: from A's privacy at the environment that adds
the computed witness, for a committer of the form `Arg.CommitsFromCoins` (`hC`) and an R with
`PP = Unit`. The same simulator, the same bound. -/
theorem PrivacyFor.fixWitness (hC : A.CommitsFromCoins commit) {i : I}
    {Z : ViewEnv lam IVK X Unit Pf} (h : PrivacyFor R A S ζ i (Z.addWitness (witness i))) :
    PrivacyFor (languageRelation IsTrue) (A.fixWitness witness) S ζ i Z := by
  intro tV Vt N hV
  rw [realExp_fixWitness hC, idealExp_addWitness R IsTrue S Vt Z (witness i) i N]
  exact h tV Vt N hV

/-- If `witness i x` is a witness wherever `IsTrue i x` (`hw`), an environment that chooses true
instances only, with the computed witnesses added, chooses pairs of the relation only. -/
theorem ViewEnv.IsValid.addWitness (hw : ∀ i x, IsTrue i x → R.rel i x (witness i x)) {i : I}
    {Z : ViewEnv lam IVK X Unit Pf} (hZ : Z.IsValid (languageRelation IsTrue) i) :
    (Z.addWitness (witness i)).IsValid R i := by
  intro v x w e
  have e1 : (Z v).map (fun xu => (xu.1, witness i xu.1)) = some (x, w) := e
  cases hz : Z v with
  | none => rw [hz] at e1; cases e1
  | some xu =>
    rw [hz] at e1
    have e2 : (xu.1, witness i xu.1) = (x, w) := Option.some.inj e1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
    exact hw i xu.1 (hZ v xu.1 xu.2 hz)

/-- Index privacy in the stronger form, under the hypotheses below, with the same simulator and the
same bound. The public parameters of R are the one element of `Unit`, as those of the relation
without witnesses. -/
theorem HasStrongIndexPrivacyWith.fixWitness (hC : A.CommitsFromCoins commit)
    (hw : ∀ i x, IsTrue i x → R.rel i x (witness i x)) (h : HasStrongIndexPrivacyWith R A S ζ) :
    HasStrongIndexPrivacyWith (languageRelation IsTrue) (A.fixWitness witness) S ζ :=
  fun i Z hZ => PrivacyFor.fixWitness hC (h i (Z.addWitness (witness i)) (hZ.addWitness hw))

/-- Completeness, index binding and index privacy together, under the hypotheses below and for an R
with `PP = Unit`, with the same three bounds. -/
theorem IsZKCPArgWith.fixWitness {E : Extractor lam I X W IVK Pf} {α : ℝ≥0∞} {ε : ℕ → ℕ → ℝ≥0∞}
    (hC : A.CommitsFromCoins commit) (hw : ∀ i x, IsTrue i x → R.rel i x (witness i x))
    (hl : ∀ i x w, R.rel i x w → IsTrue i x) (h : IsZKCPArgWith R A E S α ε ζ) :
    IsZKCPArgWith (languageRelation IsTrue) (A.fixWitness witness) E.forgetWitness S α ε ζ :=
  ⟨h.completeness.fixWitness hC hw, h.indexBinding.fixWitness witness hl,
    h.indexPrivacy.fixWitness hC hw⟩

end Honest

end ZKCP
