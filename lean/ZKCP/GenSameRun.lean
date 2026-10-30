-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/GenSameRun.lean: the properties of ZKCP/Gen.lean depend only on the output distributions.

These are the honest algorithms' output distributions. The file follows ZKCP/SameRun.lean, for
families of oracles, two relations and batches. (The counterpart of that file's relation is
`SameRunAll` below; `SameRun` here is weaker: see P.)

The relation. A = (C, P, V) and A' = (C', P', V') are two schemes of ZKCP/Gen.lean over the same
family of oracles, with the same types but for the prover's key: A' may keep more in it (a cache
beside the key), and a map φ : ISK' → ISK says which key of A a key of A' represents.
`A.SameRunVia φ A'` says, for every family g of oracle functions and every input:

    C: the output distribution of C(i) is that of C'(i) with φ applied to the prover's key;
    P: on every key that C'(i) can return under the same g (for some index i), P' has on every batch
        the output distribution of P on the key's image under φ;
    V: V and V' have the same output distribution.

How many queries the algorithms make, and which, is not compared. On a key that C' cannot return
under g, nothing is asked of P'. `A.SameRun A'` is the case φ = id. `A.SameRunAll A'`: the same
output distributions on all inputs, keys that no committer returns included.

What is proved. For A and A' in the relation, every property below holds for A if and only if it
holds for A', with the same pair of relations, the same B, the same extractor, the same simulator
and the same bounds: completeness and refined completeness, index binding, index privacy, the
primitive, completeness against an adaptive environment (ZKCP/GenAdaptive.lean).

Why. In each of these experiments the honest algorithms enter by `bind` only: they are run and their
outputs are passed on; no trace of theirs is taken; and the prover's key goes from C to P and to no
one else. So for every g the two experiments have the same output distribution (for refined
completeness: after φ, with the events matched by `mem_badKeys_iff`), and a probability `Rom.Pr`
depends on nothing else.

The exception. The statement that the extracted index is the committed one (ZKCP/GenOptional.lean:
`HasExtractionError`) gives the extractor the trace of the honest committer, of which the relation
says nothing. `hasExtractionError_iff_of` names a condition that suffices: for every g, what the
extractor reads off key and trace has the same distribution.

Notation: B: a natural number; the bound on the length of a batch (`Arg`, `ValidBatch`,
ZKCP/Gen.lean).

Limits: the relation does not carry properties of the algorithms as programs, such as a bound on the
queries of an honest algorithm (counterexamples for one oracle: ZKCP/SameRun.lean, last section).
The file has no statement on a construction: nothing here says that two given schemes are in the
relation.
-/
import ZKCP.Gen
import ZKCP.GenAdaptive
import ZKCP.GenOptional

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)

variable {S : OSpec} {I X W PP IVK ISK ISK' ISK'' Pf : Type}

/-- Two schemes whose algorithms have the same output distributions, for every family of oracle
functions; φ reads a prover's key of A' as one of A. Of P' something is asked only on keys that C'
can return under the same family. Nothing is said of queries. -/
structure Arg.SameRunVia (φ : ISK' → ISK)
    (A : Arg S I X W IVK ISK Pf) (A' : Arg S I X W IVK ISK' Pf) : Prop where
  C : ∀ i g, (A.C i).runEager g = ((A'.C i).runEager g).map (Prod.map id φ)
  P : ∀ i g key, key ∈ ((A'.C i).runEager g).support →
    ∀ b, (A'.P key.2 b).runEager g = (A.P (φ key.2) b).runEager g
  V : ∀ ivk x π g, (A.V ivk x π).runEager g = (A'.V ivk x π).runEager g

/-- The case of one type of keys and φ = id. -/
def Arg.SameRun (A A' : Arg S I X W IVK ISK Pf) : Prop := A.SameRunVia id A'

/-! ## General facts -/

/-- A probability of the form `Rom.Pr` depends on the computation through its output distributions
only. -/
theorem Pr_congr {α : Type} {c c' : Rom.OComp S α}
    (h : ∀ g, c.runEager g = c'.runEager g) (E : Fam S → Set α) : Rom.Pr c E = Rom.Pr c' E := by
  unfold Rom.Pr Rom.PrCoins
  simp only [h]

private theorem runEager_bind {α β : Type} (g : Fam S) (c : Rom.OComp S α) (k : α → Rom.OComp S β) :
    (c.bind k).runEager g = (c.runEager g).bind fun a => (k a).runEager g := by
  induction c with
  | pure a => simp [Rom.OComp.bind, Rom.OComp.runEager]
  | query o q f ih => simp only [Rom.OComp.bind, Rom.OComp.runEager, ih]
  | sample n f ih => simp only [Rom.OComp.bind, Rom.OComp.runEager, ih, PMF.bind_bind]

private theorem pmf_bind_congr
    {α β : Type} (p : PMF α) {f f' : α → PMF β} (h : ∀ a ∈ p.support, f a = f' a) :
    p.bind f = p.bind f' := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((p.mem_support_iff a).2 ha)]

/-- Two computations in a row: if both steps have the same output distributions under g, so has the
whole. -/
theorem runEager_bind_congr {α β : Type} {c c' : Rom.OComp S α} {k k' : α → Rom.OComp S β}
    (g : Fam S) (hc : c.runEager g = c'.runEager g)
    (hk : ∀ a, (k a).runEager g = (k' a).runEager g) :
    (c.bind k).runEager g = (c'.bind k').runEager g := by
  rw [runEager_bind, runEager_bind, hc]
  simp only [hk]

namespace Arg.SameRunVia
variable {φ : ISK' → ISK} {A : Arg S I X W IVK ISK Pf}
  {A' : Arg S I X W IVK ISK' Pf} (h : A.SameRunVia φ A')
include h

/-- The relation composes, with the composed map φ ∘ ψ. -/
theorem trans {ψ : ISK'' → ISK'} {A'' : Arg S I X W IVK ISK'' Pf} (h' : A'.SameRunVia ψ A'') :
    A.SameRunVia (φ ∘ ψ) A'' where
  C i g := by
    rw [h.C i g, h'.C i g, PMF.map_comp]
    rfl
  P i g key hkey b := by
    have h2 : (key.1, ψ key.2) ∈ ((A'.C i).runEager g).support := by
      rw [h'.C i g, PMF.support_map]
      exact ⟨key, hkey, rfl⟩
    rw [h'.P i g key hkey b]
    exact h.P i g _ h2 b
  V ivk x π g := (h.V ivk x π g).trans (h'.V ivk x π g)

/-! ## The experiments -/

/-- For A and A' in the relation: the committer, followed by anything; it suffices to compare what
follows on the keys that C' can return. -/
theorem C_bind {β : Type} (i : I) (g : Fam S)
    {K : IVK × ISK → Rom.OComp S β} {K' : IVK × ISK' → Rom.OComp S β}
    (hK : ∀ key ∈ ((A'.C i).runEager g).support,
      (K (key.1, φ key.2)).runEager g = (K' key).runEager g) :
    ((A.C i).bind K).runEager g = ((A'.C i).bind K').runEager g := by
  rw [runEager_bind, runEager_bind, h.C i g, PMF.bind_map]
  exact pmf_bind_congr _ hK

theorem verifyAll_run (ivk : IVK) (g : Fam S) :
    ∀ l : List (X × Pf), (verifyAll A ivk l).runEager g = (verifyAll A' ivk l).runEager g
  | [] => rfl
  | (x, π) :: rest =>
    runEager_bind_congr g (h.V ivk x π g) fun _ =>
      runEager_bind_congr g (verifyAll_run ivk g rest) fun _ => rfl

theorem verifyBits_run (ivk : IVK) (g : Fam S) :
    ∀ l : List (X × Pf), (verifyBits A ivk l).runEager g = (verifyBits A' ivk l).runEager g
  | [] => rfl
  | (x, π) :: rest =>
    runEager_bind_congr g (h.V ivk x π g) fun _ =>
      runEager_bind_congr g (verifyBits_run ivk g rest) fun _ => rfl

/-- For A and A' in the relation, one honest batch has the same output distribution on a key on
which the two provers agree. -/
theorem sessionExp_run (ivk : IVK) (k : ISK') (g : Fam S)
    (hk : ∀ b, (A'.P k b).runEager g = (A.P (φ k) b).runEager g) (b : List (X × W)) :
    (sessionExp A ivk (φ k) b).runEager g = (sessionExp A' ivk k b).runEager g :=
  runEager_bind_congr g (hk b).symm fun _ => h.verifyAll_run ivk g _

theorem completenessExp_run (i : I) (b : List (X × W)) (g : Fam S) :
    (completenessExp A i b).runEager g = (completenessExp A' i b).runEager g :=
  h.C_bind i g fun key hkey => h.sessionExp_run key.1 key.2 g (h.P i g key hkey) b

theorem bindingExp_run {St : Type} (E : Extractor S I X W IVK Pf) (Ct : Rom.OComp S (IVK × St))
    (Pt : St → Rom.OComp S (X × Pf)) (g : Fam S) :
    (bindingExp A E Ct Pt).runEager g = (bindingExp A' E Ct Pt).runEager g :=
  runEager_bind_congr g rfl fun _ =>
    runEager_bind_congr g rfl fun _ => runEager_bind_congr g (h.V _ _ _ g) fun _ => rfl

omit h in
theorem realLoop_run (Z : ViewEnv S IVK X W Pf) (k : ISK') (g : Fam S)
    (hk : ∀ b, (A'.P k b).runEager g = (A.P (φ k) b).runEager g) :
    ∀ (Vt : AdvVerifier S X Pf) (n : ℕ) (v : View S IVK X Pf),
      (realLoop A Z (φ k) Vt n v).runEager g = (realLoop A' Z k Vt n v).runEager g
  | .halt, _, _ => rfl
  | .query o q f, n, v => by
      simp only [realLoop, Rom.OComp.runEager]
      exact realLoop_run Z k g hk (f (g o q)) n _
  | .sample m f, n, v => by
      simp only [realLoop, Rom.OComp.runEager]
      exact congrArg _ (funext fun r => realLoop_run Z k g hk (f r) n _)
  | .request _, 0, _ => rfl
  | .request f, n + 1, v => by
      simp only [realLoop]
      cases Z v with
      | none => rfl
      | some b =>
        exact runEager_bind_congr g (hk b.pairs).symm fun πs =>
          realLoop_run Z k g hk (f (b.released πs.val)) n _

theorem realExp_run (Vt : IVK → AdvVerifier S X Pf) (Z : ViewEnv S IVK X W Pf)
    (i : I) (N : ℕ) (g : Fam S) :
    (realExp A Vt Z i N).runEager g = (realExp A' Vt Z i N).runEager g :=
  h.C_bind i g fun key hkey => realLoop_run Z key.2 g (h.P i g key hkey) (Vt key.1) N _

theorem adaptiveLoop_run (ivk : IVK) (k : ISK') (g : Fam S)
    (hk : ∀ b, (A'.P k b).runEager g = (A.P (φ k) b).runEager g) :
    ∀ (E : BEnv S X W Pf) (n : ℕ),
      (adaptiveLoop A ivk (φ k) E n).runEager g = (adaptiveLoop A' ivk k E n).runEager g
  | .halt, _ => rfl
  | .query o q f, n => by
      simp only [adaptiveLoop, Rom.OComp.runEager]
      exact adaptiveLoop_run ivk k g hk (f (g o q)) n
  | .sample m f, n => by
      simp only [adaptiveLoop, Rom.OComp.runEager]
      exact congrArg _ (funext fun r => adaptiveLoop_run ivk k g hk (f r) n)
  | .batch _ _, 0 => rfl
  | .batch b f, n + 1 => by
      simp only [adaptiveLoop]
      exact runEager_bind_congr g (hk b).symm fun πs =>
          runEager_bind_congr g (h.verifyBits_run ivk g _) fun bs =>
        runEager_bind_congr g (adaptiveLoop_run ivk k g hk (f πs.val bs) n) fun _ => rfl

theorem adaptiveExp_run (E : IVK → BEnv S X W Pf) (i : I) (N : ℕ) (g : Fam S) :
    (adaptiveExp A E i N).runEager g = (adaptiveExp A' E i N).runEager g :=
  h.C_bind i g fun key hkey => h.adaptiveLoop_run key.1 key.2 g (h.P i g key hkey) (E key.1) N

/-! ## The properties: the same relations, B, extractor, simulator and bounds on both sides -/

variable (R : RelPair I X W PP)

theorem hasCompletenessError_iff (B : ℕ) (α : ℝ≥0∞) :
    HasCompletenessError R A B α ↔ HasCompletenessError R A' B α := by
  unfold HasCompletenessError
  simp only [Pr_congr (h.completenessExp_run _ _)]

/-- For A and A' in the relation, a key that C' can return is bad for A' if and only if its image is
bad for A. -/
theorem mem_badKeys_iff (B : ℕ) (αP : ℝ≥0∞) (i : I) (g : Fam S) (key : IVK × ISK')
    (hkey : key ∈ ((A'.C i).runEager g).support) :
    Prod.map id φ key ∈ badKeys R A B αP i g ↔ key ∈ badKeys R A' B αP i g := by
  show (∃ b,
      ValidBatch R B i b ∧ Rom.PrCoins g (sessionExp A key.1 (φ key.2) b) {c | c = false} > αP) ↔
    ∃ b, ValidBatch R B i b ∧ Rom.PrCoins g (sessionExp A' key.1 key.2 b) {c | c = false} > αP
  unfold Rom.PrCoins
  simp only [h.sessionExp_run key.1 key.2 g (h.P i g key hkey)]

/-- For A and A' in the relation, the probability of a bad key is the same. -/
theorem Pr_badKeys (B : ℕ) (αP : ℝ≥0∞) (i : I) :
    Rom.Pr (A.C i) (fun g => badKeys R A B αP i g) =
      Rom.Pr (A'.C i) fun g => badKeys R A' B αP i g := by
  unfold Rom.Pr Rom.PrCoins
  refine MeasureTheory.lintegral_congr fun g => ?_
  rw [h.C i g, Prob.pr_map]
  exact Prob.pr_congr_support _ fun key hkey => h.mem_badKeys_iff R B αP i g key hkey

theorem hasRefinedCompletenessError_iff (B : ℕ) (αC αP : ℝ≥0∞) :
    HasRefinedCompletenessError R A B αC αP ↔ HasRefinedCompletenessError R A' B αC αP := by
  unfold HasRefinedCompletenessError
  simp only [h.Pr_badKeys R]

theorem hasIndexBindingWith_iff (E : Extractor S I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWith R A E ε ↔ HasIndexBindingWith R A' E ε := by
  unfold HasIndexBindingWith
  simp only [Pr_congr (h.bindingExp_run E _ _)]

theorem hasIndexBinding_iff (ε : ℕ → ℕ → ℝ≥0∞) : HasIndexBinding R A ε ↔ HasIndexBinding R A' ε :=
  exists_congr fun E => h.hasIndexBindingWith_iff R E ε

theorem privacyFor_iff (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (i : I) (Z : ViewEnv S IVK X W Pf) :
    PrivacyFor R A Sim ζ i Z ↔ PrivacyFor R A' Sim ζ i Z := by
  unfold PrivacyFor
  simp only [Pr_congr (h.realExp_run _ Z i _)]

theorem hasIndexPrivacyWith_iff (B : ℕ) (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) :
    HasIndexPrivacyWith R A B Sim ζ ↔ HasIndexPrivacyWith R A' B Sim ζ := by
  unfold HasIndexPrivacyWith
  simp only [h.privacyFor_iff R Sim ζ]

theorem hasIndexPrivacy_iff (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) :
    HasIndexPrivacy R A B ζ ↔ HasIndexPrivacy R A' B ζ :=
  exists_congr fun Sim => h.hasIndexPrivacyWith_iff R B Sim ζ

/-- For A and A' in the relation, the primitive with extractor and simulator named holds for A if
and only if it holds for A': same extractor, same simulator, same three bounds. -/
theorem isZKCPArgWith_iff (B : ℕ) (E : Extractor S I X W IVK Pf) (Sim : Simulator S PP IVK X Pf)
    (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    IsZKCPArgWith R A B E Sim α ε ζ ↔ IsZKCPArgWith R A' B E Sim α ε ζ :=
  ⟨fun a =>
      ⟨(h.hasCompletenessError_iff R B α).1 a.completeness,
        (h.hasIndexBindingWith_iff R E ε).1 a.indexBinding,
        (h.hasIndexPrivacyWith_iff R B Sim ζ).1 a.indexPrivacy⟩,
    fun a =>
      ⟨(h.hasCompletenessError_iff R B α).2 a.completeness,
        (h.hasIndexBindingWith_iff R E ε).2 a.indexBinding,
        (h.hasIndexPrivacyWith_iff R B Sim ζ).2 a.indexPrivacy⟩⟩

/-- For A and A' in the relation, the primitive (`IsZKCPArg`) holds for A if and only if it holds
for A', with the same bounds. -/
theorem isZKCPArg_iff (B : ℕ) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    IsZKCPArg R A B α ε ζ ↔ IsZKCPArg R A' B α ε ζ :=
  ⟨fun a =>
      ⟨(h.hasCompletenessError_iff R B α).1 a.completeness,
        (h.hasIndexBinding_iff R ε).1 a.indexBinding,
        (h.hasIndexPrivacy_iff R B ζ).1 a.indexPrivacy⟩,
    fun a =>
      ⟨(h.hasCompletenessError_iff R B α).2 a.completeness,
        (h.hasIndexBinding_iff R ε).2 a.indexBinding,
        (h.hasIndexPrivacy_iff R B ζ).2 a.indexPrivacy⟩⟩

/-- For A and A' in the relation, completeness against an adaptive environment holds for A if and
only if it holds for A'. -/
theorem hasAdaptiveCompletenessError_iff (B : ℕ) (α : ℕ → ℕ → ℝ≥0∞) :
    HasAdaptiveCompletenessError R A B α ↔ HasAdaptiveCompletenessError R A' B α := by
  unfold HasAdaptiveCompletenessError
  simp only [Pr_congr (h.adaptiveExp_run _ _ _)]

end Arg.SameRunVia

/-! ## One type of keys -/

namespace Arg.SameRun
variable {A A' A'' : Arg S I X W IVK ISK Pf}

/-- `SameRun` follows from three plain equalities of output distributions. -/
theorem of (hC : ∀ i g, (A.C i).runEager g = (A'.C i).runEager g)
    (hP : ∀ k b g, (A.P k b).runEager g = (A'.P k b).runEager g)
    (hV : ∀ ivk x π g, (A.V ivk x π).runEager g = (A'.V ivk x π).runEager g) : A.SameRun A' where
  C i g := by rw [Prod.map_id, PMF.map_id]; exact hC i g
  P _ g key _ b := (hP key.2 b g).symm
  V := hV

theorem refl (A : Arg S I X W IVK ISK Pf) : A.SameRun A :=
  of (fun _ _ => rfl) (fun _ _ _ => rfl) fun _ _ _ _ => rfl

end Arg.SameRun

/-- The same output distributions on all inputs: for every family of oracle functions, every index,
every prover's key (also one that no committer returns) with every batch, every verification key,
instance and proof.
Stronger than `SameRun`, which asks something of the provers only on keys that the committer can
return. -/
structure Arg.SameRunAll (A A' : Arg S I X W IVK ISK Pf) : Prop where
  C : ∀ i g, (A.C i).runEager g = (A'.C i).runEager g
  P : ∀ k b g, (A.P k b).runEager g = (A'.P k b).runEager g
  V : ∀ ivk x π g, (A.V ivk x π).runEager g = (A'.V ivk x π).runEager g

theorem Arg.SameRunAll.toSameRun {A A' : Arg S I X W IVK ISK Pf} (h : A.SameRunAll A') :
    A.SameRun A' :=
  Arg.SameRun.of h.C h.P h.V

namespace Arg.SameRun
variable {A A' A'' : Arg S I X W IVK ISK Pf}

/-- The clause on the committers, without the identity map. -/
theorem run_C (h : A.SameRun A') (i : I) (g : Fam S) :
    (A.C i).runEager g = (A'.C i).runEager g := by
  have e := Arg.SameRunVia.C h i g
  rwa [Prod.map_id, PMF.map_id] at e

theorem symm (h : A.SameRun A') : A'.SameRun A where
  C i g := by rw [Prod.map_id, PMF.map_id]; exact (h.run_C i g).symm
  P i g key hkey b := (Arg.SameRunVia.P h i g key (by rw [← h.run_C i g]; exact hkey) b).symm
  V ivk x π g := (Arg.SameRunVia.V h ivk x π g).symm

theorem trans (h : A.SameRun A') (h' : A'.SameRun A'') : A.SameRun A'' := Arg.SameRunVia.trans h h'

/-- For A and A' in `SameRun`: if the two provers agree on all keys, the sets of bad keys of refined
completeness are equal. -/
theorem badKeys_eq (h : A.SameRun A') (hP : ∀ k b g, (A.P k b).runEager g = (A'.P k b).runEager g)
    (R : RelPair I X W PP) (B : ℕ) (αP : ℝ≥0∞) (i : I) (g : Fam S) :
    badKeys R A B αP i g = badKeys R A' B αP i g := by
  ext key
  have e : ∀ b,
      (sessionExp A key.1 key.2 b).runEager g = (sessionExp A' key.1 key.2 b).runEager g := fun b =>
    Arg.SameRunVia.sessionExp_run h key.1 key.2 g (fun b => (hP key.2 b g).symm) b
  show (∃ b, ValidBatch R B i b ∧ Rom.PrCoins g (sessionExp A key.1 key.2 b) {c | c = false} > αP)
    ↔ ∃ b, ValidBatch R B i b ∧ Rom.PrCoins g (sessionExp A' key.1 key.2 b) {c | c = false} > αP
  unfold Rom.PrCoins
  simp only [e]

end Arg.SameRun

/-! ## The exception: a property that reads the trace of the honest committer -/

/-- The statement that the extracted index is the committed one runs the honest committer with its
trace. That two committers have the same outputs says nothing of their traces; that, for every
family of oracle functions, what the extractor reads off key and trace has the same distribution
suffices. -/
theorem hasExtractionError_iff_of {A : Arg S I X W IVK ISK Pf}
    {A' : Arg S I X W IVK ISK' Pf} (E : Extractor S I X W IVK Pf)
    (hE : ∀ i g, ((A.C i).withTrace.runEager g).map (fun o => E.Ei o.1.1 o.2) =
      ((A'.C i).withTrace.runEager g).map (fun o => E.Ei o.1.1 o.2)) (δ : ℝ≥0∞) :
    HasExtractionError A E δ ↔ HasExtractionError A' E δ := by
  have key : ∀ (K : Type) (p : PMF ((IVK × K) × Rom.Trace S)) (i : I),
      Prob.pr p {o | E.Ei o.1.1 o.2 ≠ some i} =
        Prob.pr (p.map fun o => E.Ei o.1.1 o.2) {j | j ≠ some i} := fun K p i =>
    (Prob.pr_map p (fun o => E.Ei o.1.1 o.2) {j | j ≠ some i}).symm
  unfold HasExtractionError Rom.Pr Rom.PrCoins
  simp only [key, hE]

end ZKCP.Gen
