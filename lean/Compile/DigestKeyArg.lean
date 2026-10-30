-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DigestKeyArg.lean: what the scheme `A.digestKey enc` (ZKCP/DigestKey.lean), in which the
verifier's key is the digest of A's, keeps of the properties of A, and at which price.

For every scheme A of ZKCP/Defs.lean and every coding `enc` of its verifier's keys (`IVK`). α, ε, ζ,
δ are A's bounds, with the extractor E and the simulator S. λ is the length of a digest. tC and tP
bound the queries to the hash function of the adversary's committer and prover, t those of the
adversary's verifier; N bounds the number of sessions.
  `HasCompletenessError.digestKey`         completeness: the same α
  `HasIndexBindingWith.digestKey`          index binding: ε tC tP + (tC + tP + 2)² / 2^λ
                                           (Compile/DigestKeyBinding.lean)
  `HasStrongIndexPrivacyWith.digestKey`    strong index privacy: ζ (t + 1) N
  `IsZKCPArgWith.digestKey`                these three together
  `HasExtractionError.digestKey`           the honest committer's index is the extracted one
                                           (`HasExtractionError`, ZKCP/Optional.lean):
                                           δ + (tC + 1)² / 2^λ; here tC bounds the queries of A's
                                           own committer at every index
Conditions on the coding. Strong index privacy: none. Index binding: `CodeIsOneToOne enc`. (A coding
that is defined nowhere has that property; then the verifier rejects everything, so index binding
says something only together with completeness.) Completeness: `A.KeysHaveCodes enc`. The three
together and extraction: both.
`HasExtractionError.digestKey` has one condition more, `E.IgnoresKeyQuery enc`. The query log of the
committer of `A.digestKey enc` is, for a key that has a code, the log of A's committer with one
entry more, the query at the key's code, and the extractor is given the whole log. The condition
says that such a last entry, for every log and every answer, does not change the index that E gives.
It holds if E reads only entries of a kind to which no query at a code belongs
(`Extractor.ignoresKeyQuery_of_filter`). It is a condition on E and `enc` together and has to be
shown for each scheme. The other theorems do not use it.

Limits.
* Opening a digest is not treated here. If somebody shows an index and random choices from which
  the committer computes a given digest: Compile/DigestKeyWithOpenings.lean.
* The bounds on completeness, on strong index privacy and on extraction are taken also over random
  choices that the committer draws itself.
* Index binding is about one proof.
* Not carried here: completeness for each key (`HasRefinedCompletenessError`), session-augmented
  index binding (many sessions: ZKCP/Optional.lean), and index privacy from `HasIndexPrivacy` alone
  (`HasIndexPrivacyWith`): the premise on privacy is the strong form.
* The hash function is a random oracle. No number here is a security level.
* A's verifier's key travels with every proof, so each proof is longer by that key.
-/
import Compile.DigestKeyBinding
import ZKCP.PrivacyWrap
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X X' W W' PP IVK ISK Pf : Type}

open DigestKey

/-! ## 1. Definitions -/

/-- The re-packing (`Wrap`, ZKCP/PrivacyWrap.lean) that turns a verifier's key into its digest and
puts the key in front of each proof. The three maps on instances and witnesses are parameters, so
that a change of the instances' type can go through the same use of `PrivacyFor.wrap`; this library
uses the identity for all three. -/
def Wrap.digestKey (enc : IVK → Option Str) (inst : X' → X) (wit : W' → W) (back : X → X') :
    Wrap lam IVK X W Pf (Digest lam) X' W' (IVK × Pf) where
  ask := enc
  key := fun _ answer => answer.getD fun _ => false
  proof := fun key proof => (key, proof)
  inst := inst
  wit := wit
  back := back

/-- The simulator for `Arg.digestKey`: S, which also answers the query at the code of the key that
it has made. That answer is the digest that it hands out; for a key without a code it hands out the
digest of zeros. It puts its key in front of each proof. -/
def Simulator.digestKey (S : Simulator lam PP IVK X Pf) (enc : IVK → Option Str) :
    Simulator lam PP (Digest lam) X (IVK × Pf) :=
  (Wrap.digestKey (W := Unit) (W' := Unit) enc id id id).sim S id

/-- The index that E gives at a key does not change if a query at that key's code is appended to the
query log, whatever the log and the answer are. -/
def Extractor.IgnoresKeyQuery (E : Extractor lam I X W IVK Pf) (enc : IVK → Option Str) : Prop :=
  ∀ key code answer log, enc key = some code → E.Ei key (log ++ [(code, answer)]) = E.Ei key log

/-- The condition holds for an extractor whose index is computed from those entries of the log that
pass a test `reads`, if no query at a code passes it. -/
theorem Extractor.ignoresKeyQuery_of_filter (E : Extractor lam I X W IVK Pf)
    {enc : IVK → Option Str} (reads : Str × Digest lam → Bool)
    (g : IVK → Trace lam → Option I) (hE : ∀ key log, E.Ei key log = g key (log.filter reads))
    (hno : ∀ key code answer, enc key = some code → reads (code, answer) = false) :
    E.IgnoresKeyQuery enc := by
  intro key code answer log hs
  have hf : ¬ reads (code, answer) = true := by
    rw [hno key code answer hs]
    exact Bool.false_ne_true
  rw [hE, hE, List.filter_append, List.filter_cons_of_neg hf, List.filter_nil, List.append_nil]

/-- What the query for a key's digest adds to a query log under the hash function f. -/
def digestLog (f : Oracle lam) (enc : IVK → Option Str) (key : IVK) : Trace lam :=
  ((enc key).map fun code => (code, f code)).toList

/-! ## 2. Under each hash function -/

theorem digestLog_of_some (f : Oracle lam) {enc : IVK → Option Str} {key : IVK} {code : Str}
    (h : enc key = some code) : digestLog f enc key = [(code, f code)] := by
  have e : digestLog f enc key = ((some code).map fun code => (code, f code)).toList := by
    unfold digestLog
    rw [h]
  exact e

theorem run_withTrace_keyDigest (f : Oracle lam) (enc : IVK → Option Str) (key : IVK) :
    (keyDigest enc key).withTrace.run f
      = PMF.pure (digestUnder f enc key, digestLog f enc key) := by
  unfold keyDigest digestUnder digestLog
  cases enc key with
  | none => rfl
  | some code => rfl

/-- The committer with its query log: A's committer with its log, then the query for the digest. -/
theorem run_withTrace_C_digestKey (A : Arg lam I X W IVK ISK Pf) (enc : IVK → Option Str)
    (f : Oracle lam) (i : I) : ((A.digestKey enc).C i).withTrace.run f
      = ((A.C i).withTrace.run f).map fun o =>
        ((digestUnder f enc o.1.1, o.1), o.2 ++ digestLog f enc o.1.1) := by
  show ((A.C i).bind fun keys =>
      (keyDigest enc keys.1).mapO fun digest => (digest, keys)).withTrace.run f = _
  rw [OComp.withTrace_bind, run_bind]
  show _ = ((A.C i).withTrace.run f).bind fun o =>
    PMF.pure ((digestUnder f enc o.1.1, o.1), o.2 ++ digestLog f enc o.1.1)
  refine congrArg _ (funext fun o => ?_)
  rw [OComp.withTrace_mapO, OComp.mapO_bind, run_bind, run_withTrace_keyDigest, PMF.pure_bind]
  rfl

/-- One honest session under the digest of a key that has a code is one honest session of A. -/
theorem run_sessionExp_digestKey (A : Arg lam I X W IVK ISK Pf) {enc : IVK → Option Str}
    (f : Oracle lam) (keys : IVK × ISK) (x : X) (w : W) (h : enc keys.1 ≠ none) :
    (sessionExp (A.digestKey enc) (digestUnder f enc keys.1) keys x w).run f
      = (sessionExp A keys.1 keys.2 x w).run f := by
  cases hs : enc keys.1 with
  | none => exact absurd hs h
  | some code =>
    show (((A.P keys.2 x w).mapO fun proof => (keys.1, proof)).bind fun proof =>
        verifyDigestKey A.V enc (digestUnder f enc keys.1) x proof).run f
      = ((A.P keys.2 x w).bind fun proof => A.V keys.1 x proof).run f
    rw [OComp.mapO_bind, run_bind, run_bind]
    refine congrArg _ (funext fun proof => ?_)
    rw [run_verifyDigestKey A.V f _ x (keys.1, proof) hs, digestUnder_of_some f hs, if_pos rfl]

/-! ## 3. Completeness -/

/-- Completeness passes to `A.digestKey enc` with the same bound, if every verifier's key that A's
committer can output has a code. -/
theorem HasCompletenessError.digestKey {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {α : ℝ≥0∞} (h : HasCompletenessError R A α)
    {enc : IVK → Option Str} (hcode : A.KeysHaveCodes enc) :
    HasCompletenessError R (A.digestKey enc) α := by
  intro i x w hr
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) (h i x w hr)
  show prob ((((A.digestKey enc).C i).bind fun keys =>
      sessionExp (A.digestKey enc) keys.1 keys.2 x w).run f) {b | b = false}
    ≤ prob (((A.C i).bind fun keys => sessionExp A keys.1 keys.2 x w).run f) {b | b = false}
  rw [run_bind, run_bind, run_C_digestKey, prob_bind, prob_bind, expect_map]
  refine expect_le_on_support _ fun keys hkeys => le_of_eq ?_
  show prob ((sessionExp (A.digestKey enc) (digestUnder f enc keys.1) keys x w).run f) _ = _
  rw [run_sessionExp_digestKey A f keys x w (hcode i f keys hkeys)]

/-! ## 4. Strong index privacy -/

/-- The step at one index i and one environment Z. If A has privacy at i and at the environment that
reads its view as a view of `A.digestKey enc` and then asks Z, then `A.digestKey enc` has it at i
and Z, with the simulator `S.digestKey enc` and the bound of A at one query more. -/
theorem PrivacyFor.digestKey {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} {i : I} (enc : IVK → Option Str)
    {Z : ViewEnv lam (Digest lam) X W (IVK × Pf)}
    (h : PrivacyFor R A S ζ i ((Wrap.digestKey enc id id id).env Z)) :
    PrivacyFor R (A.digestKey enc) (S.digestKey enc) (fun t N => ζ (t + 1) N) i Z :=
  PrivacyFor.wrap (Wrap.digestKey enc id id id) (R := R) (R' := R) (A := A)
    (B := A.digestKey enc) id rfl (fun f => (A.C i).run f) (fun _ keys => keys)
    (fun _ keys => keys) (fun _ => (PMF.map_id _).symm) (fun f => run_C_digestKey A enc f i)
    (fun f keys _ x w _ => run_P_digestKey A enc f keys x w) (fun _ _ _ _ => rfl) h

/-- Strong index privacy passes to `A.digestKey enc`, for every coding, with the simulator
`S.digestKey enc` and the bound of A at one query more. -/
theorem HasStrongIndexPrivacyWith.digestKey {R : IndexedRelation I X W PP}
    {A : Arg lam I X W IVK ISK Pf} {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : HasStrongIndexPrivacyWith R A S ζ) (enc : IVK → Option Str) :
    HasStrongIndexPrivacyWith R (A.digestKey enc) (S.digestKey enc) fun t N => ζ (t + 1) N := by
  intro i Z hZ
  refine PrivacyFor.digestKey enc (h i _ fun v x w hv => ?_)
  obtain ⟨xw, hz, e⟩ := Option.map_eq_some_iff.1 hv
  have e' : (xw.1, xw.2) = (x, w) := e
  cases e'
  exact hZ _ xw.1 xw.2 hz

/-! ## 5. The three properties together -/

/-- `A.digestKey enc` is an argument of the same kind as A, with the extractor and the simulator
named, if the coding is one to one and the keys of A's committer have codes: α is kept, ε grows by
(tC + tP + 2)² / 2^λ, ζ is taken at t + 1. -/
theorem IsZKCPArgWith.digestKey {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}
    {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf} {α : ℝ≥0∞}
    {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A E S α ε ζ) {enc : IVK → Option Str}
    (hinj : CodeIsOneToOne enc) (hcode : A.KeysHaveCodes enc) :
    IsZKCPArgWith R (A.digestKey enc) (E.digestKey enc) (S.digestKey enc) α
      (fun tC tP => ε tC tP + (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam)
      (fun t N => ζ (t + 1) N) where
  completeness := h.completeness.digestKey hcode
  indexBinding := h.indexBinding.digestKey hinj
  indexPrivacy := h.indexPrivacy.digestKey enc

/-! ## 6. Extraction from an honest key -/

namespace DigestKey

/-- On what a distribution can output, an event that lies in the union of two others has at most the
sum of their probabilities. -/
theorem prob_le_add_of_support {α : Type} (p : PMF α) (S T U : Set α)
    (h : ∀ a ∈ p.support, a ∈ S → a ∈ T ∨ a ∈ U) : prob p S ≤ prob p T + prob p U := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  refine expect_le_on_support _ fun a ha => ?_
  by_cases hS : a ∈ S
  · rcases h a ha hS with hT | hU
    · rw [if_pos hS, if_pos hT]
      exact le_self_add
    · rw [if_pos hS, if_pos hU]
      exact le_add_self
  · rw [if_neg hS]
    exact zero_le _

end DigestKey

/-- Extraction from an honest key passes to `A.digestKey enc` with the extractor `E.digestKey enc`
and the bound δ + (tC + 1)² / 2^λ, where tC bounds the queries of A's committer at every index. The
conditions: the coding is one to one, the keys of A's committer have codes, and
`E.IgnoresKeyQuery enc`. -/
theorem HasExtractionError.digestKey {A : Arg lam I X W IVK ISK Pf}
    {E : Extractor lam I X W IVK Pf} {δ : ℝ≥0∞} (h : HasExtractionError A E δ)
    {enc : IVK → Option Str} (hinj : CodeIsOneToOne enc) (hcode : A.KeysHaveCodes enc)
    (hE : E.IgnoresKeyQuery enc) {tC : ℕ} (hC : ∀ i, (A.C i).QueryBound tC) :
    HasExtractionError (A.digestKey enc) (E.digestKey enc)
      (δ + (((tC + 1) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam) := by
  intro i
  refine le_trans (Pr_le_add _ (A.C i).withTrace ((A.digestKey enc).C i).withTrace _
      {o | E.Ei o.1.1 o.2 ≠ some i} {o | AnswerRepeats o.2} fun f => ?_)
    (add_le_add (h i) (Pr_answerRepeats_le _ _ (queryBound_C_digestKey A enc i tC (hC i))))
  rw [run_withTrace_C_digestKey, prob_map, prob_map]
  refine prob_le_add_of_support _ _ _ _ fun o ho hbad => ?_
  by_contra hnot
  rw [not_or] at hnot
  obtain ⟨hA, hrep⟩ := hnot
  have hA' : E.Ei o.1.1 o.2 = some i := not_not.1 hA
  have hrep' : ¬ AnswerRepeats (o.2 ++ digestLog f enc o.1.1) := hrep
  have hbad' : (firstKey enc (digestUnder f enc o.1.1) (o.2 ++ digestLog f enc o.1.1)).bind
      (fun key => E.Ei key (o.2 ++ digestLog f enc o.1.1)) ≠ some i := hbad
  cases hs : enc o.1.1 with
  | none => exact hcode i f o.1 (mem_support_withTrace f _ o ho) hs
  | some code =>
    rw [digestLog_of_some f hs] at hrep' hbad'
    rw [digestUnder_of_some f hs] at hbad'
    have hfirst : firstKey enc (f code) (o.2 ++ [(code, f code)]) = some o.1.1 := by
      by_contra hne
      exact hrep' (answerRepeats_of_mem hinj hs (by simp) hne)
    rw [hfirst] at hbad'
    exact hbad' ((hE o.1.1 code (f code) o.2 hs).trans hA')

end ZKCP
