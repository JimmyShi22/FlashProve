-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/BuildInstance.lean: a scheme on instances of another type.

`Arg.buildInstance A build aux π₀` is made from the scheme A (ZKCP/Defs.lean), whose instances have
the type X. Its instances have another type X', and a proof has a first part of a type `Aux`. The
verifier computes an instance of A, `build x' a`, from the new instance x' and the first part a of
the proof, and runs A's verifier on it; where `build` gives none it rejects. The honest prover sends
`aux x'` as the first part; the second is A's prover's proof for the built instance, or `π₀` where
`build x' (aux x')` is none. The committer is A's.
The statements listed below are for relations without witnesses (ZKCP/LanguageRelation.lean). Let
  `sound`:    wherever `build x' a = some x` and x is true at an index (`IsTrue`), x' is true at
              that index (`IsTrue'`);
  `complete`: wherever x' can be served at an index (`CanServe`), `build x' (aux x')` is an instance
              that is true at that index.
Then the new scheme has what A has for `IsTrue`, with the same bounds:
  `HasIndexBindingWith.buildInstance`         index binding for `IsTrue'` (from `sound` and an
                                              instance `x₀` of A), same index extractor
  `HasCompletenessError.buildInstance`        completeness for `CanServe` (from `complete`)
  `HasStrongIndexPrivacyWith.buildInstance`   index privacy, with the simulator `S.buildInstance`
                                              (from A's in the stronger form, `complete`, and a
                                              function `back` that gives x' again from the built
                                              instance)
  `HasExtractionError.buildInstance`, `Arg.CommitsFromCoins.buildInstance`: the committer is A's
  `drawsNoCoin_buildInstance_V`, `queryBound_buildInstance_V`, `queryBound_buildInstance_P`
Limits. The prover chooses the first part of the proof: soundness holds for every choice,
completeness and privacy are about `aux x'` alone. Completeness says nothing on an instance that
cannot be served. Nor does privacy: its environments choose only instances that can be served, and
whether an instance can be served may depend on the index. Privacy is about the index alone. The
simulator is handed every instance, and a view holds the instances: nothing is said to hide them.
Words: a hash function is an `Oracle`, the query log is the `Trace` that `withTrace` returns.
-/
import ZKCP.LanguageRelation
import ZKCP.CommitsFromCoins
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X X' Aux W PP IVK ISK Pf : Type}

/-! ## 1. The scheme -/

/-- The scheme on instances of another type: the verifier builds A's instance from the new instance
and the first part of the proof, and rejects where none is built; the honest prover sends `aux x'`
as that part. Where `build x' (aux x')` is none the honest prover sends `π₀`, which the verifier
rejects. -/
def Arg.buildInstance (A : Arg lam I X W IVK ISK Pf) (build : X' → Aux → Option X)
    (aux : X' → Aux) (π₀ : Pf) : Arg lam I X' W IVK ISK (Aux × Pf) where
  C := A.C
  P := fun secret x' w => match build x' (aux x') with
    | some x => (A.P secret x w).mapO fun π => (aux x', π)
    | none => .pure (aux x', π₀)
  V := fun key x' proof => match build x' proof.1 with
    | some x => A.V key x proof.2
    | none => .pure false

/-- The extractor on the new types, for relations without witnesses: the index part of E. -/
def Extractor.buildInstance (E : Extractor lam I X Unit IVK Pf) :
    Extractor lam I X' Unit IVK (Aux × Pf) :=
  ⟨E.Ei, fun _ _ _ _ _ => ()⟩

/-- What a prover against the new scheme outputs, as the output of a prover against A: the built
instance, or `x₀` where none is built, and the second part of the proof. -/
def builtOutput (build : X' → Aux → Option X) (x₀ : X) (o : X' × (Aux × Pf)) : X × Pf :=
  ((build o.1 o.2.1).getD x₀, o.2.2)

section Scheme
variable (A : Arg lam I X W IVK ISK Pf) (build : X' → Aux → Option X) (aux : X' → Aux) (π₀ : Pf)

/-- The committer is A's. -/
theorem buildInstance_C : (A.buildInstance build aux π₀).C = A.C := rfl

/-- Where an instance is built the verifier is A's verifier on it. -/
theorem buildInstance_V_some {x' : X'} {proof : Aux × Pf} {x : X}
    (h : build x' proof.1 = some x) (key : IVK) :
    (A.buildInstance build aux π₀).V key x' proof = A.V key x proof.2 := by
  show (match build x' proof.1 with
    | some x => A.V key x proof.2
    | none => .pure false) = A.V key x proof.2
  cases hb : build x' proof.1 with
  | none => cases hb.symm.trans h
  | some y =>
    cases hb.symm.trans h
    rfl

/-- Where no instance is built the verifier rejects, without a query. -/
theorem buildInstance_V_none {x' : X'} {proof : Aux × Pf} (h : build x' proof.1 = none)
    (key : IVK) : (A.buildInstance build aux π₀).V key x' proof = .pure false := by
  show (match build x' proof.1 with
    | some x => A.V key x proof.2
    | none => .pure false) = .pure false
  cases hb : build x' proof.1 with
  | none => rfl
  | some y => cases hb.symm.trans h

/-- Where `build x' (aux x')` is an instance the honest prover is A's prover on it, with `aux x'`
put in front of the proof. -/
theorem buildInstance_P_some {x' : X'} {x : X} (h : build x' (aux x') = some x) (secret : ISK)
    (w : W) :
    (A.buildInstance build aux π₀).P secret x' w = (A.P secret x w).mapO fun π => (aux x', π) := by
  show (match build x' (aux x') with
    | some x => (A.P secret x w).mapO fun π => (aux x', π)
    | none => .pure (aux x', π₀)) = (A.P secret x w).mapO fun π => (aux x', π)
  cases hb : build x' (aux x') with
  | none => cases hb.symm.trans h
  | some y =>
    cases hb.symm.trans h
    rfl

/-- The verifier samples nothing if A's verifier samples nothing. -/
theorem drawsNoCoin_buildInstance_V (h : ∀ key x π, (A.V key x π).DrawsNoCoin) (key : IVK)
    (x' : X') (proof : Aux × Pf) : ((A.buildInstance build aux π₀).V key x' proof).DrawsNoCoin := by
  show (match build x' proof.1 with
    | some x => A.V key x proof.2
    | none => .pure false : OComp lam Bool).DrawsNoCoin
  cases build x' proof.1 with
  | none => trivial
  | some x => exact h key x proof.2

/-- A bound on the queries of A's verifier holds for the verifier. -/
theorem queryBound_buildInstance_V {n : ℕ} (h : ∀ key x π, (A.V key x π).QueryBound n) (key : IVK)
    (x' : X') (proof : Aux × Pf) :
    ((A.buildInstance build aux π₀).V key x' proof).QueryBound n := by
  show (match build x' proof.1 with
    | some x => A.V key x proof.2
    | none => .pure false : OComp lam Bool).QueryBound n
  cases build x' proof.1 with
  | none => trivial
  | some x => exact h key x proof.2

/-- A bound on the queries of A's prover at all instances holds for the honest prover. -/
theorem queryBound_buildInstance_P {n : ℕ} {secret : ISK} {w : W}
    (h : ∀ x, (A.P secret x w).QueryBound n) (x' : X') :
    ((A.buildInstance build aux π₀).P secret x' w).QueryBound n := by
  show (match build x' (aux x') with
    | some x => (A.P secret x w).mapO fun π => (aux x', π)
    | none => .pure (aux x', π₀) : OComp lam (Aux × Pf)).QueryBound n
  cases build x' (aux x') with
  | none => trivial
  | some x => exact OComp.QueryBound.mapO _ _ n (h x)

/-- One run of the verifier, under a fixed hash function, against one run of A's verifier on the
built instance, or on `x₀` where none is built. `g'` makes the outcome of one experiment from the
verifier's bit, `g` that of the other from the instance and the bit. If a rejection is not in the
event E', and an outcome in E' gives, where an instance is built, an outcome in E, then E' is at
most as probable as E. -/
theorem prob_V_buildInstance_le (f : Oracle lam) (key : IVK) (x' : X') (proof : Aux × Pf) (x₀ : X)
    {β β' : Type} (g' : Bool → β') (g : X → Bool → β) (E' : Set β') (E : Set β)
    (hfalse : g' false ∉ E')
    (himp : ∀ x, build x' proof.1 = some x → ∀ b, g' b ∈ E' → g x b ∈ E) :
    prob ((((A.buildInstance build aux π₀).V key x' proof).bind fun b => .pure (g' b)).run f) E'
      ≤ prob (((A.V key ((build x' proof.1).getD x₀) proof.2).bind fun b =>
          .pure (g ((build x' proof.1).getD x₀) b)).run f) E := by
  cases hb : build x' proof.1 with
  | none =>
    rw [buildInstance_V_none A build aux π₀ hb]
    refine le_trans (le_of_eq ?_) (zero_le _)
    show prob (PMF.pure (g' false)) E' = 0
    rw [prob_pure, if_neg hfalse]
  | some x =>
    rw [buildInstance_V_some A build aux π₀ hb]
    show prob (((A.V key x proof.2).bind fun b => .pure (g' b)).run f) E'
      ≤ prob (((A.V key x proof.2).bind fun b => .pure (g x b)).run f) E
    rw [run_bind, run_bind, prob_bind, prob_bind]
    refine expect_mono _ fun b => ?_
    show prob (PMF.pure (g' b)) E' ≤ prob (PMF.pure (g x b)) E
    rw [prob_pure, prob_pure]
    by_cases h : g' b ∈ E'
    · rw [if_pos h, if_pos (himp x hb b h)]
    · rw [if_neg h]
      exact zero_le _

end Scheme

/-! ## 2. Index binding -/

section Sound
variable {build : X' → Aux → Option X} {aux : X' → Aux} {π₀ : Pf} {IsTrue : I → X → Prop}
  {IsTrue' : I → X' → Prop}

/-- Under `sound`, the bad event of index binding at the new instance gives the bad event at the
built instance. -/
theorem bindingBad_buildInstance
    (sound : ∀ i x' a x, build x' a = some x → IsTrue i x → IsTrue' i x') {x' : X'} {a : Aux}
    {x : X} (hx : build x' a = some x) (b : Bool) (s : Option I)
    (h : (⟨b, s, x', ()⟩ : BindingOutcome I X' Unit) ∈ bindingBad (languageRelation IsTrue')) :
    (⟨b, s, x, ()⟩ : BindingOutcome I X Unit) ∈ bindingBad (languageRelation IsTrue) := by
  rw [bindingBad_languageRelation] at h ⊢
  exact ⟨h.1, fun ⟨i, e, ht⟩ => h.2 ⟨i, e, sound i x' a x hx ht⟩⟩

/-- Index binding from A's, under `sound`, with the same bound and the index part of the same
extractor. A cheating prover against the new scheme is one against A that outputs the built
instance, or `x₀` where none is built; there the new verifier rejects. -/
theorem HasIndexBindingWith.buildInstance {A : Arg lam I X Unit IVK ISK Pf}
    {E : Extractor lam I X Unit IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (x₀ : X)
    (sound : ∀ i x' a x, build x' a = some x → IsTrue i x → IsTrue' i x')
    (h : HasIndexBindingWith (languageRelation IsTrue) A E ε) :
    HasIndexBindingWith (languageRelation IsTrue') (A.buildInstance build aux π₀)
      E.buildInstance ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct (fun st => (Pt st).mapO (builtOutput build x₀)) hC
    fun st => OComp.QueryBound.mapO _ _ tP (hP st))
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
      ((A.buildInstance build aux π₀).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
        .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1, ()⟩ : BindingOutcome I X' Unit)).run f)
      (bindingBad (languageRelation IsTrue'))
    ≤ prob ((Ct.withTrace.bind fun o =>
      ((Pt o.1.2).mapO (builtOutput build x₀)).withTrace.bind fun o' =>
        (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
          .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1, ()⟩ : BindingOutcome I X Unit)).run f)
      (bindingBad (languageRelation IsTrue))
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  rw [OComp.withTrace_mapO, OComp.mapO_bind, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o' => ?_
  exact prob_V_buildInstance_le A build aux π₀ f o.1.1 o'.1.1 o'.1.2 x₀
    (fun b => (⟨b, E.Ei o.1.1 o.2, o'.1.1, ()⟩ : BindingOutcome I X' Unit))
    (fun x b => (⟨b, E.Ei o.1.1 o.2, x, ()⟩ : BindingOutcome I X Unit))
    (bindingBad (languageRelation IsTrue')) (bindingBad (languageRelation IsTrue))
    (fun hb => Bool.false_ne_true hb.1) fun x hx b hb => bindingBad_buildInstance sound hx b _ hb

/-- What the extractor gives from the honest committer's key and query log is unchanged. So the
extraction error δ (`HasExtractionError`) carries over. -/
theorem HasExtractionError.buildInstance {A : Arg lam I X Unit IVK ISK Pf}
    {E : Extractor lam I X Unit IVK Pf} {δ : ℝ≥0∞} (h : HasExtractionError A E δ) :
    HasExtractionError (A.buildInstance build aux π₀) (E.buildInstance (X' := X') (Aux := Aux)) δ :=
  h

/-- The committer keeps its form. -/
theorem Arg.CommitsFromCoins.buildInstance {bound : ℕ}
    {A : Arg lam I X W IVK (I × Fin (bound + 1)) Pf} {commit : I → Fin (bound + 1) → OComp lam IVK}
    (hC : A.CommitsFromCoins commit) : (A.buildInstance build aux π₀).CommitsFromCoins commit :=
  ⟨hC.committer, hC.noCoin⟩

end Sound

/-! ## 3. Completeness -/

section Complete
variable (A : Arg lam I X W IVK ISK Pf) (build : X' → Aux → Option X) (aux : X' → Aux) (π₀ : Pf)

/-- Where `build x' (aux x')` is an instance, one honest session on x' is A's honest session on the
built instance. -/
theorem sessionExp_buildInstance {x' : X'} {x : X} (h : build x' (aux x') = some x) (ivk : IVK)
    (isk : ISK) (w : W) :
    sessionExp (A.buildInstance build aux π₀) ivk isk x' w = sessionExp A ivk isk x w := by
  show ((A.buildInstance build aux π₀).P isk x' w).bind
      (fun π => (A.buildInstance build aux π₀).V ivk x' π)
    = (A.P isk x w).bind fun π => A.V ivk x π
  rw [buildInstance_P_some A build aux π₀ h, OComp.mapO_bind]
  exact congrArg _ (funext fun π =>
    buildInstance_V_some A build aux π₀ (proof := (aux x', π)) h ivk)

/-- Where `build x' (aux x')` is an instance, the experiment of completeness on x' is A's on the
built instance. -/
theorem completenessExp_buildInstance {x' : X'} {x : X} (h : build x' (aux x') = some x) (i : I)
    (w : W) :
    completenessExp (A.buildInstance build aux π₀) i x' w = completenessExp A i x w := by
  show (A.C i).bind (fun key => sessionExp (A.buildInstance build aux π₀) key.1 key.2 x' w)
    = (A.C i).bind fun key => sessionExp A key.1 key.2 x w
  exact congrArg _ (funext fun key => sessionExp_buildInstance A build aux π₀ h key.1 key.2 w)

end Complete

/-- Completeness on the instances that can be served, from A's, under `complete`, with the same
error. -/
theorem HasCompletenessError.buildInstance {A : Arg lam I X Unit IVK ISK Pf}
    {build : X' → Aux → Option X} {aux : X' → Aux} {π₀ : Pf} {IsTrue : I → X → Prop}
    {CanServe : I → X' → Prop} {α : ℝ≥0∞}
    (complete : ∀ i x', CanServe i x' → ∃ x, build x' (aux x') = some x ∧ IsTrue i x)
    (h : HasCompletenessError (languageRelation IsTrue) A α) :
    HasCompletenessError (languageRelation CanServe) (A.buildInstance build aux π₀) α := by
  intro i x' u hr
  obtain ⟨x, hx, ht⟩ := complete i x' hr
  rw [completenessExp_buildInstance A build aux π₀ hx]
  exact h i x u ht

/-! ## 4. Index privacy

For an environment as in `hZ` below (and, in the ideal experiment, relations with the same `pp`),
both experiments of the new scheme are those of A, for a verifier and an environment that translate
instances and proofs, with the view translated at the end. A view holds instances, so the
translation needs a function `back` that gives the new instance again from the built one. -/

/-- The simulator: handed x', it runs A's simulator on `build x' (aux x')` and puts `aux x'` in
front of the proof; where none is built it returns `π₀`, as the honest prover does. Its state, its
start and its answers to queries are A's simulator's. -/
def Simulator.buildInstance (S : Simulator lam PP IVK X Pf)
    (build : X' → Aux → Option X) (aux : X' → Aux) (π₀ : Pf) :
    Simulator lam PP IVK X' (Aux × Pf) where
  St := S.St
  init := S.init
  answer := S.answer
  prove := fun s x' => match build x' (aux x') with
    | some x => (S.prove s x).map fun o => ((aux x', o.1), o.2)
    | none => PMF.pure ((aux x', π₀), s)

/-- A view of A's experiments as a view of the new scheme's. -/
def View.buildInstance (back : X → X') (aux : X' → Aux) (v : View lam IVK X Pf) :
    View lam IVK X' (Aux × Pf) :=
  ⟨v.ivk, v.sessions.map fun s => (back s.1, (aux (back s.1), s.2)), v.trace, v.coins⟩

/-- A verifier against the new scheme as a verifier against A. -/
def AdvVerifier.buildInstance (back : X → X') (aux : X' → Aux) :
    AdvVerifier lam X' (Aux × Pf) → AdvVerifier lam X Pf
  | .halt => .halt
  | .query q k => .query q fun r => AdvVerifier.buildInstance back aux (k r)
  | .sample n k => .sample n fun r => AdvVerifier.buildInstance back aux (k r)
  | .request k => .request fun x π =>
      AdvVerifier.buildInstance back aux (k (back x) (aux (back x), π))

/-- An environment of the new scheme as an environment of A: it chooses the built instance. -/
def ViewEnv.buildInstance (Z : ViewEnv lam IVK X' W (Aux × Pf)) (build : X' → Aux → Option X)
    (back : X → X') (aux : X' → Aux) : ViewEnv lam IVK X W Pf :=
  fun v => (Z (v.buildInstance back aux)).bind fun xw =>
    (build xw.1 (aux xw.1)).map fun x => (x, xw.2)

section Privacy
variable {build : X' → Aux → Option X} {back : X → X'} {aux : X' → Aux} {π₀ : Pf}

/-- A bound on the verifier's queries holds for the translated verifier too. -/
theorem AdvVerifier.QueryBound.buildInstance (back : X → X') (aux : X' → Aux) :
    ∀ (a : AdvVerifier lam X' (Aux × Pf)) (n : ℕ), a.QueryBound n →
      (a.buildInstance back aux).QueryBound n
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, n + 1, h => fun r => AdvVerifier.QueryBound.buildInstance back aux (k r) n (h r)
  | .sample _ k, n, h => fun r => AdvVerifier.QueryBound.buildInstance back aux (k r) n (h r)
  | .request k, n, h => fun x π =>
      AdvVerifier.QueryBound.buildInstance back aux (k (back x) (aux (back x), π)) n
        (h (back x) (aux (back x), π))

/-- The translation of a view with one session more. -/
theorem View.buildInstance_sessions (back : X → X') (aux : X' → Aux) (v : View lam IVK X Pf)
    (x : X) (π : Pf) :
    View.buildInstance back aux { v with sessions := v.sessions ++ [(x, π)] }
      = { View.buildInstance back aux v with
          sessions := (View.buildInstance back aux v).sessions
            ++ [(back x, (aux (back x), π))] } := by
  simp [View.buildInstance]

/-- Where the environment declines, the translated one declines. -/
theorem ViewEnv.buildInstance_none (build : X' → Aux → Option X)
    {Z : ViewEnv lam IVK X' W (Aux × Pf)} {v : View lam IVK X Pf}
    (hz : Z (v.buildInstance back aux) = none) : Z.buildInstance build back aux v = none :=
  congrArg (fun o : Option (X' × W) => o.bind fun xw =>
    (build xw.1 (aux xw.1)).map fun x => (x, xw.2)) hz

/-- Where the environment chooses x', the translated one chooses the built instance. -/
theorem ViewEnv.buildInstance_some {Z : ViewEnv lam IVK X' W (Aux × Pf)} {v : View lam IVK X Pf}
    {x' : X'} {w : W} {x : X} (hz : Z (v.buildInstance back aux) = some (x', w))
    (hx : build x' (aux x') = some x) : Z.buildInstance build back aux v = some (x, w) :=
  (congrArg (fun o : Option (X' × W) => o.bind fun xw =>
    (build xw.1 (aux xw.1)).map fun x => (x, xw.2)) hz).trans
    (congrArg (fun o : Option X => o.map fun x => (x, w)) hx)

/-- The real experiment at a request for a session. -/
theorem realLoop_request (A : Arg lam I X W IVK ISK Pf) (Z : ViewEnv lam IVK X W Pf) (isk : ISK)
    (k : X → Pf → AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf) :
    realLoop A Z isk (.request k) (n + 1) v
      = (Z v).elim (.pure v) fun xw => (A.P isk xw.1 xw.2).bind fun π =>
        realLoop A Z isk (k xw.1 π) n { v with sessions := v.sessions ++ [(xw.1, π)] } := by
  simp only [realLoop]
  cases Z v with
  | none => rfl
  | some xw => rfl

/-- The ideal experiment at a request for a session. -/
theorem idealLoop_request (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam IVK X W Pf)
    (k : X → Pf → AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf) (s : S.St) :
    idealLoop S Z (.request k) (n + 1) v s
      = (Z v).elim (PMF.pure v) fun xw => (S.prove s xw.1).bind fun out =>
        idealLoop S Z (k xw.1 out.1) n { v with sessions := v.sessions ++ [(xw.1, out.1)] }
          out.2 := by
  simp only [idealLoop]
  cases Z v with
  | none => rfl
  | some xw => rfl

/-- Where `build x' (aux x')` is an instance the simulator makes A's simulated proof for it. -/
theorem Simulator.buildInstance_prove_some (S : Simulator lam PP IVK X Pf) (π₀ : Pf) {x' : X'}
    {x : X} (h : build x' (aux x') = some x) (s : S.St) :
    (S.buildInstance build aux π₀).prove s x'
      = (S.prove s x).map fun o => ((aux x', o.1), o.2) := by
  show (match build x' (aux x') with
    | some x => (S.prove s x).map fun o => ((aux x', o.1), o.2)
    | none => PMF.pure ((aux x', π₀), s)) = (S.prove s x).map fun o => ((aux x', o.1), o.2)
  cases hb : build x' (aux x') with
  | none => cases hb.symm.trans h
  | some y =>
    cases hb.symm.trans h
    rfl

/- From here to the end of the section Z is an environment such that from every instance x' that it
chooses, `build x' (aux x')` is an instance and `back` returns x' from it (`hZ`). -/
variable {Z : ViewEnv lam IVK X' W (Aux × Pf)}
  (hZ : ∀ v x' w, Z v = some (x', w) → ∃ x, build x' (aux x') = some x ∧ back x = x')
include hZ

/-- For Z as in `hZ`, the sessions of the real experiment are A's, with the view translated at the
end. -/
theorem realLoop_buildInstance (A : Arg lam I X W IVK ISK Pf) (π₀ : Pf) (isk : ISK) :
    ∀ (a : AdvVerifier lam X' (Aux × Pf)) (n : ℕ) (v : View lam IVK X Pf),
      realLoop (A.buildInstance build aux π₀) Z isk a n (v.buildInstance back aux)
        = (realLoop A (Z.buildInstance build back aux) isk (a.buildInstance back aux) n v).mapO
          (View.buildInstance back aux)
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      show OComp.query q (fun r => realLoop (A.buildInstance build aux π₀) Z isk (k r) n
          (View.buildInstance back aux { v with trace := v.trace ++ [(q, r)] }))
        = OComp.query q fun r => (realLoop A (Z.buildInstance build back aux) isk
          ((k r).buildInstance back aux) n { v with trace := v.trace ++ [(q, r)] }).mapO
            (View.buildInstance back aux)
      exact congrArg _ (funext fun r => realLoop_buildInstance A π₀ isk (k r) n _)
  | .sample m k, n, v => by
      show OComp.sample m (fun r => realLoop (A.buildInstance build aux π₀) Z isk (k r) n
          (View.buildInstance back aux { v with coins := v.coins ++ [r.val] }))
        = OComp.sample m fun r => (realLoop A (Z.buildInstance build back aux) isk
          ((k r).buildInstance back aux) n { v with coins := v.coins ++ [r.val] }).mapO
            (View.buildInstance back aux)
      exact congrArg _ (funext fun r => realLoop_buildInstance A π₀ isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      have eR : (AdvVerifier.request k).buildInstance back aux
          = (.request fun x π => (k (back x) (aux (back x), π)).buildInstance back aux :
            AdvVerifier lam X Pf) := rfl
      rw [eR, realLoop_request, realLoop_request]
      cases hz : Z (v.buildInstance back aux) with
      | none =>
          rw [ViewEnv.buildInstance_none build hz]
          rfl
      | some xw =>
          obtain ⟨x', w⟩ := xw
          obtain ⟨x, hx, rfl⟩ := hZ _ x' w hz
          rw [ViewEnv.buildInstance_some hz hx]
          show ((A.buildInstance build aux π₀).P isk (back x) w).bind (fun π' =>
              realLoop (A.buildInstance build aux π₀) Z isk (k (back x) π') n
                { View.buildInstance back aux v with
                  sessions := (View.buildInstance back aux v).sessions ++ [(back x, π')] })
            = ((A.P isk x w).bind fun π => realLoop A (Z.buildInstance build back aux) isk
              ((k (back x) (aux (back x), π)).buildInstance back aux) n
                { v with sessions := v.sessions ++ [(x, π)] }).mapO (View.buildInstance back aux)
          rw [buildInstance_P_some A build aux π₀ hx, OComp.mapO_bind, OComp.bind_mapO]
          refine congrArg _ (funext fun π => ?_)
          show realLoop (A.buildInstance build aux π₀) Z isk (k (back x) (aux (back x), π)) n
              { View.buildInstance back aux v with
                sessions := (View.buildInstance back aux v).sessions
                  ++ [(back x, (aux (back x), π))] } = _
          rw [← View.buildInstance_sessions back aux v x π]
          exact realLoop_buildInstance A π₀ isk (k (back x) (aux (back x), π)) n _

/-- For Z as in `hZ`, the real experiment is A's, with the view translated at the end. -/
theorem realExp_buildInstance (A : Arg lam I X W IVK ISK Pf) (π₀ : Pf)
    (Vt : IVK → AdvVerifier lam X' (Aux × Pf)) (i : I) (N : ℕ) :
    realExp (A.buildInstance build aux π₀) Vt Z i N
      = (realExp A (fun ivk => (Vt ivk).buildInstance back aux) (Z.buildInstance build back aux)
        i N).mapO (View.buildInstance back aux) := by
  show (A.C i).bind (fun key => realLoop (A.buildInstance build aux π₀) Z key.2 (Vt key.1) N
      ⟨key.1, [], [], []⟩)
    = ((A.C i).bind fun key => realLoop A (Z.buildInstance build back aux) key.2
      ((Vt key.1).buildInstance back aux) N ⟨key.1, [], [], []⟩).mapO (View.buildInstance back aux)
  rw [OComp.bind_mapO]
  exact congrArg _ (funext fun key =>
    realLoop_buildInstance hZ A π₀ key.2 (Vt key.1) N ⟨key.1, [], [], []⟩)

/-- For Z as in `hZ`, the sessions of the ideal experiment are `S`'s, with the view translated at
the end. -/
theorem idealLoop_buildInstance (S : Simulator lam PP IVK X Pf) (π₀ : Pf) :
    ∀ (a : AdvVerifier lam X' (Aux × Pf)) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop (S.buildInstance build aux π₀) Z a n (v.buildInstance back aux) s
        = (idealLoop S (Z.buildInstance build back aux) (a.buildInstance back aux) n v s).map
          (View.buildInstance back aux)
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s => by
      simp only [idealLoop, AdvVerifier.buildInstance, PMF.map_bind]
      exact congrArg _ (funext fun out =>
        idealLoop_buildInstance S π₀ (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, AdvVerifier.buildInstance, PMF.map_bind]
      exact congrArg _ (funext fun r =>
        idealLoop_buildInstance S π₀ (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      have eR : (AdvVerifier.request k).buildInstance back aux
          = (.request fun x π => (k (back x) (aux (back x), π)).buildInstance back aux :
            AdvVerifier lam X Pf) := rfl
      rw [eR, idealLoop_request, idealLoop_request]
      cases hz : Z (v.buildInstance back aux) with
      | none =>
          rw [ViewEnv.buildInstance_none build hz]
          exact (PMF.pure_map _ _).symm
      | some xw =>
          obtain ⟨x', w⟩ := xw
          obtain ⟨x, hx, rfl⟩ := hZ _ x' w hz
          rw [ViewEnv.buildInstance_some hz hx]
          show ((S.buildInstance build aux π₀).prove s (back x)).bind (fun out =>
              idealLoop (S.buildInstance build aux π₀) Z (k (back x) out.1) n
                { View.buildInstance back aux v with
                  sessions := (View.buildInstance back aux v).sessions ++ [(back x, out.1)] }
                out.2)
            = ((S.prove s x).bind fun out => idealLoop S (Z.buildInstance build back aux)
              ((k (back x) (aux (back x), out.1)).buildInstance back aux) n
                { v with sessions := v.sessions ++ [(x, out.1)] } out.2).map
                  (View.buildInstance back aux)
          rw [Simulator.buildInstance_prove_some S π₀ hx]
          show ((S.prove s x).map fun o => ((aux (back x), o.1), o.2)).bind (fun out =>
              idealLoop (S.buildInstance build aux π₀) Z (k (back x) out.1) n
                { View.buildInstance back aux v with
                  sessions := (View.buildInstance back aux v).sessions ++ [(back x, out.1)] }
                out.2) = _
          rw [PMF.bind_map, PMF.map_bind]
          refine congrArg _ (funext fun out => ?_)
          show idealLoop (S.buildInstance build aux π₀) Z (k (back x) (aux (back x), out.1)) n
              { View.buildInstance back aux v with
                sessions := (View.buildInstance back aux v).sessions
                  ++ [(back x, (aux (back x), out.1))] } out.2 = _
          rw [← View.buildInstance_sessions back aux v x out.1]
          exact idealLoop_buildInstance S π₀ (k (back x) (aux (back x), out.1)) n _ out.2

/-- For Z as in `hZ`, the ideal experiment is `S`'s, with the view translated at the end, for two
relations with the same public parameters `pp` (`hpp`). -/
theorem idealExp_buildInstance (R : IndexedRelation I X W PP) (R' : IndexedRelation I X' W PP)
    (hpp : ∀ i, R'.pp i = R.pp i) (S : Simulator lam PP IVK X Pf) (π₀ : Pf)
    (Vt : IVK → AdvVerifier lam X' (Aux × Pf)) (i : I) (N : ℕ) :
    idealExp R' (S.buildInstance build aux π₀) Vt Z i N
      = (idealExp R S (fun ivk => (Vt ivk).buildInstance back aux)
        (Z.buildInstance build back aux) i N).map (View.buildInstance back aux) := by
  show (S.init (R'.pp i) N).bind (fun out =>
      idealLoop (S.buildInstance build aux π₀) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)
    = ((S.init (R.pp i) N).bind fun out => idealLoop S (Z.buildInstance build back aux)
      ((Vt out.1).buildInstance back aux) N ⟨out.1, [], [], []⟩ out.2).map
        (View.buildInstance back aux)
  rw [hpp i, PMF.map_bind]
  exact congrArg _ (funext fun out =>
    idealLoop_buildInstance hZ S π₀ (Vt out.1) N ⟨out.1, [], [], []⟩ out.2)

/-- For Z as in `hZ` and two relations with the same `pp` (`hpp`): index privacy at one index and
one environment, from A's privacy at the translated environment. The same bound, at the same number
of queries. -/
theorem PrivacyFor.buildInstance {R : IndexedRelation I X W PP} {R' : IndexedRelation I X' W PP}
    (hpp : ∀ i, R'.pp i = R.pp i) {A : Arg lam I X W IVK ISK Pf} {S : Simulator lam PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} {i : I} (h : PrivacyFor R A S ζ i (Z.buildInstance build back aux)) :
    PrivacyFor R' (A.buildInstance build aux π₀) (S.buildInstance build aux π₀) ζ i Z := by
  intro tV Vt N hV
  have b := h tV (fun ivk => (Vt ivk).buildInstance back aux) N
    fun ivk => AdvVerifier.QueryBound.buildInstance back aux (Vt ivk) tV (hV ivk)
  simp only [realExp_buildInstance hZ A π₀, idealExp_buildInstance hZ R R' hpp S π₀, Pr_mapO,
    prob_map]
  exact ⟨le_trans (SD_preimage_le (View.buildInstance back aux) _ _) b.1, b.2⟩

end Privacy

/-- Under `complete` and `h`: index privacy in the stronger form on the instances that can be
served, with the simulator `S.buildInstance` and the same bound. `back` gives the new instance again
from the instance that the honest prover builds. -/
theorem HasStrongIndexPrivacyWith.buildInstance {A : Arg lam I X Unit IVK ISK Pf}
    {build : X' → Aux → Option X} {aux : X' → Aux} {π₀ : Pf} {IsTrue : I → X → Prop}
    {CanServe : I → X' → Prop} {S : Simulator lam Unit IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}
    (back : X → X') (hback : ∀ x' x, build x' (aux x') = some x → back x = x')
    (complete : ∀ i x', CanServe i x' → ∃ x, build x' (aux x') = some x ∧ IsTrue i x)
    (h : HasStrongIndexPrivacyWith (languageRelation IsTrue) A S ζ) :
    HasStrongIndexPrivacyWith (languageRelation CanServe) (A.buildInstance build aux π₀)
      (S.buildInstance build aux π₀) ζ := by
  intro i Z hZ
  refine PrivacyFor.buildInstance (back := back) (fun v x' w e => ?_) (fun _ => rfl)
    (h i (Z.buildInstance build back aux) ?_)
  · obtain ⟨x, hx, -⟩ := complete i x' (hZ v x' w e)
    exact ⟨x, hx, hback x' x hx⟩
  · intro v x w e
    cases hz : Z (v.buildInstance back aux) with
    | none =>
      rw [ViewEnv.buildInstance_none build hz] at e
      cases e
    | some xw =>
      obtain ⟨x1, hx1, ht⟩ := complete i xw.1 (hZ _ xw.1 xw.2 hz)
      rw [ViewEnv.buildInstance_some (x' := xw.1) (w := xw.2) hz hx1] at e
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
      exact ht

end ZKCP
