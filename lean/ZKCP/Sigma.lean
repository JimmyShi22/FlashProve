-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Sigma.lean: a family of schemes over a public parameter t as one scheme whose key names t.

That scheme is "the combined scheme" below, the A t its members; its index is (t, i). For a type T
with decidable equality and, for every t : T, an indexed relation R t and a scheme A t = (C, P, V)
of ZKCP/Defs.lean, whose types of keys and proofs may depend on t (the types of indices, instances,
witnesses and public parameters, and λ, do not):
  `IndexedRelation.sigma R`  the index is (t, i); ((t, i), x, w) is in it iff (i, x, w) is in R t;
                             pp(t, i) = (t, pp(i))
  `Arg.sigma A`              keys and proofs are pairs ⟨t, a key or proof of A t⟩. C on (t, i) runs
                             A t's C on i and writes t into both keys; P reads t from isk and writes
                             it into the proof; V reads t from the key, rejects without a query a
                             proof that names another t, and else runs A t's V
  `Simulator.sigma S`        is initialised with (t, pp) and is S t from then on;
                             `Extractor.sigma E` reads t from the key: i* is (t, what E t finds), w
                             is what E t finds (a default witness for a proof that names another t)
  `HasCompletenessError.sigma`, `HasStrongIndexPrivacyWith.sigma`, `HasIndexPrivacyWith.sigma`,
      `HasIndexPrivacy.sigma`: from the family at every t, with one bound for all t, which is the
      bound of the combined scheme
  `IsZKCPArgWith.sigma`, `IsZKCPArg.sigma`: the primitive, from the family at every t and from index
      binding of the combined scheme, a hypothesis. (Of the family only completeness and privacy are
      used; its own binding is among the hypotheses with a free bound and is not used.)
  `Extractor.sigma_Ei_fst`   what `Extractor.sigma E` extracts names the t of the key
  `sigma_V_self`, `sigma_V_of_ne`, `QueryBound.sigma_V`
      on a key and a proof that name one t, V is A t's; for a proof that names another t than the
      key the computation is "false"; a bound on the queries of every A t's V is one for V
  `Arg.sigmaAt A t₀`, `HasIndexBindingWith.sigmaAt`
      binding at a t₀ that is fixed before the oracle, in the words of ZKCP/Defs.lean,
      `HasIndexBinding`.
      The definition: sigmaAt A t₀ is Arg.sigma A whose V also rejects every key that names another
      t than t₀ (sigmaAt_V_of_ne, sigmaAt_V_self).
      The theorem: if A t₀ has index binding for R t₀ with E t₀, sigmaAt A t₀ has index binding for
      IndexedRelation.sigma R with Extractor.sigma E and the bound of A t₀.
      In other words (read off sigmaAt's V; this sentence is not itself a theorem here, the outcome
      of `bindingExp` containing no key): for Arg.sigma A and Extractor.sigma E the
      chance of "V accepts, what is extracted is bad, and the key names t₀" is at most A t₀'s
      bound, for every t₀
  `IndexedRelation.sigmaU`, `Simulator.sigmaU`, `IsZKCPArgWith.sigmaU`,
  `HasStrongIndexPrivacyWith.sigmaU`, `HasIndexPrivacyWith.sigmaU`, `HasIndexBindingWith.sigmaAtU`
      where the members' public parameters are the one element of Unit: pp(t, i) = t
      (IndexedRelation.sigmaU_pp; ZKCP/MapPP.lean)
Why. A theorem "for every t, A t has the three properties" binds t outside the experiments. Here t
is where the definition has a place for it: it is a part of the index, it is (with pp(i); alone, in
the form sigmaU) the part of the index that may be revealed, and the extractor has to name a t. That
it is the t of the key is no part of `HasIndexBinding`: it is true of Extractor.sigma E
(Extractor.sigma_Ei_fst) and has to be shown for any other extractor; only with it does index
binding of the combined scheme say "what V accepts under a key that names t is true AT t".

Limits:
- Index binding of `Arg.sigma A` with the family's bound does not follow from the family's, and no
  index binding of `Arg.sigma A` is proved here: a committer may choose t after it has seen answers
  of the oracle. (Let A t's V accept iff f of the empty string is t, all relations empty: every
  member has error 2^-λ, and one query breaks the combined scheme. Not in Lean here.)
- For a finite T the sum of the members' bounds over all of T would follow from `sigmaAt`, a key
  naming one t; that is not stated here either.
- For an extractor of the combined scheme other than `Extractor.sigma E` nothing here says that it
  names the key's t.
- `sigmaAt A t₀` is a device for a statement: its V rejects every honest key of another t
  (`sigmaAt_V_of_ne`).
- t is in the key in the clear, and nothing here ties the rest of the key to it.
- The cast in V and in the extractor is along π.1 = vk.1 (the proof names the key's t), which V, and
  the extractor, has just decided.
- The other properties of this library (refined and adaptive completeness, many sessions) are not
  carried over here (calls in flight: neither stated nor proved in this library).

After `IsZKCPArg` and its three properties in ZKCP/Defs.lean; the step itself is not in
ZKCP/Defs.lean.
-/
import ZKCP.KeyTag
import ZKCP.MapPP
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {T I X W PP : Type} {IVK ISK Pf : T → Type}

/-! ## The definitions -/

/-- the index is (t, i); its public parameters are t and those of i -/
def IndexedRelation.sigma (R : T → IndexedRelation I X W PP) :
    IndexedRelation (T × I) X W (T × PP) where
  rel i x w := (R i.1).rel i.2 x w
  pp i := (i.1, (R i.1).pp i.2)

def View.inT (t : T) (v : View lam (IVK t) X (Pf t)) : View lam (Σ t, IVK t) X (Σ t, Pf t) :=
  ⟨⟨t, v.ivk⟩, v.sessions.map fun s => (s.1, ⟨t, s.2⟩), v.trace, v.coins⟩

def AdvVerifier.atT (t : T) : AdvVerifier lam X (Σ t, Pf t) → AdvVerifier lam X (Pf t)
  | .halt => .halt
  | .query q k => .query q fun r => (k r).atT t
  | .sample n k => .sample n fun r => (k r).atT t
  | .request k => .request fun x π => (k x ⟨t, π⟩).atT t

theorem AdvVerifier.QueryBound.atT (t : T) :
    ∀ (a : AdvVerifier lam X (Σ t, Pf t)) (n : ℕ), a.QueryBound n → (a.atT t).QueryBound n
  | .halt, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ k, n + 1, h => fun r => AdvVerifier.QueryBound.atT t (k r) n (h r)
  | .sample _ k, n, h => fun r => AdvVerifier.QueryBound.atT t (k r) n (h r)
  | .request k, n, h => fun x π => AdvVerifier.QueryBound.atT t (k x ⟨t, π⟩) n (h x ⟨t, π⟩)

def Simulator.sigma (S : ∀ t, Simulator lam PP (IVK t) X (Pf t)) :
    Simulator lam (T × PP) (Σ t, IVK t) X (Σ t, Pf t) where
  St := Σ t, (S t).St
  init p n := ((S p.1).init p.2 n).map fun o => (⟨p.1, o.1⟩, ⟨p.1, o.2⟩)
  answer s q := ((S s.1).answer s.2 q).map fun o => (o.1, ⟨s.1, o.2⟩)
  prove s x := ((S s.1).prove s.2 x).map fun o => (⟨s.1, o.1⟩, ⟨s.1, o.2⟩)

variable [DecidableEq T]

/-- C writes t into both keys; P writes it into the proof; V reads t from the key -/
def Arg.sigma (A : ∀ t, Arg lam I X W (IVK t) (ISK t) (Pf t)) :
    Arg lam (T × I) X W (Σ t, IVK t) (Σ t, ISK t) (Σ t, Pf t) where
  C i := ((A i.1).C i.2).mapO fun k => (⟨i.1, k.1⟩, ⟨i.1, k.2⟩)
  P sk x w := ((A sk.1).P sk.2 x w).mapO fun π => ⟨sk.1, π⟩
  V vk x π := if h : π.1 = vk.1 then (A vk.1).V vk.2 x (h ▸ π.2) else .pure false

variable (R : T → IndexedRelation I X W PP) (A : ∀ t, Arg lam I X W (IVK t) (ISK t) (Pf t))

/-- The extractor: it reads t from the key. -/
def Extractor.sigma [Inhabited W] (E : ∀ t, Extractor lam I X W (IVK t) (Pf t)) :
    Extractor lam (T × I) X W (Σ t, IVK t) (Σ t, Pf t) where
  Ei vk tr := ((E vk.1).Ei vk.2 tr).map fun i => (vk.1, i)
  Ew vk tr x π tr' := if h : π.1 = vk.1 then (E vk.1).Ew vk.2 tr x (h ▸ π.2) tr' else default

/-- what Extractor.sigma E extracts names the t of the key -/
theorem Extractor.sigma_Ei_fst [Inhabited W] (E : ∀ t, Extractor lam I X W (IVK t) (Pf t))
    (vk : Σ t, IVK t) (tr : Trace lam) (i : T × I) (h : (Extractor.sigma E).Ei vk tr = some i) :
    i.1 = vk.1 := by
  obtain ⟨j, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- the scheme whose V also rejects every key that names another t than t₀ -/
def Arg.sigmaAt (A : ∀ t, Arg lam I X W (IVK t) (ISK t) (Pf t)) (t₀ : T) :
    Arg lam (T × I) X W (Σ t, IVK t) (Σ t, ISK t) (Σ t, Pf t) where
  C := (Arg.sigma A).C
  P := (Arg.sigma A).P
  V vk x π := if vk.1 = t₀ then (Arg.sigma A).V vk x π else .pure false

/-! ## V -/

theorem sigma_V_self (t : T) (ivk : IVK t) (x : X) (π : Pf t) :
    (Arg.sigma A).V ⟨t, ivk⟩ x ⟨t, π⟩ = (A t).V ivk x π := dif_pos rfl

/-- V rejects every proof that names another t than the key: the computation is "false". -/
theorem sigma_V_of_ne {vk : Σ t, IVK t} {π : Σ t, Pf t} (h : π.1 ≠ vk.1) (x : X) :
    (Arg.sigma A).V vk x π = .pure false := dif_neg h

theorem QueryBound.sigma_V {N : ℕ} (h : ∀ t ivk x π, ((A t).V ivk x π).QueryBound N)
    (vk : Σ t, IVK t) (x : X) (π : Σ t, Pf t) :
    ((Arg.sigma A).V vk x π).QueryBound N := by
  show (if h : π.1 = vk.1 then (A vk.1).V vk.2 x (h ▸ π.2)
    else .pure false : OComp lam Bool).QueryBound N
  split
  · exact h _ _ _ _
  · trivial

theorem sigmaAt_V_self (t : T) (ivk : IVK t) (x : X) (π : Pf t) :
    (Arg.sigmaAt A t).V ⟨t, ivk⟩ x ⟨t, π⟩ = (A t).V ivk x π :=
  (if_pos rfl).trans (sigma_V_self A t ivk x π)

/-- sigmaAt's V rejects every key that names another t than t₀. -/
theorem sigmaAt_V_of_ne {t₀ : T} {vk : Σ t, IVK t} (h : vk.1 ≠ t₀) (x : X) (π : Σ t, Pf t) :
    (Arg.sigmaAt A t₀).V vk x π = .pure false := if_neg h

theorem sigmaAt_V_of_ne' {t₀ : T} {vk : Σ t, IVK t} {π : Σ t, Pf t} (h : π.1 ≠ vk.1) (x : X) :
    (Arg.sigmaAt A t₀).V vk x π = .pure false := by
  show (if vk.1 = t₀ then (Arg.sigma A).V vk x π else .pure false) = _
  rw [sigma_V_of_ne A h, ite_self]

/-! ## Completeness -/

theorem sigma_sessionExp (t : T) (ivk : IVK t) (isk : ISK t) (x : X) (w : W) :
    sessionExp (Arg.sigma A) ⟨t, ivk⟩ ⟨t, isk⟩ x w = sessionExp (A t) ivk isk x w := by
  show (((A t).P isk x w).mapO fun π => (⟨t, π⟩ : Σ t, Pf t)).bind
      (fun π => (Arg.sigma A).V ⟨t, ivk⟩ x π) =
    ((A t).P isk x w).bind fun π => (A t).V ivk x π
  rw [OComp.mapO_bind]
  simp only [sigma_V_self]

theorem sigma_completenessExp (t : T) (i : I) (x : X) (w : W) :
    completenessExp (Arg.sigma A) (t, i) x w = completenessExp (A t) i x w := by
  show (((A t).C i).mapO fun k => ((⟨t, k.1⟩ : Σ t, IVK t), (⟨t, k.2⟩ : Σ t, ISK t))).bind
      (fun key => sessionExp (Arg.sigma A) key.1 key.2 x w) =
    ((A t).C i).bind fun key => sessionExp (A t) key.1 key.2 x w
  rw [OComp.mapO_bind]
  simp only [sigma_sessionExp]

variable {R A}

theorem HasCompletenessError.sigma {α : ℝ≥0∞} (h : ∀ t, HasCompletenessError (R t) (A t) α) :
    HasCompletenessError (IndexedRelation.sigma R) (Arg.sigma A) α := fun i x w hr => by
  obtain ⟨t, i⟩ := i
  rw [sigma_completenessExp]
  exact h t i x w hr

/-! ## Index privacy -/

omit [DecidableEq T] in
theorem View.inT_sessions (t : T) (v : View lam (IVK t) X (Pf t)) (x : X) (π : Pf t) :
    ({ v.inT t with
       sessions := (v.inT t).sessions ++ [(x, ⟨t, π⟩)] } : View lam (Σ t, IVK t) X (Σ t, Pf t)) =
      View.inT t { v with sessions := v.sessions ++ [(x, π)] } := by
  simp [View.inT]

theorem sigma_realLoop (t : T) (Z : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)) (isk : ISK t) :
    ∀ (a : AdvVerifier lam X (Σ t, Pf t)) (n : ℕ) (v : View lam (IVK t) X (Pf t)),
      realLoop (Arg.sigma A) Z ⟨t, isk⟩ a n (v.inT t) =
        (realLoop (A t) (fun v => Z (v.inT t)) isk (a.atT t) n v).mapO (View.inT t)
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      show OComp.query q (fun r =>
          realLoop (Arg.sigma A) Z ⟨t, isk⟩ (k r) n
            (View.inT t { v with trace := v.trace ++ [(q, r)] })) =
        OComp.query q fun r =>
          (realLoop (A t) (fun v => Z (v.inT t)) isk ((k r).atT t) n
              { v with trace := v.trace ++ [(q, r)] }).mapO (View.inT t)
      exact congrArg _ (funext fun r => sigma_realLoop t Z isk (k r) n _)
  | .sample m k, n, v => by
      show OComp.sample m (fun r =>
          realLoop (Arg.sigma A) Z ⟨t, isk⟩ (k r) n
            (View.inT t { v with coins := v.coins ++ [r.val] })) =
        OComp.sample m fun r =>
          (realLoop (A t) (fun v => Z (v.inT t)) isk ((k r).atT t) n
              { v with coins := v.coins ++ [r.val] }).mapO (View.inT t)
      exact congrArg _ (funext fun r => sigma_realLoop t Z isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop, AdvVerifier.atT]
      cases Z (v.inT t) with
      | none => rfl
      | some xw =>
          show (((A t).P isk xw.1 xw.2).mapO fun π => (⟨t, π⟩ : Σ t, Pf t)).bind
              (fun π =>
                realLoop (Arg.sigma A) Z ⟨t, isk⟩ (k xw.1 π) n
                  { v.inT t with sessions := (v.inT t).sessions ++ [(xw.1, π)] }) =
            (((A t).P isk xw.1 xw.2).bind fun π =>
                realLoop (A t) (fun v => Z (v.inT t)) isk ((k xw.1 ⟨t, π⟩).atT t) n
                  { v with sessions := v.sessions ++ [(xw.1, π)] }).mapO (View.inT t)
          rw [OComp.mapO_bind, OComp.bind_mapO]
          refine congrArg _ (funext fun π => ?_)
          rw [View.inT_sessions]
          exact sigma_realLoop t Z isk (k xw.1 ⟨t, π⟩) n _

theorem sigma_realExp (Vt : (Σ t, IVK t) → AdvVerifier lam X (Σ t, Pf t))
    (Z : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)) (t : T) (i : I) (N : ℕ) :
    realExp (Arg.sigma A) Vt Z (t, i) N =
      (realExp (A t) (fun ivk => (Vt ⟨t, ivk⟩).atT t) (fun v => Z (v.inT t)) i N).mapO
        (View.inT t) := by
  show (((A t).C i).mapO fun k => ((⟨t, k.1⟩ : Σ t, IVK t), (⟨t, k.2⟩ : Σ t, ISK t))).bind
      (fun key => realLoop (Arg.sigma A) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    (((A t).C i).bind fun key =>
        realLoop (A t) (fun v => Z (v.inT t)) key.2 ((Vt ⟨t, key.1⟩).atT t)
          N ⟨key.1, [], [], []⟩).mapO (View.inT t)
  rw [OComp.mapO_bind, OComp.bind_mapO]
  exact congrArg _
    (funext fun key => sigma_realLoop t Z key.2 (Vt ⟨t, key.1⟩) N ⟨key.1, [], [], []⟩)

omit [DecidableEq T] in
theorem sigma_idealLoop (S : ∀ t, Simulator lam PP (IVK t) X (Pf t)) (t : T)
    (Z : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)) :
    ∀ (a : AdvVerifier lam X (Σ t, Pf t)) (n : ℕ) (v : View lam (IVK t) X (Pf t)) (s : (S t).St),
      idealLoop (Simulator.sigma S) Z a n (v.inT t) ⟨t, s⟩ =
        (idealLoop (S t) (fun v => Z (v.inT t)) (a.atT t) n v s).map (View.inT t)
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s => by
      simp only [idealLoop, AdvVerifier.atT, PMF.map_bind]
      show (((S t).answer s q).map fun o => (o.1, (⟨t, o.2⟩ : Σ t, (S t).St))).bind _ = _
      rw [PMF.bind_map]
      exact congrArg _
        (funext fun out =>
          sigma_idealLoop S t Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, AdvVerifier.atT, PMF.map_bind]
      exact congrArg _
        (funext fun r => sigma_idealLoop S t Z (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      simp only [idealLoop, AdvVerifier.atT]
      cases Z (v.inT t) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          simp only [PMF.map_bind]
          show (((S t).prove s xw.1).map fun o =>
              ((⟨t, o.1⟩ : Σ t, Pf t), (⟨t, o.2⟩ : Σ t, (S t).St))).bind _ = _
          rw [PMF.bind_map]
          refine congrArg _ (funext fun out => ?_)
          show idealLoop (Simulator.sigma S) Z (k xw.1 ⟨t, out.1⟩) n
              { v.inT t with sessions := (v.inT t).sessions ++ [(xw.1, ⟨t, out.1⟩)] } ⟨t, out.2⟩ = _
          rw [View.inT_sessions]
          exact sigma_idealLoop S t Z (k xw.1 ⟨t, out.1⟩) n _ out.2

omit [DecidableEq T] in
theorem sigma_idealExp (S : ∀ t, Simulator lam PP (IVK t) X (Pf t))
    (Vt : (Σ t, IVK t) → AdvVerifier lam X (Σ t, Pf t))
    (Z : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)) (t : T) (i : I) (N : ℕ) :
    idealExp (IndexedRelation.sigma R) (Simulator.sigma S) Vt Z (t, i) N =
      (idealExp (R t) (S t) (fun ivk => (Vt ⟨t, ivk⟩).atT t) (fun v => Z (v.inT t)) i N).map
        (View.inT t) := by
  show (((S t).init ((R t).pp i) N).map fun o =>
        ((⟨t, o.1⟩ : Σ t, IVK t), (⟨t, o.2⟩ : Σ t, (S t).St))).bind
      (fun out => idealLoop (Simulator.sigma S) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    (((S t).init ((R t).pp i) N).bind fun out =>
        idealLoop (S t) (fun v => Z (v.inT t)) ((Vt ⟨t, out.1⟩).atT t) N
          ⟨out.1, [], [], []⟩ out.2).map (View.inT t)
  rw [PMF.bind_map, PMF.map_bind]
  exact congrArg _
    (funext fun out => sigma_idealLoop S t Z (Vt ⟨t, out.1⟩) N ⟨out.1, [], [], []⟩ out.2)

theorem PrivacyFor.sigma {S : ∀ t, Simulator lam PP (IVK t) X (Pf t)} {ζ : ℕ → ℕ → ℝ≥0∞} {t : T}
    {i : I} {Z : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)}
    (h : PrivacyFor (R t) (A t) (S t) ζ i fun v => Z (v.inT t)) :
    PrivacyFor (IndexedRelation.sigma R) (Arg.sigma A) (Simulator.sigma S) ζ (t, i) Z := by
  intro tV Vt N hV
  have b := h tV (fun ivk => (Vt ⟨t, ivk⟩).atT t) N fun ivk =>
    AdvVerifier.QueryBound.atT t _ _ (hV ⟨t, ivk⟩)
  simp only [sigma_realExp, sigma_idealExp, Pr_mapO, prob_map]
  exact ⟨le_trans (SD_preimage_le (View.inT t) _ _) b.1, b.2⟩

theorem HasStrongIndexPrivacyWith.sigma {S : ∀ t, Simulator lam PP (IVK t) X (Pf t)}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : ∀ t, HasStrongIndexPrivacyWith (R t) (A t) (S t) ζ) :
    HasStrongIndexPrivacyWith (IndexedRelation.sigma R) (Arg.sigma A) (Simulator.sigma S) ζ :=
  fun i Z hZ => PrivacyFor.sigma (h i.1 i.2 (fun v => Z (v.inT i.1)) fun _ x w e => hZ _ x w e)

/-- the environment in the form `Env` of ZKCP/Defs.lean -/
theorem HasIndexPrivacyWith.sigma {S : ∀ t, Simulator lam PP (IVK t) X (Pf t)} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ∀ t, HasIndexPrivacyWith (R t) (A t) (S t) ζ) :
    HasIndexPrivacyWith (IndexedRelation.sigma R) (Arg.sigma A) (Simulator.sigma S) ζ := by
  rintro ⟨t, i⟩ Z hZ
  have e : (Env.onView (fun i' hist => Z (t, i') (hist.map fun s => (s.1, ⟨t, s.2⟩)))
        i : ViewEnv lam (IVK t) X W (Pf t)) =
      fun v => (Z.onView (t, i) : ViewEnv lam (Σ t, IVK t) X W (Σ t, Pf t)) (v.inT t) := rfl
  have b := h t i (fun i' hist => Z (t, i') (hist.map fun s => (s.1, ⟨t, s.2⟩))) fun hist => hZ _
  rw [e] at b
  exact PrivacyFor.sigma b

theorem HasIndexPrivacy.sigma {ζ : ℕ → ℕ → ℝ≥0∞} (h : ∀ t, HasIndexPrivacy (R t) (A t) ζ) :
    HasIndexPrivacy (IndexedRelation.sigma R) (Arg.sigma A) ζ :=
  ⟨Simulator.sigma fun t => (h t).choose, HasIndexPrivacyWith.sigma fun t => (h t).choose_spec⟩

/-! ## The primitive, index binding assumed -/

/-- Completeness and privacy come from the family; index binding is assumed. -/
theorem IsZKCPArgWith.sigma {E : ∀ t, Extractor lam I X W (IVK t) (Pf t)}
    {S : ∀ t, Simulator lam PP (IVK t) X (Pf t)} {α : ℝ≥0∞} {ε ε' ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ∀ t, IsZKCPArgWith (R t) (A t) (E t) (S t) α ε' ζ)
    (Es : Extractor lam (T × I) X W (Σ t, IVK t) (Σ t, Pf t))
    (hb : HasIndexBindingWith (IndexedRelation.sigma R) (Arg.sigma A) Es ε) :
    IsZKCPArgWith (IndexedRelation.sigma R) (Arg.sigma A) Es (Simulator.sigma S) α ε ζ :=
  ⟨HasCompletenessError.sigma fun t => (h t).completeness,
    hb,
    HasStrongIndexPrivacyWith.sigma fun t => (h t).indexPrivacy⟩

/-- IsZKCPArg (ZKCP/Defs.lean), index binding being asked -/
theorem IsZKCPArg.sigma {α : ℝ≥0∞} {ε ε' ζ : ℕ → ℕ → ℝ≥0∞} (h : ∀ t, IsZKCPArg (R t) (A t) α ε' ζ)
    (hb : HasIndexBinding (IndexedRelation.sigma R) (Arg.sigma A) ε) :
    IsZKCPArg (IndexedRelation.sigma R) (Arg.sigma A) α ε ζ :=
  ⟨HasCompletenessError.sigma fun t => (h t).completeness,
    hb,
    HasIndexPrivacy.sigma fun t => (h t).indexPrivacy⟩

/-! ## Index binding at a t₀ that is fixed before the oracle -/

/-- In a computation in two steps the probability of an event is at most that of another event with
another second step, if it is so for every outcome of the first. -/
theorem prob_run_bind_le2 {α β β' : Type} (f : Oracle lam) (c : OComp lam α) {g : α → OComp lam β}
    {g' : α → OComp lam β'} (E : Set β) (E' : Set β')
    (h : ∀ a, prob ((g a).run f) E ≤ prob ((g' a).run f) E') :
    prob ((c.bind g).run f) E ≤ prob ((c.bind g').run f) E' := by
  rw [run_bind, run_bind, prob_bind, prob_bind]
  exact expect_mono _ h

/-- the second component of a pair that names t₀, or d if it names another t -/
def sigmaAtD {β : T → Type} (t₀ : T) (d : β t₀) (v : Σ t, β t) : β t₀ :=
  if h : v.1 = t₀ then h ▸ v.2 else d

theorem sigmaAtD_self {β : T → Type} (t₀ : T) (d b : β t₀) : sigmaAtD t₀ d ⟨t₀, b⟩ = b :=
  dif_pos rfl

omit [DecidableEq T] in
/-- the bad event at (t, i*) is R t's at i* -/
theorem bindingBad_sigma (t : T) (b : Bool) (o : Option I) (x : X) (w : W) :
    (⟨b, o.map fun i => (t, i), x, w⟩ : BindingOutcome (T × I) X W) ∈
      bindingBad (IndexedRelation.sigma R) ↔
    (⟨b, o, x, w⟩ : BindingOutcome I X W) ∈ bindingBad (R t) := by
  cases o <;> rfl

/-- after a rejection the bad event has probability 0, if the outcome records V's bit (hF) -/
theorem prob_reject {I' : Type} (R' : IndexedRelation I' X W PP) (f : Oracle lam)
    (F : Bool → BindingOutcome I' X W) (hF : ∀ b, (F b).accept = b) :
    prob (((OComp.pure false : OComp lam Bool).bind fun b => .pure (F b)).run f) (bindingBad R') =
      0 := by
  show prob (PMF.pure (F false)) (bindingBad R') = 0
  rw [prob_pure, if_neg]
  exact fun hb => Bool.noConfusion ((hF false).symm.trans hb.1)

/-- Under h, binding of A t₀: binding of `Arg.sigmaAt A t₀`, with `Extractor.sigma E` and the same
bound. (W has a default element.) -/
theorem HasIndexBindingWith.sigmaAt [Inhabited W] {E : ∀ t, Extractor lam I X W (IVK t) (Pf t)}
    {ε : ℕ → ℕ → ℝ≥0∞} (t₀ : T) (h : HasIndexBindingWith (R t₀) (A t₀) (E t₀) ε) :
    HasIndexBindingWith (IndexedRelation.sigma R) (Arg.sigmaAt A t₀) (Extractor.sigma E) ε := by
  intro tC tP St Ct Pt hC hP
  by_cases hk : Nonempty (IVK t₀) ∧ Nonempty (Pf t₀)
  · obtain ⟨⟨k₀⟩, ⟨π₀⟩⟩ := hk
    refine le_trans ?_
      (h tC tP St (Ct.mapO fun o => (sigmaAtD t₀ k₀ o.1, o.2))
        (fun s => (Pt s).mapO fun o => (o.1, sigmaAtD t₀ π₀ o.2)) (OComp.QueryBound.mapO _ Ct tC hC)
        fun s => OComp.QueryBound.mapO _ (Pt s) tP (hP s))
    refine MeasureTheory.lintegral_mono fun f => ?_
    show prob ((Ct.withTrace.bind fun o =>
          (Pt o.1.2).withTrace.bind fun o' =>
            ((Arg.sigmaAt A t₀).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
              .pure (⟨b, (Extractor.sigma E).Ei o.1.1 o.2,
                  o'.1.1,
                  (Extractor.sigma E).Ew o.1.1 o.2 o'.1.1 o'.1.2
                    o'.2⟩ : BindingOutcome (T × I) X W)).run f)
        (bindingBad (IndexedRelation.sigma R)) ≤
      prob (((Ct.mapO fun o => (sigmaAtD t₀ k₀ o.1, o.2)).withTrace.bind fun o =>
          ((Pt o.1.2).mapO fun o => (o.1, sigmaAtD t₀ π₀ o.2)).withTrace.bind fun o' =>
            ((A t₀).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
              .pure (⟨b, (E t₀).Ei o.1.1 o.2, o'.1.1,
                  (E t₀).Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f)
        (bindingBad (R t₀))
    rw [OComp.withTrace_mapO, OComp.mapO_bind]
    refine prob_run_bind_le2 f _ _ _ fun o => ?_
    simp only [OComp.withTrace_mapO, OComp.mapO_bind]
    refine prob_run_bind_le2 f _ _ _ fun o' => ?_
    obtain ⟨⟨⟨t, k⟩, st⟩, trC⟩ := o
    obtain ⟨⟨x, ⟨t', π⟩⟩, trP⟩ := o'
    by_cases e : t = t₀
    · subst e
      by_cases e' : t' = t
      · subst e'
        simp only [sigmaAt_V_self, sigmaAtD_self]
        refine prob_run_bind_le2 f _ _ _ fun b => ?_
        show prob (PMF.pure _) _ ≤ prob (PMF.pure _) _
        rw [prob_pure, prob_pure]
        have hw : (Extractor.sigma E).Ew ⟨t', k⟩ trC x ⟨t', π⟩ trP = (E t').Ew k trC x π trP :=
          dif_pos rfl
        have hi : (Extractor.sigma E).Ei ⟨t', k⟩ trC = ((E t').Ei k trC).map fun i => (t', i) := rfl
        rw [hw, hi]
        by_cases hb : (⟨b, (E t').Ei k trC, x, (E t').Ew k trC x π trP⟩ : BindingOutcome I X W) ∈
          bindingBad (R t')
        · rw [if_pos hb]
          split <;> simp
        · rw [if_neg fun hs => hb ((bindingBad_sigma t' b _ x _).1 hs)]
          exact zero_le _
      · rw [sigmaAt_V_of_ne' A (vk := ⟨t, k⟩) (π := ⟨t', π⟩) e' x, prob_reject _ f _ fun _ => rfl]
        exact zero_le _
    · rw [sigmaAt_V_of_ne A (vk := ⟨t, k⟩) e x ⟨t', π⟩, prob_reject _ f _ fun _ => rfl]
      exact zero_le _
  · have hV : ∀ (vk : Σ t, IVK t) (x : X) (π : Σ t, Pf t),
        (Arg.sigmaAt A t₀).V vk x π = .pure false := by
      rintro ⟨t, k⟩ x ⟨t', π⟩
      by_cases e : t = t₀
      · subst e
        by_cases e' : t' = t
        · subst e'
          exact absurd ⟨⟨k⟩, ⟨π⟩⟩ hk
        · exact sigmaAt_V_of_ne' A (vk := ⟨t, k⟩) (π := ⟨t', π⟩) e' x
      · exact sigmaAt_V_of_ne A (vk := ⟨t, k⟩) e x ⟨t', π⟩
    refine le_trans (le_of_eq ?_) (zero_le _)
    refine (MeasureTheory.lintegral_congr fun f => ?_).trans MeasureTheory.lintegral_zero
    refine le_antisymm
      (le_trans ?_
        (le_of_eq (show prob
              ((Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun _ => OComp.pure ()).run f)
              (∅ : Set Unit) = 0 from by simp [prob]))) (zero_le _)
    show prob ((Ct.withTrace.bind fun o =>
          (Pt o.1.2).withTrace.bind fun o' =>
            ((Arg.sigmaAt A t₀).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
              .pure (⟨b, (Extractor.sigma E).Ei o.1.1 o.2,
                  o'.1.1,
                  (Extractor.sigma E).Ew o.1.1 o.2 o'.1.1 o'.1.2
                    o'.2⟩ : BindingOutcome (T × I) X W)).run f)
        (bindingBad (IndexedRelation.sigma R)) ≤ _
    refine prob_run_bind_le2 f _ _ _ fun o => prob_run_bind_le2 f _ _ _ fun o' => ?_
    rw [hV, prob_reject _ f _ fun _ => rfl]
    exact zero_le _

/-! ## Where the members' public parameters are the one element of Unit: pp(t, i) = t -/

section U
variable {R : T → IndexedRelation I X W Unit}

omit [DecidableEq T] in
/-- the index is (t, i); its public parameters are t -/
def IndexedRelation.sigmaU (R : T → IndexedRelation I X W Unit) : IndexedRelation (T × I) X W T :=
  (IndexedRelation.sigma R).mapPP Prod.fst

omit [DecidableEq T] in
/-- the public parameters of (t, i) are t -/
theorem IndexedRelation.sigmaU_pp (R : T → IndexedRelation I X W Unit) :
    (IndexedRelation.sigmaU R).pp = Prod.fst := rfl

omit [DecidableEq T] in
/-- the simulator is initialised with t -/
def Simulator.sigmaU (S : ∀ t, Simulator lam Unit (IVK t) X (Pf t)) :
    Simulator lam T (Σ t, IVK t) X (Σ t, Pf t) :=
  (Simulator.sigma S).comapPP fun t => (t, ())

theorem HasCompletenessError.sigmaU {α : ℝ≥0∞} (h : ∀ t, HasCompletenessError (R t) (A t) α) :
    HasCompletenessError (IndexedRelation.sigmaU R) (Arg.sigma A) α :=
  (HasCompletenessError.sigma h).mapPP _

theorem HasStrongIndexPrivacyWith.sigmaU {S : ∀ t, Simulator lam Unit (IVK t) X (Pf t)}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : ∀ t, HasStrongIndexPrivacyWith (R t) (A t) (S t) ζ) :
    HasStrongIndexPrivacyWith (IndexedRelation.sigmaU R) (Arg.sigma A) (Simulator.sigmaU S) ζ :=
  (HasStrongIndexPrivacyWith.sigma h).mapPP fun _ => rfl

theorem HasIndexPrivacyWith.sigmaU {S : ∀ t, Simulator lam Unit (IVK t) X (Pf t)} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ∀ t, HasIndexPrivacyWith (R t) (A t) (S t) ζ) :
    HasIndexPrivacyWith (IndexedRelation.sigmaU R) (Arg.sigma A) (Simulator.sigmaU S) ζ :=
  (HasIndexPrivacyWith.sigma h).mapPP fun _ => rfl

theorem HasIndexBindingWith.sigmaAtU [Inhabited W] {E : ∀ t, Extractor lam I X W (IVK t) (Pf t)}
    {ε : ℕ → ℕ → ℝ≥0∞} (t₀ : T) (h : HasIndexBindingWith (R t₀) (A t₀) (E t₀) ε) :
    HasIndexBindingWith (IndexedRelation.sigmaU R) (Arg.sigmaAt A t₀) (Extractor.sigma E) ε :=
  (HasIndexBindingWith.sigmaAt t₀ h).mapPP _

/-- Completeness and privacy come from the family; index binding is assumed. -/
theorem IsZKCPArgWith.sigmaU {E : ∀ t, Extractor lam I X W (IVK t) (Pf t)}
    {S : ∀ t, Simulator lam Unit (IVK t) X (Pf t)} {α : ℝ≥0∞} {ε ε' ζ : ℕ → ℕ → ℝ≥0∞}
    (h : ∀ t, IsZKCPArgWith (R t) (A t) (E t) (S t) α ε' ζ)
    (Es : Extractor lam (T × I) X W (Σ t, IVK t) (Σ t, Pf t))
    (hb : HasIndexBindingWith (IndexedRelation.sigmaU R) (Arg.sigma A) Es ε) :
    IsZKCPArgWith (IndexedRelation.sigmaU R) (Arg.sigma A) Es (Simulator.sigmaU S) α ε ζ :=
  ⟨HasCompletenessError.sigmaU fun t => (h t).completeness,
    hb,
    HasStrongIndexPrivacyWith.sigmaU fun t => (h t).indexPrivacy⟩

end U

end ZKCP
