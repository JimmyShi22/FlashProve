-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/KeyTag.lean: a tag, a constant of the scheme, as a field of the verification key.

V compares the key's tag with its own. For every scheme (C, P, V) of ZKCP/Defs.lean, every type T
with decidable equality and every t : T:
  `Arg.tagKey A t`      C outputs ((t, ivk), isk); P is A's; V, given (t', ivk), runs A's V on ivk
                        if t' = t and rejects otherwise, without a query
  `Extractor.tagKey E`  reads the key without its tag
  `Simulator.tagKey S t` puts t before the key that S makes
  `IsZKCPArgWith.tagKey` the three properties are carried over, for the same relation, with the same
                        bounds and these two terms; `IsZKCPArg.tagKey`: likewise, no terms named
  `tagKey_V_of_ne`      V rejects every key that names another tag: for t' ≠ t the computation V
                        (t', ivk) x π is "false", whatever ivk, x, π are, for every oracle, with no
                        query and no coin
  `tagKey_one_tag`      two schemes of any types with tags of one type, two keys with the same first
                        field: if neither V's computation is "false", the two tags are equal
Why. A family of schemes A_t over public parameters t (a table of constants) has, scheme by scheme,
the three properties for a t that is fixed before the oracle (here a hypothesis: h of
`IsZKCPArgWith.tagKey`, `IsZKCPArg.tagKey`). Nothing then says that a key made under t is rejected
under t'. With the tag it is: a key names one t, and V under any other parameter rejects it
(`tagKey_V_of_ne`).

Limits:
- V's own tag comes from elsewhere than the key. A client that copies its tag from the key runs
  another verifier, V*(t', ivk) = A_t'.V ivk, for which the comparison is always true and this file
  gives nothing: there are families with index binding at every fixed tag whose V* is broken with
  one query (an example that is not in this library; a comment sketches one: ZKCP/Sigma.lean,
  Limits).
- The tag is a label beside ivk and is not hashed here: whoever has (t, ivk) can write (t', ivk),
  which is another key; for it the properties of the scheme at t' apply as for every key; nothing
  says that it is rejected, or that the index behind it is the same; the extractor drops the tag.
- The tag is public as a constant of the scheme, the same for all indices (V has it, so the
  simulator may): it does not pass through the definition's pp(i).
- Nothing is said about a parameter that is chosen after queries: t is bound outside the
  experiments.
- The keys of A_t and A_t' may have different types; `tagKey_V_of_ne` is about the keys of one
  scheme's own type.
- Of the other properties of this library refined and adaptive completeness and many sessions are
  not carried over here; that flight privacy (with batches: ZKCP/GenKeyTag.lean) follows from
  `IsZKCPArgWith` is neither stated nor proved in this library.

After `IsZKCPArg` and its three properties in ZKCP/Defs.lean; the step itself is not in
ZKCP/Defs.lean.
-/
import ZKCP.Lemmas
import ZKCP.Basic
import ZKCP.SameRun
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf T : Type}

/-! ## A function applied to the output of a computation -/

namespace OComp
variable {α β γ : Type}

theorem bind_bind (c : OComp lam α) (g : α → OComp lam β) (h : β → OComp lam γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | query q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

/-- a function applied to the output -/
def mapO (h : α → β) (c : OComp lam α) : OComp lam β := c.bind fun a => .pure (h a)

theorem mapO_bind (h : α → β) (c : OComp lam α) (g : β → OComp lam γ) :
    (c.mapO h).bind g = c.bind fun a => g (h a) := bind_bind c _ g

theorem bind_mapO (c : OComp lam α) (g : α → OComp lam β) (h : β → γ) :
    (c.bind g).mapO h = c.bind fun a => (g a).mapO h := bind_bind c g _

theorem run_mapO (f : Oracle lam) (h : α → β) (c : OComp lam α) :
    (c.mapO h).run f = (c.run f).map h := by
  unfold mapO
  rw [run_bind]
  rfl

theorem withTrace_mapO (h : α → β) (c : OComp lam α) :
    (c.mapO h).withTrace = c.withTrace.mapO fun o => (h o.1, o.2) := by
  induction c with
  | pure a => rfl
  | query q k ih =>
      show OComp.query q
          (fun r => ((k r).mapO h).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)) =
        OComp.query q fun r =>
          ((k r).withTrace.bind fun out => .pure (out.1, (q, r) :: out.2)).mapO fun o =>
            (h o.1, o.2)
      refine congrArg _ (funext fun r => ?_)
      rw [ih r, mapO_bind, bind_mapO]
      rfl
  | sample n k ih =>
      show OComp.sample n (fun r => ((k r).mapO h).withTrace) =
        OComp.sample n fun r => (k r).withTrace.mapO fun o => (h o.1, o.2)
      exact congrArg _ (funext ih)

theorem QueryBound.mapO (h : α → β) :
    ∀ (c : OComp lam α) (t : ℕ), c.QueryBound t → (c.mapO h).QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _, 0, hc => hc.elim
  | .query _ k, t + 1, hc => fun r => QueryBound.mapO h (k r) t (hc r)
  | .sample _ k, t, hc => fun r => QueryBound.mapO h (k r) t (hc r)

end OComp

theorem prob_map {α β : Type} (p : PMF α) (h : α → β) (E : Set β) :
    prob (p.map h) E = prob p (h ⁻¹' E) :=
  PMF.toOuterMeasure_map_apply h p E

theorem Pr_mapO {α β : Type} (h : α → β) (c : OComp lam α) (E : Set β) :
    Pr (c.mapO h) (fun _ => E) = Pr c fun _ => h ⁻¹' E := by
  unfold Pr PrCoins
  simp only [OComp.run_mapO, prob_map]

/-- in a computation in two steps the probability of an event grows with its probability in the
second step -/
theorem prob_run_bind_le {α β : Type} (f : Oracle lam) (c : OComp lam α) {g g' : α → OComp lam β}
    (E : Set β) (h : ∀ a, prob ((g a).run f) E ≤ prob ((g' a).run f) E) :
    prob ((c.bind g).run f) E ≤ prob ((c.bind g').run f) E := by
  rw [run_bind, run_bind, prob_bind, prob_bind]
  exact expect_mono _ h

/-- a function applied to both sides does not raise the distance -/
theorem SD_preimage_le {α β : Type} (h : α → β) (P Q : Set α → ℝ≥0∞) :
    SD (fun E : Set β => P (h ⁻¹' E)) (fun E => Q (h ⁻¹' E)) ≤ SD P Q :=
  iSup_le fun E => le_iSup (fun E : Set α => max (P E - Q E) (Q E - P E)) (h ⁻¹' E)

/-! ## The scheme with a tag in the key -/

/-- The extractor: it reads the key without its tag. -/
def Extractor.tagKey (E : Extractor lam I X W IVK Pf) : Extractor lam I X W (T × IVK) Pf :=
  ⟨fun v => E.Ei v.2, fun v => E.Ew v.2⟩

/-- The simulator: the tag before the key that S makes. -/
def Simulator.tagKey (S : Simulator lam PP IVK X Pf) (t : T) :
    Simulator lam PP (T × IVK) X Pf where
  St := S.St
  init p n := (S.init p n).map fun o => ((t, o.1), o.2)
  answer := S.answer
  prove := S.prove

/-- the tag before the key of a view -/
def View.tagKey (t : T) (v : View lam IVK X Pf) : View lam (T × IVK) X Pf :=
  ⟨(t, v.ivk), v.sessions, v.trace, v.coins⟩

variable [DecidableEq T]

/-- The scheme with the tag t: C puts t before ivk, and V rejects a key with another tag. -/
def Arg.tagKey (A : Arg lam I X W IVK ISK Pf) (t : T) : Arg lam I X W (T × IVK) ISK Pf where
  C i := (A.C i).mapO fun k => ((t, k.1), k.2)
  P := A.P
  V v x π := if v.1 = t then A.V v.2 x π else .pure false

variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf) (t : T)

/-- V rejects every key that names another tag: the computation is "false". -/
theorem tagKey_V_of_ne {t' : T} (h : t' ≠ t) (ivk : IVK) (x : X) (π : Pf) :
    (A.tagKey t).V (t', ivk) x π = .pure false := if_neg h

theorem tagKey_V_self (ivk : IVK) (x : X) (π : Pf) : (A.tagKey t).V (t, ivk) x π = A.V ivk x π :=
  if_pos rfl

/-- Two keys with the same first field are not both accepted unless the two tags agree; the two
schemes may have any types. -/
theorem tagKey_one_tag {I' X' W' IVK' ISK' Pf' : Type} (A' : Arg lam I' X' W' IVK' ISK' Pf')
    {t t' : T} (k : T × IVK) (k' : T × IVK') (e : k.1 = k'.1) {x : X} {x' : X'} {π : Pf} {π' : Pf'}
    (h : (A.tagKey t).V k x π ≠ .pure false) (h' : (A'.tagKey t').V k' x' π' ≠ .pure false) :
    t = t' := by
  by_contra hne
  by_cases h1 : k.1 = t
  · exact h' (if_neg fun h2 => hne (h1.symm.trans (e.trans h2)))
  · exact h (if_neg h1)

theorem QueryBound.tagKey_V {N : ℕ} (h : ∀ ivk x π, (A.V ivk x π).QueryBound N)
    (v : T × IVK) (x : X) (π : Pf) :
    ((A.tagKey t).V v x π).QueryBound N := by
  show (if v.1 = t then A.V v.2 x π else .pure false : OComp lam Bool).QueryBound N
  split
  · exact h _ _ _
  · trivial

/-! ## Completeness -/

theorem tagKey_sessionExp (ivk : IVK) (isk : ISK) (x : X) (w : W) :
    sessionExp (A.tagKey t) (t, ivk) isk x w = sessionExp A ivk isk x w := by
  show (A.P isk x w).bind (fun π => (A.tagKey t).V (t, ivk) x π) =
    (A.P isk x w).bind fun π => A.V ivk x π
  simp only [tagKey_V_self]

theorem tagKey_completenessExp (i : I) (x : X) (w : W) :
    completenessExp (A.tagKey t) i x w = completenessExp A i x w := by
  show ((A.C i).mapO fun k => ((t, k.1), k.2)).bind
      (fun key => sessionExp (A.tagKey t) key.1 key.2 x w) =
    (A.C i).bind fun key => sessionExp A key.1 key.2 x w
  rw [OComp.mapO_bind]
  simp only [tagKey_sessionExp]

variable {R A}

theorem HasCompletenessError.tagKey {α : ℝ≥0∞} (h : HasCompletenessError R A α) :
    HasCompletenessError R (A.tagKey t) α := fun i x w hr => by
  rw [tagKey_completenessExp]
  exact h i x w hr

/-! ## Index binding -/

theorem HasIndexBindingWith.tagKey
    {E : Extractor lam I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R (A.tagKey t) (E.tagKey (T := T)) ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_
    (h tC tP (T × St) (Ct.mapO fun o => (o.1.2, (o.1.1, o.2))) (fun s => Pt s.2)
      (OComp.QueryBound.mapO _ Ct tC hC) fun s => hP s.2)
  refine MeasureTheory.lintegral_mono fun f => ?_
  show prob ((Ct.withTrace.bind fun o =>
        (Pt o.1.2).withTrace.bind fun o' =>
          ((A.tagKey t).V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1.2 o.2, o'.1.1,
                E.Ew o.1.1.2 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f)
      (bindingBad R) ≤
    prob (((Ct.mapO fun o => (o.1.2, (o.1.1, o.2))).withTrace.bind fun o =>
        (Pt o.1.2.2).withTrace.bind fun o' =>
          (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
            .pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
                E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)).run f) (bindingBad R)
  rw [OComp.withTrace_mapO, OComp.mapO_bind]
  refine prob_run_bind_le f _ _ fun o => prob_run_bind_le f _ _ fun o' => ?_
  by_cases e : o.1.1.1 = t
  · have e2 : (A.tagKey t).V o.1.1 o'.1.1 o'.1.2 = A.V o.1.1.2 o'.1.1 o'.1.2 := if_pos e
    rw [e2]
  · have e2 : (A.tagKey t).V o.1.1 o'.1.1 o'.1.2 = .pure false := if_neg e
    rw [e2]
    refine le_trans (le_of_eq ?_) (zero_le _)
    show prob (PMF.pure _) (bindingBad R) = 0
    rw [prob_pure, if_neg]
    exact fun hb => Bool.noConfusion hb.1

theorem HasIndexBinding.tagKey {ε : ℕ → ℕ → ℝ≥0∞} (h : HasIndexBinding R A ε) :
    HasIndexBinding R (A.tagKey t) ε :=
  h.elim fun E hE => ⟨E.tagKey, hE.tagKey t⟩

/-! ## Index privacy -/

theorem tagKey_realLoop (Z : ViewEnv lam (T × IVK) X W Pf) (isk : ISK) :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf),
      realLoop (A.tagKey t) Z isk a n (v.tagKey t) =
        (realLoop A (fun v => Z (v.tagKey t)) isk a n v).mapO (View.tagKey t)
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      show OComp.query q (fun r =>
          realLoop (A.tagKey t) Z isk (k r) n
            (View.tagKey t { v with trace := v.trace ++ [(q, r)] })) =
        OComp.query q fun r =>
          (realLoop A (fun v => Z (v.tagKey t)) isk (k r) n
              { v with trace := v.trace ++ [(q, r)] }).mapO (View.tagKey t)
      exact congrArg _ (funext fun r => tagKey_realLoop Z isk (k r) n _)
  | .sample m k, n, v => by
      show OComp.sample m (fun r =>
          realLoop (A.tagKey t) Z isk (k r) n
            (View.tagKey t { v with coins := v.coins ++ [r.val] })) =
        OComp.sample m fun r =>
          (realLoop A (fun v => Z (v.tagKey t)) isk (k r) n
              { v with coins := v.coins ++ [r.val] }).mapO (View.tagKey t)
      exact congrArg _ (funext fun r => tagKey_realLoop Z isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop]
      cases Z (v.tagKey t) with
      | none => rfl
      | some xw =>
          show (A.P isk xw.1 xw.2).bind (fun π =>
              realLoop (A.tagKey t) Z isk (k xw.1 π) n
                (View.tagKey t { v with sessions := v.sessions ++ [(xw.1, π)] })) =
            ((A.P isk xw.1 xw.2).bind fun π =>
                realLoop A (fun v => Z (v.tagKey t)) isk (k xw.1 π) n
                  { v with sessions := v.sessions ++ [(xw.1, π)] }).mapO (View.tagKey t)
          rw [OComp.bind_mapO]
          exact congrArg _ (funext fun π => tagKey_realLoop Z isk (k xw.1 π) n _)

theorem tagKey_realExp (Vt : T × IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam (T × IVK) X W Pf) (i : I) (N : ℕ) :
    realExp (A.tagKey t) Vt Z i N =
      (realExp A (fun ivk => Vt (t, ivk)) (fun v => Z (v.tagKey t)) i N).mapO (View.tagKey t) := by
  show ((A.C i).mapO fun k => ((t, k.1), k.2)).bind
      (fun key => realLoop (A.tagKey t) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    ((A.C i).bind fun key =>
        realLoop A (fun v => Z (v.tagKey t)) key.2 (Vt (t, key.1)) N ⟨key.1, [], [], []⟩).mapO
      (View.tagKey t)
  rw [OComp.mapO_bind, OComp.bind_mapO]
  exact congrArg _
    (funext fun key => tagKey_realLoop t Z key.2 (Vt (t, key.1)) N ⟨key.1, [], [], []⟩)

omit [DecidableEq T] in
theorem tagKey_idealLoop (S : Simulator lam PP IVK X Pf) (Z : ViewEnv lam (T × IVK) X W Pf) :
    ∀ (a : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf) (s : S.St),
      idealLoop (S.tagKey t) Z a n (v.tagKey t) s =
        (idealLoop S (fun v => Z (v.tagKey t)) a n v s).map (View.tagKey t)
  | .halt, _, _, _ => (PMF.pure_map _ _).symm
  | .query q k, n, v, s => by
      simp only [idealLoop, PMF.map_bind]
      exact congrArg _
        (funext fun out =>
          tagKey_idealLoop S Z (k out.1) n { v with trace := v.trace ++ [(q, out.1)] } out.2)
  | .sample m k, n, v, s => by
      simp only [idealLoop, PMF.map_bind]
      exact congrArg _
        (funext fun r => tagKey_idealLoop S Z (k r) n { v with coins := v.coins ++ [r.val] } s)
  | .request _, 0, _, _ => (PMF.pure_map _ _).symm
  | .request k, n + 1, v, s => by
      simp only [idealLoop]
      cases Z (v.tagKey t) with
      | none => exact (PMF.pure_map _ _).symm
      | some xw =>
          simp only [PMF.map_bind]
          exact congrArg _
            (funext fun out =>
              tagKey_idealLoop S Z (k xw.1 out.1) n
                { v with sessions := v.sessions ++ [(xw.1, out.1)] } out.2)

omit [DecidableEq T] in
theorem tagKey_idealExp (S : Simulator lam PP IVK X Pf) (Vt : T × IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam (T × IVK) X W Pf) (i : I) (N : ℕ) :
    idealExp R (S.tagKey t) Vt Z i N =
      (idealExp R S (fun ivk => Vt (t, ivk)) (fun v => Z (v.tagKey t)) i N).map
        (View.tagKey t) := by
  show ((S.init (R.pp i) N).map fun o => ((t, o.1), o.2)).bind
      (fun out => idealLoop (S.tagKey t) Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2) =
    ((S.init (R.pp i) N).bind fun out =>
        idealLoop S (fun v => Z (v.tagKey t)) (Vt (t, out.1)) N ⟨out.1, [], [], []⟩ out.2).map
      (View.tagKey t)
  rw [PMF.bind_map, PMF.map_bind]
  exact congrArg _
    (funext fun out => tagKey_idealLoop t S Z (Vt (t, out.1)) N ⟨out.1, [], [], []⟩ out.2)

theorem PrivacyFor.tagKey {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} {i : I}
    {Z : ViewEnv lam (T × IVK) X W Pf} (h : PrivacyFor R A S ζ i fun v => Z (v.tagKey t)) :
    PrivacyFor R (A.tagKey t) (S.tagKey t) ζ i Z := by
  intro tV Vt N hV
  have b := h tV (fun ivk => Vt (t, ivk)) N fun ivk => hV (t, ivk)
  simp only [tagKey_realExp, tagKey_idealExp, Pr_mapO, prob_map]
  exact ⟨le_trans (SD_preimage_le (View.tagKey t) _ _) b.1, b.2⟩

theorem HasStrongIndexPrivacyWith.tagKey
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasStrongIndexPrivacyWith R A S ζ) :
    HasStrongIndexPrivacyWith R (A.tagKey t) (S.tagKey t) ζ :=
  fun i Z hZ => (h i (fun v => Z (v.tagKey t)) fun _ x w e => hZ _ x w e).tagKey t

theorem HasIndexPrivacyWith.tagKey
    {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacyWith R A S ζ) :
    HasIndexPrivacyWith R (A.tagKey t) (S.tagKey t) ζ :=
  fun i Z hZ => PrivacyFor.tagKey t (h i Z hZ)

theorem HasIndexPrivacy.tagKey {ζ : ℕ → ℕ → ℝ≥0∞} (h : HasIndexPrivacy R A ζ) :
    HasIndexPrivacy R (A.tagKey t) ζ :=
  h.elim fun S hS => ⟨S.tagKey t, hS.tagKey t⟩

/-! ## The primitive -/

/-- `IsZKCPArgWith` is carried over, with the same bounds. -/
theorem IsZKCPArgWith.tagKey {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf}
    {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArgWith R A E S α ε ζ) :
    IsZKCPArgWith R (A.tagKey t) (E.tagKey (T := T)) (S.tagKey t) α ε ζ :=
  ⟨h.completeness.tagKey t, h.indexBinding.tagKey t, h.indexPrivacy.tagKey t⟩

/-- IsZKCPArg (ZKCP/Defs.lean) is carried over, with the same bounds. -/
theorem IsZKCPArg.tagKey {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (h : IsZKCPArg R A α ε ζ) :
    IsZKCPArg R (A.tagKey t) α ε ζ :=
  ⟨h.completeness.tagKey t, h.indexBinding.tagKey t, h.indexPrivacy.tagKey t⟩

end ZKCP
